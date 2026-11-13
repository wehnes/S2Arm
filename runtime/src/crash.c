// 崩溃现场（旧库 crash.c 改后搬，只留信号处理本身）：出错地址、pc / lr 换成模块内偏移、寄存器、帧指针回溯、线程表。
#include "native.h"
#include "../../platform/plat.h"
#include "guest_failure_diag.h"
#include <signal.h>
#include <dlfcn.h>
#include <sys/ucontext.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <mach/mach.h>
#else
#include <sys/uio.h>
#endif
#if defined(__ANDROID__)
#include "../../android/native/runtime/fault/fault.h"
#include <fcntl.h>
#include <stdatomic.h>
#endif

__attribute__((weak)) int s2a_trap_brk(void *ctx);   // traps.c；只编 crash.c 的单测 / 安卓测试壳里没有它
static void where(uint64_t a, char *b, size_t n) {   // 地址 → 「模块+偏移」或宿主符号
    module_t *m = module_of((void *)a);
    if (m) {   // 补丁区：近端在映像尾（偏移 ≥ patch_off），FAR 在基址前（偏移为负，按有符号打，原先无符号相减打成 0xffff… 回绕值）
        int64_t off = (int64_t)(a - (uint64_t)m->base);
        int patch = s2a_in_patch(m, a);   // 任一补丁岛（双岛时另一个岛在基址前 / 键页后）
        snprintf(b, n, "%s%s%#llx%s", m->name, off < 0 ? "-" : "+", (unsigned long long)(off < 0 ? -off : off), patch ? "（补丁区）" : "");
        return;
    }
    Dl_info di; if (dladdr((void *)a, &di) && di.dli_sname) { snprintf(b, n, "%s+%#llx（宿主）", di.dli_sname, (unsigned long long)(a - (uint64_t)di.dli_saddr)); return; }
    snprintf(b, n, "%#llx", (unsigned long long)a);
}
void s2a_where(uint64_t a, char *b, size_t n) { where(a, b, n); }
// 读一帧 {上一帧 fp, 返回地址}：经内核读，帧指针坏了（未映射 / 不可读）回 0，不在崩溃处理里二次缺页（二次缺页 = 处理函数自己 _exit，后面现场全丢）。信号里可调
static int frame_read(uint64_t fp, uint64_t rec[2]) {
#if defined(__APPLE__)
    vm_size_t got = 0;
    return vm_read_overwrite(mach_task_self(), (vm_address_t)fp, 16, (vm_address_t)rec, &got) == KERN_SUCCESS && got == 16;
#else
    struct iovec l = {rec, 16}, r = {(void *)(uintptr_t)fp, 16};
    return process_vm_readv(getpid(), &l, 1, &r, 1, 0) == 16;
#endif
}
// 帧指针链 → 返回地址（至多 max 个）：8 对齐、逐帧往高处走、每帧经 frame_read 读、返回地址非 0
static int s2a_frames(uint64_t fp, uint64_t *lr, int max) {
    int k = 0; uint64_t rec[2];
    while (k < max && fp && !(fp & 7) && frame_read(fp, rec) && rec[1]) { lr[k++] = rec[1]; if (rec[0] <= fp) break; fp = rec[0]; }   // 返回地址 0 = 链尾（不可读页经内核读出全 0 也落在这里）
    return k;
}
void s2a_backtrace(uint64_t fp) {
    uint64_t lr[32]; int k = s2a_frames(fp, lr, 32);
    for (int i = 0; i < k; i++) { char b[160]; where(lr[i], b, sizeof b); LOG("  #%d %s", i, b); }
}
unsigned s2a_guest_failure_frames(uint64_t fp, uint64_t *out, unsigned max) {
    return (unsigned)s2a_frames(fp, out, (int)(max > 6 ? 6 : max));
}
static int break_diag_read(void *ctx, uint64_t address, uint64_t *words, unsigned count) {
    (void)ctx;
    if (count > 24 || (count & 1)) return 0;
    for (unsigned index = 0; index < count; index += 2)
        if (!frame_read(address + index * 8, words + index)) return 0;
    return 1;
}
static void break_diag_emit(void *ctx, unsigned depth, uint64_t address, const uint64_t *words, unsigned count) {
    (void)ctx;
    for (unsigned index = 0; index + 3 < count; index += 4)
        LOG("[break_mem] depth=%u address=%#llx words=%016llx %016llx %016llx %016llx", depth,
            (unsigned long long)(address + index * 8), (unsigned long long)words[index], (unsigned long long)words[index + 1],
            (unsigned long long)words[index + 2], (unsigned long long)words[index + 3]);
}
void s2a_guest_break_trace(uint64_t fp) {
    s2a_backtrace(fp);
    const char *enabled = getenv("S2A_GUEST_FAILURE_DIAG");
    if (!enabled || !*enabled || !strcmp(enabled, "0")) return;
    LOG("[break_mem] begin fp=%#llx bounded pointer-shaped previews", (unsigned long long)fp);
    s2a_diag_stats stats = s2a_diag_frames(fp, break_diag_read, break_diag_emit, NULL);
    LOG("[break_mem] end frames=%u nodes=%u read_failures=%u limited=%u bytes=%llu", stats.frames, stats.nodes,
        stats.failures, stats.limited, (unsigned long long)stats.bytes);
}
void s2a_thread_dump(void);
#include "../../graphics/track/s2a_track.h"
#if defined(__ANDROID__)
// The existing dispatcher remains the only owner. Managed/ART handlers may
// subsequently chain to it, so readiness is proved by fault_probe after managed
// attachment, never by comparing the top-level sigaction function pointer.
static atomic_int android_installed;
static pthread_once_t android_install_once = PTHREAD_ONCE_INIT;
static int android_install_error;
#include "crash_android_fatal.inc"
// SIGABRT 现场：fatal 行的 pc 通常落在 libc 的 abort/raise 里，guest 调用方只能看 lr。
// 这里在链回旧处置之前额外落一行（同一 fd），带 pc/lr/sp/fp/x0 与 pc/lr 是否在 guest 模块里；
// guest=1 说明 abort 由重编译的 guest 代码直接调用（游戏自己 assert），0 说明来自宿主/libc。
// 全部用 s2a_w_* 有界拼接 + 一次 write，与 fatal 行同一异步信号安全口径。
static void android_sigabrt_ctx(const ucontext_t *context) {
#if defined(__aarch64__)
    const mcontext_t *m = &context->uc_mcontext;
    char message[256];
    s2a_w_t w = {message, 0, sizeof message};
    s2a_w_raw(&w, "[s2a] Android SIGABRT ctx pc="); s2a_w_hex(&w, (uint64_t)m->pc);
    s2a_w_raw(&w, " lr="); s2a_w_hex(&w, (uint64_t)m->regs[30]);
    s2a_w_raw(&w, " sp="); s2a_w_hex(&w, (uint64_t)m->sp);
    s2a_w_raw(&w, " fp="); s2a_w_hex(&w, (uint64_t)m->regs[29]);
    s2a_w_raw(&w, " x0="); s2a_w_hex(&w, (uint64_t)m->regs[0]);
    s2a_w_raw(&w, " guest_pc="); s2a_w_dec(&w, module_of((void *)(uintptr_t)m->pc) != NULL);
    s2a_w_raw(&w, " guest_lr="); s2a_w_dec(&w, module_of((void *)(uintptr_t)m->regs[30]) != NULL);
    s2a_w_ch(&w, '\n');
    int flags = fcntl(g_s2a_logfd, F_GETFL);
    if (flags >= 0 && !fcntl(g_s2a_logfd, F_SETFL, flags | O_NONBLOCK)) {
        ssize_t ignored = write(g_s2a_logfd, message, w.n); (void)ignored;
    }
#else
    (void)context;
#endif
}
static void android_crash_fatal(int sig, siginfo_t *si, const ucontext_t *context) {
    if (sig == SIGABRT) android_sigabrt_ctx(context);
    s2a_android_fatal(sig, si, context->uc_mcontext.pc, context->uc_mcontext.sp, (void *)context);
}
static void on_crash(int sig, siginfo_t *si, void *context) {
    ucontext_t *u = context;
    // 双补丁岛 brk 兜底点（traps.c）：两岛都够不着的必改点，按原语义模拟后 pc += 4
    if (sig == SIGTRAP && s2a_trap_brk && s2a_trap_brk(context)) return;
    if (sig == SIGBUS || sig == SIGSEGV) {
        int write;
        if (s2a_android_fault_esr(context, &write)) {
            // Preserve the incoming direct-mode hook; no provider means zero.
            int s2a_direct_fault(void *, int, void *);
            if (s2a_direct_fault(si->si_addr, write, context)) return;
        }
    }
    int guest = (sig == SIGBUS || sig == SIGSEGV) && module_of((void *)(uintptr_t)u->uc_mcontext.pc) != NULL;
    int handled = s2a_android_fault_handle(sig, si->si_addr, context, guest);
    if (handled == 1) return;
    // Zero is unclaimed; negative means a required readback could not safely
    // run. Neither may fall back to tracker unprotect and return to guest.
    android_crash_fatal(sig, si, u);
}
static void android_install(void) {
    s2a_android_fault_dispatch_reset();
    for (size_t i = 0; i < S2A_ANDROID_FATAL_SIGNAL_COUNT; ++i) {
        s2a_android_fatal_remember(s2a_android_fatal_signals[i], on_crash);
        int error = plat_fault_install(s2a_android_fatal_signals[i], on_crash, PLAT_FAULT_ONSTACK);
        if (error) { android_install_error = error; return; }
    }
    atomic_store_explicit(&android_installed, 1, memory_order_release);
}
int s2a_android_fault_dispatch_installed(void) {
    return atomic_load_explicit(&android_installed, memory_order_acquire);
}
void s2a_crash_thread_init(void) {
    int error = s2a_android_fault_thread_init();
    if (error) die("Android 缺页线程初始化失败 errno=%d", error);
}
void s2a_crash_install(void) {
    int error = pthread_once(&android_install_once, android_install);
    if (error || android_install_error) die("Android 信号安装失败 errno=%d", error ? error : android_install_error);
    s2a_crash_thread_init();
}
// Android currently uses the full-readback path. The Mach context instruction
// emulation benchmark is not an Android capability or readiness check.
void s2a_emul_store_bench(void) { LOG("Android 使用完整读回；未运行 Mach 指令模拟 benchmark"); }
#else
#include "s2a_emul_st.h"
#include <mach/mach_time.h>
#include <sys/mman.h>
#include <stdatomic.h>
#include "s2a_emul_ld.h"
// 拦写模拟自测（帧率能耗线 10-24，拦写模拟开着时（缺省开，S2A_TRACK_EMUL_STORE=0 关）起局跑一次）：一张只读测试页上连写 N 次，每次都「缺页 → 信号里经可写别名模拟 → 返回」，
// 总时长 / N = 每次缺页 + 模拟的全部成本（含内核投递信号与返回；写跟踪计数里的每次耗时不含这一段）。测试页的缺页在信号处理最前面认领，不进写跟踪
static _Atomic uint64_t g_esb_page;
void s2a_emul_store_bench(void) {
    const char *e = getenv("S2A_TRACK_EMUL_STORE"); if (e && *e == '0') return;
    uint8_t *p = mmap(NULL, 0x4000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0); if (p == MAP_FAILED) return;
    memset(p, 0, 0x4000); mprotect(p, 0x4000, PROT_READ); atomic_store(&g_esb_page, (uint64_t)(uintptr_t)p);
    enum { N = 2000 }; static mach_timebase_info_data_t tb; if (!tb.denom) mach_timebase_info(&tb);
    uint64_t t0 = mach_absolute_time();
    for (int i = 0; i < N; i++) ((volatile uint32_t *)p)[(i * 17) & 0xFFF] = (uint32_t)i + 1;
    uint64_t ns = (mach_absolute_time() - t0) * tb.numer / tb.denom;
    atomic_store(&g_esb_page, 0);
    int ok = ((volatile uint32_t *)p)[((N - 1) * 17) & 0xFFF] == N;
    munmap(p, 0x4000);
    LOG("拦写模拟自测：每次缺页 + 模拟 %.2f µs（含信号投递与返回，%d 次%s）", ns / 1000.0 / N, N, ok ? "" : "；【红】写入值不对");
}
// 崩溃原始现场（两段式的第一段）：只用 write 与栈上缓冲——不取锁、不分配、不格式化浮点，崩在持日志锁 / malloc 锁的线程上也写得出来。
//   一行一项：信号、出错地址、pc / lr / sp / fp、x0–x28、帧链返回地址（经 frame_read 校验）、模块表（名、基址、大小、补丁区）——
//   离线按模块表把地址换成「模块+偏移」。第二段（下面的完整报告：符号、线程表、各种余量）尽力而为，在里面崩了这一段已经落盘
//   每行先拼进栈上一行缓冲、一次 write 落盘：同时崩的另一条线程也在写它的原始现场，按行整写才不会互相插断
typedef struct { char b[768]; size_t n; } raw_line;
static void raw_put(raw_line *l, const char *s) { while (*s && l->n < sizeof l->b - 1) l->b[l->n++] = *s++; }
static void raw_hex(raw_line *l, const char *label, uint64_t v) {
    static const char hx[] = "0123456789abcdef"; char b[24]; int k = 0; b[k++] = ' ';
    for (int sh = 60; sh >= 0; sh -= 4) b[k++] = hx[(v >> sh) & 15];
    b[k] = 0; raw_put(l, label); raw_put(l, b);
}
static void raw_end(raw_line *l) { l->b[l->n++] = '\n'; ssize_t w = write(g_s2a_logfd, l->b, l->n); (void)w; l->n = 0; }
static void crash_raw(int sig, siginfo_t *si, ucontext_t *uc, int other) {
    raw_line l = {.n = 0};
    raw_put(&l, other ? "[s2a] 【红】崩溃原始现场（另一条线程同时崩：只记这一段，等先崩的线程写完）" : "[s2a] 【红】崩溃原始现场");
    raw_hex(&l, " 信号", (uint64_t)sig); raw_hex(&l, " 地址", (uint64_t)(uintptr_t)si->si_addr);
    raw_hex(&l, " pc", uc->uc_mcontext->__ss.__pc); raw_hex(&l, " lr", uc->uc_mcontext->__ss.__lr); raw_hex(&l, " sp", uc->uc_mcontext->__ss.__sp); raw_hex(&l, " fp", uc->uc_mcontext->__ss.__fp); raw_end(&l);
    for (int i = 0; i < 29; i += 4) { raw_put(&l, "[s2a]   x"); for (int j = i; j < i + 4 && j < 29; j++) raw_hex(&l, "", uc->uc_mcontext->__ss.__x[j]); raw_end(&l); }
    uint64_t lr[32]; int k = s2a_frames(uc->uc_mcontext->__ss.__fp, lr, 32);
    raw_put(&l, "[s2a]   帧链"); for (int i = 0; i < k; i++) raw_hex(&l, "", lr[i]); raw_end(&l);
    if (other) return;   // 模块表先崩的那条已经列了
    for (int i = 0; i < g_nmod; i++) {
        char nm[17]; memcpy(nm, g_mod[i].name, 16); nm[16] = 0;
        raw_put(&l, "[s2a]   模块 "); raw_put(&l, nm); raw_hex(&l, " 基址", (uint64_t)(uintptr_t)g_mod[i].base); raw_hex(&l, " 大小", g_mod[i].size);
        raw_hex(&l, " 补丁区偏移", (uint64_t)g_mod[i].patch_off); raw_hex(&l, " 补丁区长", g_mod[i].patch_len);
        if (g_mod[i].patch2_len) { raw_hex(&l, " 补丁岛2偏移", (uint64_t)g_mod[i].patch2_off); raw_hex(&l, " 补丁岛2长", g_mod[i].patch2_len); }
        raw_end(&l);
    }
}
// 写现场的线程（第一条崩的）。原先 `static int once; if (once++) _exit()`：第二条几乎同时崩的线程直接退出整个进程，
//   第一条的现场写到一半（10-29 1-2-Switch：host.log 断在一行中间、rc=138），且 once++ 不是原子的。现在：
//   第一条照旧写完两段再 _exit；它自己在第二段里又崩 = 立即 _exit（第一段已落盘，同原先）；
//   别的线程只写自己的原始现场（无锁、按行整写），然后停在这里等第一条 _exit，最多等 10 秒（第一条卡死时不让进程挂住）
static _Atomic(pthread_t) g_crash_owner;
static void crash_other_wait(int sig) {
    struct timespec t = {0, 50 * 1000 * 1000};
    for (int i = 0; i < 200; i++) nanosleep(&t, NULL);
    _exit(128 + sig);
}
// 现场写完后按默认处置重新抛一次同一信号（#141 玩家提议）：进程以「被信号结束」收场，macOS 的 ReportCrash 生成带完整回溯的 .ips
//   （控制台「崩溃报告」/ ~/Library/Logs/DiagnosticReports），iOS 进系统崩溃日志——原先 _exit(128 + sig) 是正常退出，系统不出报告。
//   处理函数里本信号是屏蔽的，先放开再抛；万一没结束（不该发生）照旧 _exit(128 + sig)。
//   读退出码的地方：shell 里被信号结束的 $? 仍是 128 + sig；作业层 Context.run 把 Python 的负返回码折回 128 + sig（pack/jobs/core.py）
static void crash_reraise(int sig) {
    signal(sig, SIG_DFL);
    sigset_t m; sigemptyset(&m); sigaddset(&m, sig); pthread_sigmask(SIG_UNBLOCK, &m, NULL);
    raise(sig);
    _exit(128 + sig);
}
static void (*g_dsh_crash_dump)(void);   // graphics/nvn/host/dsh_miss.inc s2a_dsh_crash_dump：现编时崩溃，落盘正在编的那支输入；装信号时 dlsym 取一次（信号处理里不调 dlsym），只链运行时的单测取不到 = 空
static void on_crash(int sig, siginfo_t *si, void *ctx) {
    // 先给 16 KB 写跟踪（graphics/track）认领：游戏 / 原生层写到被写保护的游戏页，跟踪模块记脏、放开后返回重执行那条指令。
    // 是否写取 ESR 的 WnR 位（数据中止 EC = 0x24 / 0x25 时有效）
    // 写跟踪 A 方案（touch.c）：跳板回写完的 brk——恢复缺页时的现场、重执行那条写
    { int s2a_touch_brk(void *); if (sig == SIGTRAP && s2a_touch_brk(ctx)) return; }
    // 诊断钩子（diag_brk.c，S2A_DIAG_DELAY / S2A_DIAG_STAMP，只 Mac）
    { int s2a_diag_brk(void *); if (sig == SIGTRAP && s2a_diag_brk(ctx)) return; }
    // 双补丁岛 brk 兜底点（traps.c）：两岛都够不着的必改点，按原语义模拟后 pc += 4
    if (sig == SIGTRAP && s2a_trap_brk && s2a_trap_brk(ctx)) return;
    if (sig == SIGBUS || sig == SIGSEGV) {
        uint32_t esr = ((ucontext_t *)ctx)->uc_mcontext->__es.__esr, ec = esr >> 26;
        if (ec == 0x24 || ec == 0x25) {
            int w = (int)(esr >> 6 & 1); uint64_t pc = ((ucontext_t *)ctx)->uc_mcontext->__ss.__pc;
            { uint64_t bp = atomic_load(&g_esb_page), fa0 = (uint64_t)si->si_addr;   // 拦写模拟自测页（见 s2a_emul_store_bench）
              if (bp && w && (fa0 & ~0x3FFFull) == bp) { uint8_t *wa = s2a_alias_page_rw(bp); if (wa && s2a_emul_store(ctx, fa0, wa + (fa0 & 0x3FFF), NULL, NULL, NULL)) return; } }
            // 远端（far.c，乙布局）：别名区伸出宿主窗口那段一碰即缺页，在影子上代执行这条访存并记点
            { int s2a_far_fault(void *, uint64_t, int); if (s2a_far_fault(ctx, (uint64_t)si->si_addr, w)) return; }
            // 直连模式的缺页钩子（双轨，s2a_direct_host.h）：游戏代码 / 宿主代码两条分支都最先问；通用模式下没人登记，这里只读一个空指针
            { int s2a_direct_fault(void *, int, void *); if (s2a_direct_fault(si->si_addr, w, ctx)) return; }
            // 游戏代码（模块原始代码 / 补丁区）写到 GPU 改过的页：改道到正常上下文先回写；宿主代码的缺页照原路径
            if (module_of((void *)pc)) {
                // 方案 B（帧率能耗线 10-23）：游戏读到读时回写的不可读页、碰的子页不是 GPU 改过的 → 从别名模拟这条读、pc 前进，页保持不可读（不整页回写，免 16 KB / 4 KB 假共享）。
                // 模拟不了（写、独占、原子、越页、别名建不出 / 起局自检不过时 s2a_alias_page 回 NULL）落到下面原路径
                uint64_t fa = (uint64_t)si->si_addr;
                if (!w && s2a_track_read_emulable(si->si_addr)) {
                    const uint8_t *al = s2a_alias_page(fa & ~0x3FFFull);
                    if (al && s2a_emul_load(ctx, fa, al + (fa & 0x3FFF), s2a_track_emul_ok)) { s2a_track_note_emul(); return; }
                    // 模拟不了：记类别与 pc（写跟踪每 10 秒一行报，缺页处模拟的覆盖率；al 为空记类别 -1）
                    s2a_track_note_emul_fail(al ? s2a_emul_class(*(const uint32_t *)(uintptr_t)pc) : -1, *(const uint32_t *)(uintptr_t)pc, pc);
                }
                // 拦写模拟（帧率能耗线 10-24，docs/研究/拦写模拟.md；缺省开，S2A_TRACK_EMUL_STORE=0 关）：游戏写到缓冲标的 GPU 改过子页、
                // 写的字节不碰 GPU 改过的字节 → 经可写别名替它写（同宽原子存储）、记「CPU 写过」位图、pc 前进，页保持拦截，不回写不等 GPU。
                // 任一条件不满足（store_ok 里判）→ 落到下面原路径（改道回写 → 重执行）
                if (w && s2a_track_store_try(si->si_addr)) {
                    uint64_t t0 = mach_absolute_time(), ea = 0, len = 0;
                    uint8_t *wa = s2a_alias_page_rw(fa & ~0x3FFFull);
                    if (!wa) s2a_track_note_store_fail(6);
                    else if (s2a_emul_store(ctx, fa, wa + (fa & 0x3FFF), s2a_track_store_ok, &ea, &len)) {
                        static mach_timebase_info_data_t tb; if (!tb.denom) mach_timebase_info(&tb);
                        s2a_track_store_done(ea, len, (mach_absolute_time() - t0) * tb.numer / tb.denom); return; }
                    else if (!len) s2a_track_note_store_fail(7);   // 解码不认（认得但被 store_ok 拒的，原因已在 store_ok 里记）
                }
                uint64_t s2a_touch_skip(void); void s2a_touch_clear(void); int s2a_touch_redirect(void *, uint64_t);
                int r = s2a_track_fault_guest(si->si_addr, w, s2a_touch_skip());
                if (r == 2) { if (s2a_touch_redirect(ctx, (uint64_t)si->si_addr)) return; r = s2a_track_fault(si->si_addr, w); }
                s2a_touch_clear();
                if (r) return;
            } else if (s2a_track_fault(si->si_addr, w)) return;
        }
        { int s2a_det_watch_fault(uint64_t, uint64_t, uint64_t, uint64_t); ucontext_t *u = ctx;   // 确定性诊断写监视（S2A_DET_WATCH）
          if ((esr >> 6 & 1) && s2a_det_watch_fault((uint64_t)si->si_addr, u->uc_mcontext->__ss.__pc, u->uc_mcontext->__ss.__lr, u->uc_mcontext->__ss.__fp)) return; }
    }
    ucontext_t *uc = ctx; pthread_t self = pthread_self(), none = NULL;
    if (!atomic_compare_exchange_strong(&g_crash_owner, &none, self)) {
        if (pthread_equal(none, self)) _exit(128 + sig);   // 先崩的线程在写报告时自己又崩
        crash_raw(sig, si, uc, 1); crash_other_wait(sig);
    }
    uint64_t pc = uc->uc_mcontext->__ss.__pc, lr = uc->uc_mcontext->__ss.__lr, fp = uc->uc_mcontext->__ss.__fp;
    crash_raw(sig, si, uc, 0);
    // 崩在现编着色器里（graphics/nvn/host/dsh_miss.inc，#467）：把正在编的那支输入落盘成 <键>.inflight.*，诊断包带走。只用 open / write，排在原始现场之后、完整报告之前
    { if (g_dsh_crash_dump) g_dsh_crash_dump(); }
    { void (*ev)(const char *, int) = (void (*)(const char *, int))dlsym(RTLD_DEFAULT, "s2a_dguard_evidence"); if (ev) ev("崩溃", 0); }   // 直连安全网：这局算失败（有证据）；动态取，单测没链 dguard.c
    char bp[160], bl[160]; where(pc, bp, sizeof bp); where(lr, bl, sizeof bl);
    LOG("【红】CRASH 信号 %d 地址 %p pc %s lr %s sp %#llx", sig, si->si_addr, bp, bl, (unsigned long long)uc->uc_mcontext->__ss.__sp);
    for (int i = 0; i < 29; i += 4) LOG("  x%-2d %016llx %016llx %016llx %016llx", i, uc->uc_mcontext->__ss.__x[i], uc->uc_mcontext->__ss.__x[i + 1], i + 2 < 29 ? uc->uc_mcontext->__ss.__x[i + 2] : 0, i + 3 < 29 ? uc->uc_mcontext->__ss.__x[i + 3] : 0);
    s2a_backtrace(fp);
    { uint64_t ht, hl, fs, fh; int fn; s2a_low_holes(&ht, &hl); s2a_fd_usage(&fn, &fs, &fh);   // 资源耗尽类崩溃先看这两样：低区地址 / 文件句柄
      LOG("崩溃时余量：低区空洞合计 %llu MB、最大一块 %llu MB；文件句柄已开 %d 个，软上限 %llu、硬上限 %llu", (unsigned long long)(ht >> 20), (unsigned long long)(hl >> 20), fn, (unsigned long long)fs, (unsigned long long)fh); }
    s2a_lowva_crash_note();   // 低区账（各家账面、保留量、拦不到的）
    { void s2a_vm_low(const char *); s2a_vm_low("崩溃时"); }   // 低区地址耗尽类崩溃（Metal / spirv_cross / 暂存缓冲）看当时谁占着
    { void s2a_guest_va_report(const char *); s2a_guest_va_report("崩溃时"); }   // 窗口里游戏真映射了多少、落在哪
    { void s2a_diag_stamp_report(void), s2a_lockwake_report(void); s2a_diag_stamp_report(); s2a_lockwake_report(); }
    { void s2a_svc_count_report(const char *); s2a_svc_count_report("崩溃"); }   // 诊断打点（S2A_DIAG_STAMP 设了才打）
    LOG("线程表："); s2a_thread_dump();
    { void s2a_direct_wait_dump(void); s2a_direct_wait_dump(); }   // 直连模式：各等待点（s2a_crash_wait_dump_register 登记）
    { int s2a_dump_threads(const char *why); char w[64]; snprintf(w, sizeof w, "崩溃 信号 %d", sig); s2a_dump_threads(w); }
    void s2a_svc_red_summary(void); s2a_svc_red_summary();
    s2a_logcon_flush(); crash_reraise(sig);
}
// 每线程一份信号备用栈：游戏栈可能只有几 KiB，崩在上面时处理函数不能再往游戏栈压。内存从窗口尾部取（10-24 低区让给 GC；尾部放不下平台层自己 mmap）
static void *alt_tail_alloc(size_t n) { return s2a_tail_map(n, S2A_TAIL_ALTSTACK | S2A_TAIL_ONLY, PROT_READ | PROT_WRITE); }
static void alt_tail_release(void *p, size_t n) { s2a_tail_unmap(p, n, S2A_TAIL_ALTSTACK); }
void s2a_crash_thread_init(void) {
    plat_fault_altstack_set_mem(alt_tail_alloc, alt_tail_release);
    { void s2a_touch_thread_init(void); s2a_touch_thread_init(); }   // 写跟踪 A 方案的每线程保存区（信号处理里不分配）
    // 缺页处模拟读的只读别名槽（alias.c，每线程 16 KB）
    s2a_alias_thread_init();
    int e = plat_fault_altstack_init();
    if (e) LOG("【红】崩溃：备用栈安装失败 errno=%d", e);
}
void s2a_crash_install(void) {
    int sigs[] = {SIGSEGV, SIGBUS, SIGILL, SIGTRAP, SIGFPE, SIGABRT};   // SIGABRT：die() 与 C# FailFast 都走 abort，要现场
    g_dsh_crash_dump = (void (*)(void))dlsym(RTLD_DEFAULT, "s2a_dsh_crash_dump");
    for (size_t i = 0; i < sizeof sigs / sizeof *sigs; i++) {
        int e = plat_fault_install(sigs[i], on_crash, PLAT_FAULT_ONSTACK);
        if (e) LOG("【红】崩溃：安装信号 %d 失败 errno=%d", sigs[i], e);
    }
    s2a_crash_thread_init();
}
#endif
