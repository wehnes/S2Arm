// 64 GB 地址窗口（方案 5a-1）：包括 iOS 预热在内，都在最早构造阶段占窗，客体地址空间全部区域在里面排。
// 只占地址、不占内存（footprint 不计）。必须早于 NativeAOT 运行时与 Metal 初始化，否则它们的大块预留可能先落进来。
// S2A_VAWIN_NORESERVE=1（诊断，5b-1 量法）：不占窗口，只在各时刻探测别人有没有映射进来。
#if defined(__ANDROID__)
#include "../../android/native/runtime/platform/vawin_android.inc"
#else
#include "native.h"
#include "imgpack.h"
#include "as_type.h"
#include "s2a_docs.h"   // 文档根唯一取法
#include "s2a_launch_ctx.h"
#include <errno.h>
#include <dirent.h>
#include <dlfcn.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/sysctl.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <mach/mach.h>
#include <mach/vm_map.h>
#include <TargetConditionals.h>
#ifdef __IPHONE_OS_VERSION_MIN_REQUIRED   // 按 iOS SDK 编才有（Mac SDK 标成不可用）；t_ios_prewarm 在 Mac 上把 TARGET_OS_IPHONE 改成 1 编本文件，不能按它判
#include <os/proc.h>   // os_proc_available_memory：客体内存文件后备的自动判定
#else
#include <dispatch/dispatch.h>   // Mac：系统内存压力监听（文件后备的安全阀，#306）
#endif
#include <crt_externs.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>

static int g_ok;            // 1 = 窗口已占到（首选位置整块 64 GB，或退路：2^39 以下最大空洞里的一块，见 vawin_reserve）
static int g_noreserve;
static uint64_t g_base, g_size;
static uint64_t g_keep_lo;   // 放不下标准布局时窗口下方留给宿主的那段起点（0 = 没有）：Mac 复现 iPhone 约束时不占它（iphone_va_fence）
static uint64_t g_res;       // 起局时预留的大小（收尾部前的 g_size）：「还给系统 / 交尾部分配的那段」= [g_base + g_size, g_base + g_res)
// 客体内存改文件后备（S2A_GUEST_FILE；11-05 时之笛 Switch 2 iPhone 读档进场景被单进程上限 8192 MB 杀）。开不开见 s2a_guest_file_wanted：
//   =0 关、其余非空值开；不设时 iOS 上本款应用内存池 > 起局时 os_proc_available_memory() 就开（装不下才付闪存写入的代价），Mac 不设 = 关（Mac 会换页，没有单进程上限）
//   iOS 判杀按 phys_footprint，匿名脏页（含压缩）全计；文件 MAP_SHARED 映射的脏页归文件页缓存，不计（M5 Pro 实测：同样写 2 GB，匿名 +2048 MB、文件 +1 MB；
//   本仓 Mac 小程序：写 512 MB +0.5 MB，逐页读未写页 +0.5 MB）。窗口占到后整段换成一个临时文件（建完立刻 unlink，进程退出 / 被杀时系统收回）的
//   MAP_SHARED 映射，偏移 = 地址 − 窗口基址，保护仍是 PROT_NONE，之后的 mprotect / vm_remap 别名 / 零拷贝 MTLBuffer 照旧（Mac 实测 GPU 读写、两处映射一致）。
//   还页（缩堆、解除物理映射、解别名）改成「打洞 + 原偏移重新映射成 PROT_NONE」：打洞把那段文件块还回去，再读是 0，同匿名占位的语义（s2a_guest_zero）。
//   写保护缺页在文件映射上同样是 SIGBUS（同匿名，Mac 实测）。代价：内存紧张时内核把脏页写回闪存（写量 / 帧时待真机量）
static int g_gfd = -1;
int s2a_guest_fd(void) { return g_gfd; }
// 开不开（纯函数，t_guest_file_auto 测）：e = S2A_GUEST_FILE；pool = 本款应用内存池；room = 起局时离系统给本进程的内存上限还剩多少（os_proc_available_memory，
//   0 = 不知道上限，Mac 恒传 0）；host = 宿主自身开销估计；margin = 余量。设了按设的（"0" 关、其余开）；没设 → 上限已知且「池 + 宿主开销 + 余量」装不下才开。
//   11-06 维护者：原先只比「池 > 剩余」，漏算宿主开销——DOOM Eternal 池 3285 MB、宿主约 2258 MB（Mac 同局足迹 5543 MB），足迹按池算装得下、实际已逼近上限。
//   17 Pro Max（上限 8191 MB）上 Switch 1 款 3285 + 2560 + 512 = 6357 MB 装得下 → 不开、不付闪存写回代价；内存更小的机型、Switch 2 款（池 9 GiB）自动开兜底
// 新判据另起名、不改 native.h（它是抽取阶段键，改声明会让全款重抽取）；native.h 里的 3 参 s2a_guest_file_wanted 保留为「宿主开销与余量取 0」的旧口径
int s2a_guest_file_wanted2(const char *e, uint64_t pool, uint64_t room, uint64_t host, uint64_t margin) {
    return e && *e ? strcmp(e, "0") != 0 : room && pool + host + margin > room;
}
int s2a_guest_file_wanted(const char *e, uint64_t pool, uint64_t room) { return s2a_guest_file_wanted2(e, pool, room, 0, 0); }
// 11-07 卡顿线（火炬之光3 / WWZ 测试设备2 卡顿、整进程停 3–4 s，2 分钟写盘 6–7.5 GB）：剩余 6141 MB 的 iPhone 上 Switch 1 款「池 3285 + 宿主估计 2560 + 余量 512 = 6357」
//   一律判开（878 份日志里 22 款 16 款、130 / 234 局），实际进程实占多在 0.8–1.5 GB。池是客体能要的上界、2560 是 DOOM 的最坏宿主开销，两个最坏叠在一起。改为按实测：
//   ① 设了按设的；② 上限未知（Mac）关；③ 池本身 > 剩余 → 开（Switch 2 池 9 GiB，时之笛）；④ 本机本款记过实测峰值 seen（心跳记：进程实占 + 文件后备里客体已写的字节，
//   s2a_guest_mem_note）→ seen + 余量 > 剩余才开；⑤ 没记过 → 池 + 宿主估计 + 余量 > 剩余才开，宿主估计缺省 2048 MB（11-07 真机开着文件后备的局，进程实占≈宿主开销：
//   Switch 1 15 款 792–1545 MB 的 13 款、2348 / 2573 各 1 款、GRID 4125 MB；GRID 这类首局判关时由 ④ 在下一局纠正）
// ⑥ 安全阀（11-07 维护者）：上一局在前台时死掉（died：「在跑」标记还在，见 s2a_guest_run_mark）→ 这一局强制开。按估计 / 实测判了不开、实际超上限被系统杀的那一局，
//   峰值可能来不及记进 mem_peak（心跳 10 秒一次），不兜住就会每局判关、每局被杀；强制开的这一局记下真实峰值（含文件里的客体字节），下一局再按实测判
int s2a_guest_file_wanted4(const char *e, uint64_t pool, uint64_t room, uint64_t seen, uint64_t host, uint64_t margin, int died) {
    if (e && *e) return strcmp(e, "0") != 0;
    if (!room) return 0;
    if (pool > room || died || seen == UINT64_MAX) return 1;   // UINT64_MAX：坏记录（s2a_guest_mem_seen），保守开
    if (seen) return seen + margin > room;
    return pool + host + margin > room;
}
int s2a_guest_file_wanted3(const char *e, uint64_t pool, uint64_t room, uint64_t seen, uint64_t host, uint64_t margin) {
    if (e && *e) return strcmp(e, "0") != 0;
    if (!room) return 0;
    if (pool > room) return 1;
    if (seen) return seen + margin > room;
    return pool + host + margin > room;
}
// 本款本机实测峰值的记录：$HOME/Documents/wire/<程序号大写 16 位>/mem_peak（同 pso_user.tsv 的目录），一行十进制字节数。程序号按名字取（单测只链 vawin.c）
static int mem_peak_path(char *out, size_t n);
// 「本局在跑」标记（同目录 running）：App 到前台时写、进后台 / 将终止时删（ios/app.m 调 s2a_guest_run_mark）。iOS 上玩家划掉 / 系统在后台回收都不走正常退出，
//   所以「干净」= 进了后台；标记还在 = 上一局在前台时死掉（被内存上限杀、崩溃）。预热进程没到前台不写，被系统回收不误判。崩溃也会留标记：多开一局文件后备，可接受
static int run_mark_path(char *out, size_t n) {
    const char *ov = getenv("S2A_GUEST_RUN_MARK"); if (ov && *ov) { snprintf(out, n, "%s", ov); return 1; }
    char p[1024]; if (!mem_peak_path(p, sizeof p)) return 0;
    char *sl = strrchr(p, '/'); if (!sl) return 0; *sl = 0; snprintf(out, n, "%s/running", p); return 1;
}
int s2a_guest_run_died(void) { char p[1100]; struct stat st; return run_mark_path(p, sizeof p) && !stat(p, &st); }
void s2a_guest_run_mark(int running) {
    char p[1100]; if (!run_mark_path(p, sizeof p)) return;
    if (!running) { unlink(p); return; }
    { char d[1100]; snprintf(d, sizeof d, "%s", p); char *sl = strrchr(d, '/'); if (sl) { *sl = 0; mkdir(d, 0755); } }
    FILE *f = fopen(p, "w"); if (f) { fprintf(f, "%d\n", (int)getpid()); fclose(f); }
}
// 构造期（占窗口、判文件后备开不开）用的程序号：need_from_npdm 从本款 main.npdm 直接读（svc_mem.c s2a_npdm_pid），不经图形模式（审计 P1-139：
//   那时 iOS 的 s2a_gfx_mode 还没放行、程序号恒 0，Mac 上调它会把模式和程序号 0 落定）。多款容器构造期没选游戏，保持 0（按最大池判，#103）
static uint64_t g_ctor_pid; static int g_attach_phase;
static int mem_peak_path(char *out, size_t n) {
    uint64_t (*pidf)(void) = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "s2a_npdm_program_id"); const char *ov = getenv("S2A_GUEST_MEM_PEAK");
    if (ov && *ov) { snprintf(out, n, "%s", ov); return 1; }   // 单测 / 诊断指定
    uint64_t pid = g_attach_phase ? g_ctor_pid : pidf ? pidf() : 0;   // 构造期只认 npdm 直读的；局中（心跳记峰值）照旧按当前程序号
    if (!pid) return 0;
    s2a_docs_path(out, n, "wire/%016llX/mem_peak", (unsigned long long)pid); return 1;
}
// 读本款实测峰值：没有记录 → 0（按估计判）；记录在但读不出 / 为 0 → S2A_GUEST_SEEN_BAD（坏记录，按装不下判，保守开；性能线 A 审：不能因读坏文件判关）
#define S2A_GUEST_SEEN_BAD UINT64_MAX
uint64_t s2a_guest_mem_seen(void) {
    char p[1024]; if (!mem_peak_path(p, sizeof p)) return 0;
    FILE *f = fopen(p, "r"); if (!f) return errno == ENOENT ? 0 : S2A_GUEST_SEEN_BAD;
    unsigned long long v = 0; int ok = fscanf(f, "%llu", &v) == 1 && v; fclose(f); return ok ? v : S2A_GUEST_SEEN_BAD;
}
// 心跳调（每 10 秒，后台串行队列）：footprint = 进程实占字节；开着文件后备时加上文件里已落块的客体字节（脏页不计实占，换成匿名就都算）。比记录大才写（tmp + rename）
static void span_note(void);
void s2a_guest_mem_note(uint64_t footprint) {
    span_note();   // 心跳顺带记本局跨度（#783）
    uint64_t total = footprint; struct stat st;
    if (g_gfd >= 0 && !fstat(g_gfd, &st)) total += (uint64_t)st.st_blocks * 512ull;
    static uint64_t rec; static int loaded; if (!loaded) { rec = s2a_guest_mem_seen(); if (rec == UINT64_MAX) rec = 0; loaded = 1; }   // 坏记录：本局的实测覆盖它
    if (total <= rec) return;
    char p[1024], t[1100]; if (!mem_peak_path(p, sizeof p)) return;
    { char d[1024]; snprintf(d, sizeof d, "%s", p); char *sl = strrchr(d, '/'); if (sl) { *sl = 0; mkdir(d, 0755); } }
    snprintf(t, sizeof t, "%s.tmp", p); FILE *f = fopen(t, "w"); if (!f) return;
    fprintf(f, "%llu\n", (unsigned long long)total); fclose(f);
    if (!rename(t, p)) rec = total;
}
// 本款本机学到的地址跨度（#783）：同目录 span_peak，一行十进制字节数 = 局中碰到的最高地址 − 窗口基址（svc_mem.c s2a_mem_span_now，心跳每 10 秒比大才写）。
//   窗口放不下标准布局时按它给窗口、其余留给宿主（s2a_window_host_below）；没记录 / 读不出 = 0（照旧只留 HOST_BELOW）
static uint64_t read_u64(const char *p) { FILE *f = fopen(p, "r"); if (!f) return 0; unsigned long long v = 0; int ok = fscanf(f, "%llu", &v) == 1; fclose(f); return ok ? v : 0; }
static int span_path(char *out, size_t n, uint64_t pid) {   // pid = 0：按局中当前程序号（同 mem_peak 目录）
    const char *ov = getenv("S2A_WIN_SPAN_PEAK"); if (ov && *ov) { snprintf(out, n, "%s", ov); return 1; }   // 单测 / 诊断指定
    if (pid) { s2a_docs_path(out, n, "wire/%016llX/span_peak", (unsigned long long)pid); return 1; }
    if (!mem_peak_path(out, n)) return 0;
    char *sl = strrchr(out, '/'); if (!sl) return 0; snprintf(sl + 1, n - (size_t)(sl + 1 - out), "span_peak"); return 1;
}
uint64_t s2a_window_span_seen(uint64_t pid) { char p[1024]; return pid && span_path(p, sizeof p, pid) ? read_u64(p) : 0; }
static uint64_t g_span_learned;   // 本款（多款容器 = 各款最大，有一款没记录就 0）学到的跨度
// 自愈：窗口按学到的跨度收窄后布局仍放不下（svc_mem.c 起局判「连模块段、栈、堆前段都放不下」那一刻）——这份记录不可信，删掉，下一局退回缺省给法
void s2a_window_span_forget(void) {
    if (!g_span_learned) return;
    char p[1024]; if (!span_path(p, sizeof p, 0)) return;
    if (!unlink(p)) LOG("【黄】地址窗口：按学到的跨度 %llu MB 收窄后放不下本款布局，删掉这份记录（%s），下一局按缺省给窗口", (unsigned long long)(g_span_learned >> 20), p);
}
// 只记真跑起来的局（11-12 iPhone 实机实测回归）：一局刚开就死（缺直连库、崩、被杀）只碰到 2.26 GB，记下后下一局窗口按它缩到 5 GB，
//   连模块段、栈、堆前段都放不下、起不了局；起不来的局永远写不出更大的值，从此每次都起不来。出图满 SPAN_MIN_PRESENTS 次之后才记
#define SPAN_MIN_PRESENTS 300
int s2a_window_span_worth(uint64_t presents) { return presents >= SPAN_MIN_PRESENTS; }   // 纯函数，t_vawin_learned 测
static void span_note(void) {   // s2a_mem_span_now 在 svc_mem.c、mtl_present_count 在直连图形层：按名字取（只链 vawin.c 的单测没有它们；取不到 = 不记）
    static uint64_t (*spanf)(void), (*presf)(void); static int looked;
    if (!looked) { spanf = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "s2a_mem_span_now"); presf = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "mtl_present_count"); looked = 1; }
    if (!presf || !s2a_window_span_worth(presf())) return;
    uint64_t now = spanf ? spanf() : 0; if (!now) return;
    char p[1024], t[1100]; if (!span_path(p, sizeof p, 0)) return;
    static uint64_t rec; static int loaded; if (!loaded) { rec = read_u64(p); loaded = 1; }
    if (now <= rec) return;
    { char d[1024]; snprintf(d, sizeof d, "%s", p); char *sl = strrchr(d, '/'); if (sl) { *sl = 0; mkdir(d, 0755); } }
    snprintf(t, sizeof t, "%s.tmp", p); FILE *f = fopen(t, "w"); if (!f) return;
    fprintf(f, "%llu\n", (unsigned long long)now); fclose(f);
    if (!rename(t, p)) rec = now;
}
static uint64_t env_mb(const char *k, uint64_t def) { const char *v = getenv(k); return (v && *v ? strtoull(v, NULL, 10) : def) << 20; }
static int g_ctr;
static uint64_t g_ctr_pool;   // 多款容器：包内各款应用池的最大值（构造期还没选游戏，文件后备按最大的判）
uint64_t s2a_window_container_pool(void) { return g_ctr_pool; }
// Mac 开不开（纯函数，t_guest_file_auto 测；#306）：设了按设的（"0" 关、其余开）；没设 → ① 池本身大于「物理内存 − 预留」（room，0 = 读不到）就开：
//   池放不进物理内存，第一局就要兜底，不等压力记录（PR #353，wwmogu）；② 否则本机本款上一局到过系统内存压力「严重」档才开（池装得下但实际挤爆的那种）。
//   不加宿主开销估计、不看实测峰值：峰值含文件里已落块的客体字节，懒清零后只涨不降，开过一次就会一直判开（#353）
int s2a_guest_file_wanted_mac(const char *e, uint64_t pool, uint64_t room, int pressed) {
    if (e && *e) return strcmp(e, "0") != 0;
    return (room && pool > room) || pressed;
}
// 压力记录：同 mem_peak 目录的 mem_pressure（存在 = 到过「严重」档；单测 / 诊断用 S2A_GUEST_PRESSURE_MARK 指定）。记下后一直有效：内存不够是这台机器跑这款的属性
static int pressure_path(char *out, size_t n) {
    const char *ov = getenv("S2A_GUEST_PRESSURE_MARK"); if (ov && *ov) { snprintf(out, n, "%s", ov); return 1; }
    char p[1024]; if (!mem_peak_path(p, sizeof p)) return 0;
    char *sl = strrchr(p, '/'); if (!sl) return 0; *sl = 0; snprintf(out, n, "%s/mem_pressure", p); return 1;
}
int s2a_guest_pressure_seen(void) { char p[1100]; struct stat st; return pressure_path(p, sizeof p) && !stat(p, &st); }
static char g_pressure_path[1100];   // 起局时定（构造期按 npdm 程序号），压力回调里只写这一处
// 记一次「严重」：写记录（只写一次）。压力回调调；单测直接调
void s2a_guest_pressure_note(void) {
    static int done; if (done) return;
    if (!g_pressure_path[0] && !pressure_path(g_pressure_path, sizeof g_pressure_path)) { g_pressure_path[0] = 0; return; }
    done = 1;
    { char d[1100]; snprintf(d, sizeof d, "%s", g_pressure_path); char *sl = strrchr(d, '/'); if (sl) { *sl = 0; mkdir(d, 0755); } }
    FILE *f = fopen(g_pressure_path, "w"); if (f) { fprintf(f, "critical %ld\n", (long)time(NULL)); fclose(f); }
    LOG("【黄】系统内存压力到「严重」档：已记下（%s），下一局本款自动开客体内存文件后备（#306 安全阀）", f ? "写成" : "写不了记录");
}
#ifndef __IPHONE_OS_VERSION_MIN_REQUIRED
// Mac 匿名内存模式下监听系统内存压力（libdispatch，后台队列）；程序号未知（多款容器构造期）就不记
static void guest_pressure_watch(void) {
    if (!pressure_path(g_pressure_path, sizeof g_pressure_path)) { g_pressure_path[0] = 0; return; }
    static dispatch_source_t src;
    src = dispatch_source_create(DISPATCH_SOURCE_TYPE_MEMORYPRESSURE, 0, DISPATCH_MEMORYPRESSURE_CRITICAL, dispatch_get_global_queue(QOS_CLASS_UTILITY, 0));
    if (!src) return;
    dispatch_source_set_event_handler(src, ^{ if (dispatch_source_get_data(src) & DISPATCH_MEMORYPRESSURE_CRITICAL) s2a_guest_pressure_note(); });
    dispatch_resume(src);
}
#endif
static void guest_file_map(void);
// 判了要接文件、空间检查没过（#483 时之笛 iPhone：进程一起来就判，那一刻 App 正在同一进程里解刚推上来的 2.5 GB 资源包，剩余 2367 MB < 12288 MB，
//   退回匿名内存，池 9 GB 装不下，6 分钟后涨到系统上限被收掉；同一台手机解完包重开那局空间够、接上了）：记下来，装游戏模块前再查一次
static int g_gfile_pending; static uint64_t g_gfile_need, g_gfile_avail;
static void guest_file_attach_(void);
static void guest_file_attach(void) { g_attach_phase = 1; guest_file_attach_(); g_attach_phase = 0; }
// 测试开关 S2A_TEST_BALLAST_MB=<N>（11-12，小内存机型问题在大内存设备上复现用；缺省不设 = 不占）：模拟给 App 少 N MB 内存的机型（#807 6 GB 机型约 4 GB）。
//   分两步：① 起局判文件后备时，离单进程上限的余量先扣掉 N MB（判定结果同小内存机型）；② 布局排完、装游戏模块之前（host_main.c load_session_modules）
//   才真占住并逐页写满 N MB 匿名内存、整局不还（实占与系统可用内存都少这么多，内存吃紧时内核换出文件后备脏页的时机也接近）。
//   不在起局时就占：那时地址窗口刚占好、布局还没排，几 GB 匿名映射会挤掉布局要的地址（11-12 实测：报「地址窗口连模块段都放不下」）。
//   只认环境变量，玩家从图标启动不带它
static uint64_t test_ballast_bytes(void) { const char *e = getenv("S2A_TEST_BALLAST_MB"); return e && *e ? strtoull(e, NULL, 10) << 20 : 0; }
void s2a_test_ballast_commit(void) {
    static int done; uint64_t n = test_ballast_bytes(); if (!n || done++) return;
    uint64_t t0 = clock_gettime_nsec_np(CLOCK_UPTIME_RAW); uint8_t *p = mmap(NULL, n, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (p == MAP_FAILED) { LOG("【红】测试压舱：占 %llu MB 匿名内存失败（errno=%d）", (unsigned long long)(n >> 20), errno); return; }
    for (uint64_t o = 0; o < n; o += 16384) p[o] = (uint8_t)(o >> 14 | 1);   // 每页写一字节：页真提交、算进实占（全零页会被压缩，写非零）
#ifdef __IPHONE_OS_VERSION_MIN_REQUIRED
    uint64_t room = os_proc_available_memory();
#else
    uint64_t room = 0;
#endif
    LOG("【黄】测试压舱：装模块前占住并写满 %llu MB 匿名内存（%.1f 秒），此刻离单进程内存上限还剩 %llu MB（S2A_TEST_BALLAST_MB，只给测试局）",
        (unsigned long long)(n >> 20), (clock_gettime_nsec_np(CLOCK_UPTIME_RAW) - t0) / 1e9, (unsigned long long)(room >> 20));
}
static void guest_file_attach_(void) {
    // 池：s2a_app_pool（layout.c；Switch 3285 MiB、Switch 2 9 GiB）。此刻已定：上一步 need_from_npdm → s2a_npdm_window_need → npdm_read 认出 Switch 2 时就设了 9 GiB。
    //   它是游戏能向系统要的内存总量（SetHeapSize 上限 = 池 − 映像），客体脏页最多涨到这么多；窗口跨度（几十 GB 地址）不是内存，堆区随池定，game.tsv 的 app_pool 是图形层的、要到图形初始化才读。
    //   按名字取（dlsym）：单测只链 vawin.c、不链 layout.c；取不到记 0（自动判定按装得下 = 关）
    const char *e = getenv("S2A_GUEST_FILE");
    uint64_t (*poolf)(void) = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "s2a_app_pool"); uint64_t pool = poolf ? poolf() : 0;
    if (g_ctr && g_ctr_pool > pool) pool = g_ctr_pool;   // 多款容器：不按缺省池判，否则 Switch 2 款进局后内存超单进程上限被杀（#103）
#ifdef __IPHONE_OS_VERSION_MIN_REQUIRED
    uint64_t room = os_proc_available_memory(), ballast = test_ballast_bytes();   // 预热进程（ActivePrewarm）此刻的上限可能是后台档，偏小只会多开、不会漏开
    // 宿主开销估计缺省 2560 MB（DOOM Eternal 实测约 2258 MB，往上取整）、余量 512 MB；S2A_GUEST_FILE_HOST_MB / S2A_GUEST_FILE_MARGIN_MB 可改
    // 宿主开销估计缺省 2048 MB（11-07 真机实测分布，见 s2a_guest_file_wanted3）、余量 512 MB；S2A_GUEST_FILE_HOST_MB / S2A_GUEST_FILE_MARGIN_MB 可改
    if (ballast) { room = room > ballast ? room - ballast : 1; LOG("【黄】测试压舱：文件后备判定按余量少 %llu MB 算（S2A_TEST_BALLAST_MB，装模块前才真占）", (unsigned long long)(ballast >> 20)); }
    uint64_t host = env_mb("S2A_GUEST_FILE_HOST_MB", 2048), margin = env_mb("S2A_GUEST_FILE_MARGIN_MB", 512), seen = s2a_guest_mem_seen();
    int died = room && s2a_guest_run_died();
    int on = s2a_guest_file_wanted4(e, pool, room, seen, host, margin, died);
    const char *why = e && *e ? "按 S2A_GUEST_FILE 显式设定" : !room ? "自动：不知道单进程上限（Mac 会换页），缺省关"
                    : pool > room ? "自动：池本身大于剩余，装不下"
                    : died ? "自动：上一局在前台时死掉（「在跑」标记还在：被内存上限杀 / 崩溃 / 测试局在前台被 devicectl 结束），这一局强制开、记下真实峰值"
                    : seen == UINT64_MAX ? "自动：本款实测峰值记录读不出（坏记录），保守开"
                    : seen ? (on ? "自动：本机本款实测峰值 + 余量大于剩余，装不下" : "自动：本机本款实测峰值 + 余量不大于剩余，装得下、保持匿名内存")
                    : (on ? "自动：没有本款实测，池 + 宿主开销估计 + 余量大于剩余，装不下" : "自动：没有本款实测，池 + 宿主开销估计 + 余量不大于剩余，装得下、保持匿名内存");
    LOG("客体内存文件后备：%s——%s；本款应用内存池 %llu MB、离单进程内存上限还剩 %llu MB%s、本机本款实测峰值 %llu MB（0 = 没有）、宿主开销估计 %llu MB%s", on ? "开" : "关", why,
        (unsigned long long)(pool >> 20), (unsigned long long)(room >> 20), room ? "" : "（0 = 未知）", (unsigned long long)(seen == UINT64_MAX ? 0 : seen >> 20), (unsigned long long)(host >> 20), s2a_process_prewarmed() ? "；预热进程" : "");
    if (!on) return;
    guest_file_map();
#else
    // Mac 缺省匿名内存，池本身放不进物理内存、或本机本款上一局到过系统内存压力「严重」档时开文件后备（s2a_guest_file_wanted_mac；#306 / #353）。
    //   原先按「物理内存 − 6 GB」判（#41 / #68），16 GB 机器跑 Switch 2 款一律开，撞上 macOS 脏文件页上限：脏页过阈值后每缺一页都等内核写回一页，
    //   阈值随物理内存缩放（16 GB Mac 逐页写共享文件映射，2.2 GB 后 1.5 → 26 µs/页 = SSD 写速；128 GB 机器写 8 GB 无拐点；匿名 0.7 µs/页）。
    //   游戏内停 141 / 397 s、一局写盘 31 GB（#306 贡献者 M1 Pro 16 GB）。匿名内存只在真不够时由系统压缩 / 换出；真不够（#68：压缩器吃满、WindowServer 被杀）由压力记录兜住
    {
        uint64_t ph = 0, room = 0; size_t phn = sizeof ph, reserve = env_mb("S2A_GUEST_FILE_MAC_RESERVE_MB", 6144);
        if (!sysctlbyname("hw.memsize", &ph, &phn, NULL, 0) && ph > reserve) room = ph - reserve;
        int pressed = s2a_guest_pressure_seen(), on = s2a_guest_file_wanted_mac(e, pool, room, pressed);
        LOG("客体内存文件后备：%s——%s；本款应用内存池 %llu MB、物理内存 − 预留 %llu MB", on ? "开" : "关",
            e && *e ? "按 S2A_GUEST_FILE 显式设定" : room && pool > room ? "自动：池本身大于物理内存 − 预留，装不下"
            : pressed ? "自动：本机本款上一局到过系统内存压力「严重」档" : "自动：Mac 缺省匿名内存（系统按需压缩 / 换出）",
            (unsigned long long)(pool >> 20), (unsigned long long)(room >> 20));
        if (!on) { guest_pressure_watch(); return; }
        guest_file_map();
        return;
    }
#endif
}
// 整段窗口换成临时文件的 MAP_SHARED 映射（判了开之后；iOS / Mac 共用）
static void guest_file_map(void) {
    const char *td = getenv("TMPDIR"); char path[1024]; snprintf(path, sizeof path, "%s/s2a_guest_%d.bin", td && *td ? td : "/tmp", (int)getpid());
    // 起局前查闪存剩余空间（11-05 能耗线）：文件稀疏，只占内核写回的块，最坏涨到游戏弄脏的客体内存总量（Switch 2 是 12 GB）。
    //   不够就不接文件、照旧用匿名内存（等于开关关），打一行黄；门槛 S2A_GUEST_FILE_MIN_FREE_MB（缺省 12288）
    { const char *m = getenv("S2A_GUEST_FILE_MIN_FREE_MB"); uint64_t need = (m && *m ? strtoull(m, NULL, 10) : 12288ull) << 20; struct statfs sf;
      if (statfs(td && *td ? td : "/tmp", &sf)) {
          if (g_gfile_pending) g_gfile_avail = UINT64_MAX;   // 补接时这次没查到：别拿起局时那次的旧剩余数告诉玩家（审计 P2-265）
          LOG("【黄】客体内存文件后备：查不了临时目录剩余空间（errno=%d），照旧用匿名内存", errno); return; }
      uint64_t avail = (uint64_t)sf.f_bavail * (uint64_t)sf.f_bsize;
      // iPhone：f_bavail 不含系统随时能清掉的空间（「设置 → 储存空间」的「可用」含它），常小好几 GB；有「重要用途」口径就取大的那个（ios/app.m）
      { uint64_t (*important)(const char *) = (uint64_t (*)(const char *))dlsym(RTLD_DEFAULT, "s2a_ios_free_important");
        uint64_t imp = important ? important(td && *td ? td : "/tmp") : 0; if (imp > avail) avail = imp; }
      if (avail < need) {   // 先不接、记下「要接没接上」，开局装模块前再试一次（s2a_guest_file_retry）
          g_gfile_pending = 1; g_gfile_need = need; g_gfile_avail = avail;
          LOG("【黄】客体内存文件后备：临时目录剩余 %llu MB < 需要 %llu MB（S2A_GUEST_FILE_MIN_FREE_MB），先用匿名内存，装游戏前再查一次", (unsigned long long)(avail >> 20), (unsigned long long)(need >> 20)); return; }
      g_gfile_pending = 0; }
    int fd = open(path, O_RDWR | O_CREAT | O_EXCL, 0600);
    if (fd < 0) { LOG("【红】客体内存文件后备：建不了临时文件（errno=%d），照旧用匿名内存", errno); return; }
    unlink(path);
    if (ftruncate(fd, (off_t)g_size)) { LOG("【红】客体内存文件后备：文件定长 %llu MB 失败（errno=%d），照旧用匿名内存", (unsigned long long)(g_size >> 20), errno); close(fd); return; }
    void *p = mmap((void *)g_base, g_size, PROT_NONE, MAP_FIXED | MAP_SHARED, fd, 0);
    if (p != (void *)g_base) {   // 失败时那段可能已被拆掉：盖回匿名占位
        int er = errno; mmap((void *)g_base, g_size, PROT_NONE, MAP_FIXED | MAP_PRIVATE | MAP_ANON, -1, 0); close(fd);
        LOG("【红】客体内存文件后备：窗口 %#llx +%llu MB 映射成文件失败（errno=%d），照旧用匿名内存", (unsigned long long)g_base, (unsigned long long)(g_size >> 20), er); return; }
    g_gfd = fd;
    LOG("客体内存文件后备：窗口 %#llx +%llu MB 映射到临时文件（已 unlink，稀疏），脏页不计进程实占（S2A_GUEST_FILE）", (unsigned long long)g_base, (unsigned long long)(g_size >> 20));
}
// 开局装模块前（host_main.c load_session_modules）：起局时判了要接文件、但空间不够的，此刻（解包已完）再查一次、够了就接上。
//   只在窗口还原封不动（整段一块 PROT_NONE 的匿名保留）时才换：换成文件是整段 MAP_FIXED，窗口里已经有东西就会被抹掉，那种情形不换、照旧匿名。
//   还是不够：报红，并在屏幕上告诉玩家差多少空间（不然这款几分钟后涨到单进程上限被系统收掉，没有崩溃报告，玩家只看到闪退）
int s2a_guest_file_retry(void) {
    if (!g_gfile_pending || g_gfd >= 0 || !g_ok) return 0;
    // 窗口起局后分成几段保留（构造时就不止一段），逐段看：全部仍是 PROT_NONE、非共享 = 还没放开过、没有内容
    for (vm_address_t a = (vm_address_t)g_base, end = (vm_address_t)(g_base + g_size); a < end; ) {
        vm_address_t ra = a; vm_size_t sz = 0; vm_region_basic_info_data_64_t bi; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        if (vm_region_64(mach_task_self(), &ra, &sz, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&bi, &cnt, &obj) != KERN_SUCCESS || ra >= end) break;
        if (bi.protection != VM_PROT_NONE || bi.shared) {
            LOG("【黄】客体内存文件后备：装游戏前想补接文件，但窗口里已有放开过的映射（%#llx +%llu MB，权限 %d），不换，照旧匿名内存", (unsigned long long)ra, (unsigned long long)(sz >> 20), bi.protection);
            g_gfile_pending = 0; return 0; }
        a = ra + sz;
    }
    guest_file_map();
    if (g_gfd >= 0) { LOG("客体内存文件后备：装游戏前补接上了（起局时剩余 %llu MB 不够，此刻够了）", (unsigned long long)(g_gfile_avail >> 20)); return 1; }
    if (g_gfile_pending) {
        g_gfile_pending = 0;
        int unknown = g_gfile_avail == UINT64_MAX;   // 这次没查到剩余空间
        if (unknown) LOG("【黄】客体内存文件后备：装游戏前查不到剩余空间，没接上文件（需要 %llu MB）；这款内存池装不进单进程上限，玩一会儿会被系统收掉", (unsigned long long)(g_gfile_need >> 20));
        else LOG("【黄】客体内存文件后备：装游戏前仍不够，剩余 %llu MB < 需要 %llu MB；这款内存池装不进单进程上限，玩一会儿会被系统收掉", (unsigned long long)(g_gfile_avail >> 20), (unsigned long long)(g_gfile_need >> 20));
        // 不弹窗（玩家看着像被拦）：起局本来不拦，只是退回匿名内存；日志里有这一行
    }
    return 0;
}
// 窗口外也要文件后备的一段（远端影子区堆区余量用完、改从宿主任意空闲地址分时，far.c）：文件往后接长，按新偏移映射到内核挑的地址（同匿名的落点规则，不多占窗口外地址）。
//   没开文件后备返回 MAP_FAILED（调用方照旧匿名）。这些段还页时不打洞（s2a_guest_zero 只认窗口），换匿名占位：语义同样是零，只是那几页回到匿名记账
static pthread_mutex_t g_gextra_mu = PTHREAD_MUTEX_INITIALIZER; static uint64_t g_gextra;
// 文件往后接长 len，返回这段的偏移；失败返回 UINT64_MAX
static uint64_t gextra_take(uint64_t len) {
    pthread_mutex_lock(&g_gextra_mu); uint64_t off = g_size + g_gextra; int ok = !ftruncate(g_gfd, (off_t)(off + len)); if (ok) g_gextra += len; pthread_mutex_unlock(&g_gextra_mu);
    return ok ? off : UINT64_MAX;
}
// 映射失败时退回刚接长的那段（审计 P2-264）：还在文件末尾才退、截回去；后面已有别人接上就留成空洞（稀疏文件，不占盘）
static void gextra_undo(uint64_t off, uint64_t len) {
    pthread_mutex_lock(&g_gextra_mu);
    if (g_size + g_gextra == off + len && !ftruncate(g_gfd, (off_t)off)) g_gextra -= len;
    pthread_mutex_unlock(&g_gextra_mu);
}
void *s2a_guest_map_any(uint64_t len) {
    if (g_gfd < 0 || !len) return MAP_FAILED;
    uint64_t off = gextra_take(len);
    if (off == UINT64_MAX) return MAP_FAILED;
    void *p = mmap(NULL, len, PROT_NONE, MAP_SHARED, g_gfd, (off_t)off);
    if (p == MAP_FAILED) gextra_undo(off, len);
    return p;
}
// 线性远端影子（far.c，#419）的一块也要文件后备：文件往后接长，按新偏移映射到 far.c 自己预留的线性影子区里的固定地址（那段是 far.c 占的不可访问预留，
//   MAP_FIXED 只盖它自己的地址）。没开文件后备回 1（调用方用预留里的匿名页）；成功回 0，失败回 -1
int s2a_guest_map_fixed(uint64_t a, uint64_t len) {
    if (g_gfd < 0) return 1;
    if (!len) return 0;
    uint64_t off = gextra_take(len);
    if (off == UINT64_MAX) return -1;
    if (mmap((void *)(uintptr_t)a, len, PROT_NONE, MAP_FIXED | MAP_SHARED, g_gfd, (off_t)off) == (void *)(uintptr_t)a) return 0;
    gextra_undo(off, len);
    return -1;
}
// [a, a + n) 在文件后备的窗口里：打洞（还文件块，再读是 0）并按原偏移重新映射成不可访问，返回 1；不在 / 没开文件后备返回 0（调用方照旧换匿名占位）
int s2a_guest_zero(uint64_t a, uint64_t n) {
    if (g_gfd < 0 || a < g_base || a + n > g_base + g_size || !n) return 0;
    fpunchhole_t ph; memset(&ph, 0, sizeof ph); ph.fp_offset = (off_t)(a - g_base); ph.fp_length = (off_t)n;
    if (fcntl(g_gfd, F_PUNCHHOLE, &ph)) { static int once; if (!once++) LOG("【红】客体内存文件后备：打洞失败（errno=%d，%#llx +%#llx），这段改回匿名占位", errno, (unsigned long long)a, (unsigned long long)n); return 0; }
    if (mmap((void *)(uintptr_t)a, n, PROT_NONE, MAP_FIXED | MAP_SHARED, g_gfd, (off_t)(a - g_base)) != (void *)(uintptr_t)a) return 0;
    return 1;
}
// [a, a + n) 全在文件后备的窗口里返回 1（没开 / 不在 / n 为 0 返回 0）。svc_mem.c 的懒清零（#258）按它判走不走
int s2a_guest_in_file(uint64_t a, uint64_t n) { return g_gfd >= 0 && n && a >= g_base && a + n <= g_base + g_size; }
int s2a_window_ok(void) { return g_ok; }
void s2a_window_get(uint64_t *base, uint64_t *size) { *base = g_base; *size = g_size; }
int s2a_window_session_reset(void) {
    if (!g_ok || !g_size) return -1;
    // 只换客体区；尾部分配器中仍可能有宿主/运行时拥有的映射，不能清空。
    if (s2a_guest_zero(g_base, g_size)) return 0;   // 文件后备：整段打洞并重新映射成不可访问
    void *p = mmap((void *)g_base, g_size, PROT_NONE, MAP_FIXED | MAP_PRIVATE | MAP_ANON, -1, 0);
    if (p == (void *)g_base) return 0;
    // iOS 上整段盖回 EACCES（11-02 测试设备2 塞尔达设置页切 60 帧「立刻重启」，诊断 251febb68 读数：盖不掉的 6 段全是权限 r-x / 最大 r-x、私有）：
    //   那是装载器从 App 签名 __TEXT 共享进窗口的客体代码页（loader.c iOS map_image，vm_remap copy=FALSE），系统不许覆盖或解除；外置镜像包的文件代码页同样（11-03 实测）。逐段盖：
    //   代码页（当前权限含执行，或最大权限有执行没写）原样留着——重启后同一款同一落点的代码页内容不变，装载器认出来直接复用（loader.c code_same，同 nn::ro 重装 remap_writable）；
    //   其余段盖成不可访问，盖不掉才算失败
    int e0 = errno; uint64_t end = g_base + g_size; vm_address_t a = g_base; int bad = 0, kept = 0; uint64_t kept_b = 0;
    while (a < end) {
        vm_address_t r = a; vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        if (vm_region_recurse_64(mach_task_self(), &r, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) != KERN_SUCCESS || r >= end) break;
        uint64_t n = r + sz > end ? end - r : sz;
        if (s2a_prot_is_code(info.protection, info.max_protection)) { kept++; kept_b += n; a = r + sz; continue; }   // 代码页判据见 imgpack.h（外置镜像包的文件页最大权限原是 rwx，映射时压回 r-x）
        void *q = s2a_guest_zero(r, n) ? (void *)r : mmap((void *)r, n, PROT_NONE, MAP_FIXED | MAP_PRIVATE | MAP_ANON, -1, 0);
        if (q != (void *)r && bad++ < 32)
            LOG("【红】重建客体窗口：盖不掉 %#llx +%#llx（errno=%d）：权限 %d / 最大 %d、标签 %u、共享方式 %u、子映射深 %u", (unsigned long long)r, (unsigned long long)n, errno,
                info.protection, info.max_protection, info.user_tag, info.share_mode, depth);
        a = r + sz;
    }
    LOG("%s重建客体窗口：整段覆盖 errno=%d，逐段盖完；签名代码页 %d 段 %llu KB 原样留着给新局复用，盖不掉 %d 段", bad ? "【红】" : "", e0, kept, (unsigned long long)(kept_b >> 10), bad);
    return bad ? -1 : 0;
}
// 窗口之外还能给宿主大映射（Metal 大缓冲等）的地址：收尾还回的那段 + 窗口所在空洞其余部分（到 2^39 的空洞）。低区账按它判设不设限（lowva.c）
static void holes_in(uint64_t lo, uint64_t hi, uint64_t *total, uint64_t *largest);
uint64_t s2a_window_spare(void) { uint64_t t = 0, l = 0; if (!g_ok) return 0; holes_in(g_base + g_res, 1ull << 39, &t, &l); return (g_res - g_size) + t; }

// [lo, hi) 里的空洞用不可访问的保留占住（只占空洞，不盖已有映射：不带 MAP_FIXED 按提示放，落点不对就退还记 *bad）；累计段数 / 字节。
//   不用 mach_vm.h：iOS SDK 里它不可用（进 App 的代码按 iOS SDK 编），真机上也要占（S2A_VA_IOS26 在 iOS 27 测试设备上复现 iOS 26 的宿主地址预算）
static void fence_holes(uint64_t lo, uint64_t hi, uint64_t *tot, int *n, int *bad) {
    vm_address_t a = lo;
    while (a < hi) {
        vm_address_t r = a; vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        int ok = vm_region_recurse_64(mach_task_self(), &r, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) == KERN_SUCCESS;
        uint64_t he = ok && r < hi ? r : hi;   // 空洞 [a, he)
        if (he > a) {
            void *f = mmap((void *)a, he - a, PROT_NONE, MAP_PRIVATE | MAP_ANON, VM_MAKE_TAG(VM_MEMORY_GUARD), 0);
            if (f == (void *)a) { *tot += he - a; (*n)++; } else { if (f != MAP_FAILED) munmap(f, he - a); (*bad)++; }
        }
        if (!ok || r >= hi) break;
        a = r + sz;
    }
}
#if TARGET_OS_OSX
#include <mach/mach_vm.h>
// Mac 复现 iPhone 地址约束（缺省开，S2A_IPHONE_VA=0 关；10-20 八方2 / 巫师3 iPhone 地址耗尽，Mac 上从没复现过）：
// iPhone 进程里窗口外能用的只有 4 GB 起到 dyld 共享缓存区（0x1_8000_0000）之间约 2 GB——其上 [0x1_8000_0000, 0xF_C000_0000) 是共享缓存区（标签 32），
// [0xF_C000_0000, 0x70_0000_0000) 是内核保护区（标签 31），窗口尾之上没有地址。Mac 上把这些段里的空洞用不可访问、不可改权限的保留占住（只占空洞，不盖已有映射），
// 让 GC / Metal / 线程栈 / 暂存缓冲在 Mac 上也只能落进同样的低区，地址预算问题在 Mac 局上就现形
static void iphone_va_fence(void) {
    const char *e = getenv("S2A_IPHONE_VA"); if (e && *e == '0') { LOG("iPhone 地址约束：关（S2A_IPHONE_VA=0）"); return; }
    // Mac 的 malloc（xzm）大块从自己的地址提示往上找、不落低区（iPhone 上落低区）：高区只留 MALLOC_ROOM 给它，低区扣减仍由既有诊断变量指定。
    // 远端起点 = 窗口末 ≤ 2^39、跨度 ≤ S2A_FAR_SPAN；房间必须在这个上界之外，否则 far_set 会把它收回成 PROT_NONE。
    enum { MALLOC_ROOM_MB = 512 };
    const uint64_t room = (uint64_t)MALLOC_ROOM_MB << 20;
    const uint64_t room_base = (1ull << 39) + S2A_FAR_SPAN;
    struct { uint64_t lo, hi; } seg[] = {{0x180000000ull, g_keep_lo ? g_keep_lo : g_base}, {1ull << 39, room_base}, {room_base + room, MACH_VM_MAX_ADDRESS}};   // 窗口下方与 2^39 以下其余空洞照旧；高区只开放一个 room 大小的房间
    uint64_t tot = 0; int n = 0, bad = 0;
    for (size_t s = 0; s < sizeof seg / sizeof seg[0]; s++) fence_holes(seg[s].lo, seg[s].hi, &tot, &n, &bad);
    const char *dv = getenv("S2A_IPHONE_VA_DEDUCT_MB"); uint64_t ded = (uint64_t)(dv ? atoi(dv) : 0) << 20;
    void *dd = ded ? mmap(NULL, ded, PROT_NONE, MAP_PRIVATE | MAP_ANON, VM_MAKE_TAG(VM_MEMORY_GUARD), 0) : NULL;   // 低区对等扣减（落低区第一个够大的空洞）
    if (ded && (dd == MAP_FAILED || (uint64_t)dd >= 0x180000000ull)) { LOG("【红】iPhone 地址约束：低区对等扣减 %d MB 没落进低区（%p）", MALLOC_ROOM_MB, dd); bad++; }
    uint64_t ht, hl; s2a_low_holes(&ht, &hl);
    LOG("iPhone 地址约束：开（Mac 复现）——占住共享缓存区 / 保护区 / 窗口尾之上的空洞 %d 段 %llu GB%s；远端上界之外 %#llx 留 %d MB 给 Mac malloc、低区对等扣减 %llu MB；低区剩空洞合计 %llu MB、最大一块 %llu MB",
        n, (unsigned long long)(tot >> 30), bad ? "（有段没占上，见下）" : "", (unsigned long long)room_base, MALLOC_ROOM_MB, (unsigned long long)(ded >> 20), (unsigned long long)(ht >> 20), (unsigned long long)(hl >> 20));
    if (bad) LOG("【红】iPhone 地址约束：%d 段空洞没占上", bad);
}
#endif

static int g_probe_n = -1;   // 最近一次窗口探测数到的别人映射段数（-1 = 没探测过）
// 放行护栏（libs2a_vaguard.dylib，弱链接）：占窗口之前它拒掉了 macOS 27 malloc 落进窗口的大块保留；占过了（成或不成）或不占窗口（S2A_VAWIN_NORESERVE=1）都要放行，
//   否则之后要观察的窗口映射会一直被拒（10-24 #100 作者指出 NORESERVE 提前返回漏了这一步）
static void vaguard_release(void) {
#if TARGET_OS_OSX
    //   按名字取（dlsym）：单测 / 别的构建只链 vawin.c、不链护栏库也能链接
    { void (*vg_open)(void) = (void (*)(void))dlsym(RTLD_DEFAULT, "s2a_vaguard_open");
      unsigned (*vg_refused)(unsigned long long *) = (unsigned (*)(unsigned long long *))dlsym(RTLD_DEFAULT, "s2a_vaguard_refused");
      if (vg_open && vg_refused) { unsigned long long rb = 0; unsigned rn = vg_refused(&rb); vg_open();
          if (rn) LOG("地址窗口护栏：占窗口前拒了 %u 次落进窗口的固定地址映射，共 %llu MB（macOS 27 malloc 的大块保留，它会改走不保留的路径）", rn, rb >> 20); }
      else LOG("地址窗口护栏：没载入 libs2a_vaguard.dylib（应在可执行文件同目录）；macOS 27 上窗口可能被 malloc 占走"); }
#endif
}
int s2a_process_prewarmed(void) {
#if TARGET_OS_IPHONE
    const char *e = getenv("ActivePrewarm"); return e && !strcmp(e, "1");
#else
    return 0;
#endif
}
// 窗口 = 本款申请的地址跨度（10-24 维护者：「按照游戏申请的内存地址宽度自动判断……游戏申请多少就打进去多少」）：
//   跨度由包里的 main.npdm 定（地址空间类型 + SystemResourceSize → s2a_layout_need：系统资源为 0 的款 32 GB，非 0 的约 63.25 GB），
//   再加窗口尾部统一分配的 TL_TAKE（能放下才加），在系统给的 2^39 以下空洞里取一块：不带 MAP_FIXED、核对落点，不盖别人的映射；起点 1 GB 对齐。
//   放得下的空洞里取地址最高的（低区留给 GC 段与 Metal 小缓冲；iOS 27 / macOS 上就是 [0x70, 0x80) 那块）。
//   客体地址 = 宿主地址（恒等映射），布局按窗口基址算（layout.c），改写产物不含窗口地址，所以放哪都行；顶端 ≤ 2^39（HIPC 缓冲描述符只编得下 39 位，地址空间.md C7）。
//   以前写死 0x7000000000 + 64 GB：iPadOS 26.6.1（地址上限 0xfc0000000、最大连续块约 51 GB，#61）上一款都起不了，见坑记录
//   S2A_WIN_NEED_MB：跨度直接给（单测 / 不带 NPDM 的工具用）；读不到 NPDM 又没给 → 不占窗口、报红
#define TL_TAKE (2ull << 30)   // 窗口尾部统一分配接管这么多（见 s2a_window_trim）
#define TL_SMALL (256ull << 20)
#define MIN_WIN (2ull << 30)
#define HOST_BELOW (3ull << 30)   // 放不下标准布局时窗口下方留给宿主的地址（11-06：1 GB → 3 GB。iOS 上宿主可用地址 = 低区约 1.8 GB + 这一段；时之笛 Switch 2 版宿主峰值 1.7–2.1 GB，1 GB 时低区碰底在上屏路径崩。时之笛游戏最高只碰到窗口 +17.6 GB、异度3 碰到 +60.6 GB，3 GB 两者都装得下；≥3712 MB 会让 GC 上限改选分堆档吃掉收益）   // 窗口最少要这么多（模块 + 栈 + 堆前段放得下与否由布局判，layout.c）   // 窗口顶到空洞末尾时只接管这么多（九款尾部峰值 ≤ 202 MB，见 s2a_window_trim）
// 放不下标准布局时窗口下方留给宿主多少（#783，纯函数，t_vawin_learned 测）：没学到跨度（learned = 0）→ HOST_BELOW；学到了 → 窗口只给
//   learned × 1.25 + 2 GiB（1 GiB 向上取整，游戏后面还会碰得更高、留余量），这块空洞里其余都给宿主，至少 HOST_BELOW。
//   iPad Pro M2 iPadOS 27.2.1：64 GB 空洞放不下 76 GB 标准布局，固定留 3 GiB，宿主低区开局 3.4 GB、玩 10–40 分钟 mmap 碰底闪退；那款整局只碰到 16.4 GB
uint64_t s2a_window_host_below(uint64_t fit, uint64_t learned) {
    const uint64_t G = 1ull << 30;
    if (!learned) return HOST_BELOW;
    uint64_t win = (learned + learned / 4 + 2 * G + G - 1) & ~(G - 1);
    if (win < MIN_WIN) win = MIN_WIN;
    uint64_t host = fit > win ? (fit - win) & ~(G - 1) : 0;
    return host > HOST_BELOW ? host : HOST_BELOW;
}
// 起局当场自愈（v0.3.4）：窗口按学到的跨度收窄后布局放不下（svc_mem.c layout_prepare 判 -2 那一刻）——删掉记录，窗口往下放宽回缺省给法（下方只留 HOST_BELOW 给宿主），
//   布局重算、本局照常起。原先只删记录、本局照样失败，玩家第二次打开才好（v0.3.3 已记下坏记录的玩家装新版后头一次仍失败）。
//   放宽的那段 [新起点, 窗口底) 起局后可能已被宿主映射占了一部分（lp_map 带提示往这里放直连库段等）：新起点取「已占映射末端（1 GiB 向上取整）」与「留宿主底 + HOST_BELOW」的大者，
//   不盖别人；放不宽（新起点到不了窗口底以下）回 0，照旧失败（记录已删，下一局按缺省）。纯函数部分 s2a_window_widen_lo，t_vawin_learned 测；端到端 t_vawin_widen 测
uint64_t s2a_window_widen_lo(uint64_t keep_lo, uint64_t base, uint64_t used_end) {
    const uint64_t G = 1ull << 30;
    uint64_t lo = keep_lo + HOST_BELOW, u = (used_end + G - 1) & ~(G - 1);
    if (u > lo) lo = u;
    return lo < base ? lo : 0;
}
int s2a_window_span_widen(void) {
    if (!g_ok || !g_span_learned || !g_keep_lo) return 0;   // 没按学到的跨度收窄：不是这条路径的问题
    s2a_window_span_forget();
    uint64_t learned = g_span_learned; g_span_learned = 0;
    if (g_gextra) { LOG("【红】地址窗口：想当场放宽，但文件后备已往窗口外接长（%llu MB），不放宽", (unsigned long long)(g_gextra >> 20)); return 0; }
    for (vm_address_t a = (vm_address_t)g_base, end = (vm_address_t)(g_base + g_size); a < end; ) {   // 窗口还原封不动（布局前，整段 PROT_NONE）才放宽：要整段重映射
        vm_address_t ra = a; vm_size_t sz = 0; vm_region_basic_info_data_64_t bi; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        if (vm_region_64(mach_task_self(), &ra, &sz, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&bi, &cnt, &obj) != KERN_SUCCESS || ra >= end) break;
        if (bi.protection != VM_PROT_NONE) { LOG("【红】地址窗口：想当场放宽，但窗口里已有放开过的映射（%#llx +%llu MB），不放宽", (unsigned long long)ra, (unsigned long long)(sz >> 20)); return 0; }
        a = ra + sz;
    }
    uint64_t used = g_keep_lo;
    for (vm_address_t a = (vm_address_t)g_keep_lo;; ) {   // [留宿主底, 窗口底) 里已占映射的最高末端
        vm_size_t sz = 0; vm_region_basic_info_data_64_t bi; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        if (vm_region_64(mach_task_self(), &a, &sz, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&bi, &cnt, &obj) != KERN_SUCCESS || a >= g_base) break;
        if (a + sz > used) used = a + sz;
        a += sz;
    }
    uint64_t lo = s2a_window_widen_lo(g_keep_lo, g_base, used), end = g_base + g_size;
    if (!lo) { LOG("【红】地址窗口：想当场放宽，但窗口下方 %#llx 起已被宿主映射占到 %#llx，放不宽", (unsigned long long)g_keep_lo, (unsigned long long)used); return 0; }
    void *p = mmap((void *)lo, g_base - lo, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);   // 不带 MAP_FIXED：核对落点，不盖别人
    if (p != (void *)lo) { if (p != MAP_FAILED) munmap(p, g_base - lo);
        LOG("【红】地址窗口：想当场放宽，[%#llx, %#llx) 占不到（%s），不放宽", (unsigned long long)lo, (unsigned long long)g_base, p == MAP_FAILED ? "失败" : "落在别处"); return 0; }
    if (g_gfd >= 0) {   // 文件后备：整段（含放宽的那段）重映射成文件，偏移 0 起（窗口还没有内容）
        void *q = ftruncate(g_gfd, (off_t)(end - lo)) ? MAP_FAILED : mmap((void *)lo, end - lo, PROT_NONE, MAP_FIXED | MAP_SHARED, g_gfd, 0);
        if (q != (void *)lo) { int er = errno; mmap((void *)lo, end - lo, PROT_NONE, MAP_FIXED | MAP_PRIVATE | MAP_ANON, -1, 0); close(g_gfd); g_gfd = -1;
            LOG("【红】客体内存文件后备：窗口放宽后重映射成文件失败（errno=%d），照旧用匿名内存", er); } }
    LOG("【黄】地址窗口：按学到的跨度 %llu MB 收窄后放不下本款布局——当场放宽：%#llx +%llu MB → %#llx +%llu MB（下方留宿主 %llu MB），本局照常起",
        (unsigned long long)(learned >> 20), (unsigned long long)g_base, (unsigned long long)(g_size >> 20), (unsigned long long)lo, (unsigned long long)((end - lo) >> 20), (unsigned long long)((lo - g_keep_lo) >> 20));
    g_base = lo; g_size = g_res = end - lo;
    { void (*gc)(void) = (void (*)(void))dlsym(RTLD_DEFAULT, "s2a_gc_limit_reapply"); if (gc) gc(); }   // GC 上限是按放宽前的低区选的（gclimit.c），按现在的重选
    return 1;
}
static uint64_t g_need, g_fit;   // 本款要的跨度；2^39 以下最大能放的一块（1 GB 对齐后）——自检提示「本款需要 N GB，本机最多 M GB」用
void s2a_window_need(uint64_t *need, uint64_t *fit) { *need = g_need; *fit = g_fit; }
static char g_npdm[1100];   // 本款 main.npdm 路径（找不到可执行文件目录 / 模块目录时为空）：跨度算不出时按它说清原因
static int g_ctr, g_ctr_astype = -1;   // 多款容器构造期（launchctx.c ③）：g_ctr = 1；g_ctr_astype = 包内各款一致的地址空间类型（不一致 / 读不到 = -1）
static int astype_of(const char *npdm) {   // main.npdm 的地址空间类型（同 svc_mem.c npdm_read：+0x0C 位 1–3，只读头 16 字节）；读不到 / 不是 META 为 -1
    uint8_t h[0x10]; int fd = npdm && npdm[0] ? open(npdm, O_RDONLY) : -1; ssize_t n = fd >= 0 ? read(fd, h, sizeof h) : -1; if (fd >= 0) close(fd);
    return n == (ssize_t)sizeof h && !memcmp(h, "META", 4) ? (h[0x0C] >> 1) & 7 : -1;
}
// 一个模块目录（单款 = 启动上下文的模块目录 / Mac argv[1]；多款容器 = <App>/Games/<游戏号>）要的跨度：main.npdm + 模块段（svc_mem.c s2a_npdm_window_need），
//   多程序合集（s2a_programs.h）取各序号最大值——窗口每进程只占一次，ExecuteProgram 切到别的序号走进程内重启、不重占。
//   哪一支读不到（0 = 不知道要多大）就整体按 0 报，与单程序读不到同一口径；读不到的那份 main.npdm 记进 g_npdm（红行按它说原因）
static uint64_t need_dir(const char *dir) {
    snprintf(g_npdm, sizeof g_npdm, "%s/main.npdm", dir);
    uint64_t (*f)(const char *) = (uint64_t (*)(const char *))dlsym(RTLD_DEFAULT, "s2a_npdm_window_need");
    if (!f) return 0;
    uint64_t need = f(g_npdm), need0 = need;
    int (*count)(const char *) = (int (*)(const char *))dlsym(RTLD_DEFAULT, "s2a_programs_count");
    int (*pdir)(const char *, int, char *, size_t) = (int (*)(const char *, int, char *, size_t))dlsym(RTLD_DEFAULT, "s2a_programs_dir");
    void (*img)(int) = (void (*)(int))dlsym(RTLD_DEFAULT, "s2a_loader_image_program");   // iOS 镜像包里序号 n 的模块带前缀：算跨度时按该序号查
    int np = count && pdir ? count(dir) : 1;
    for (int i = 1; i < np && need; i++) {
        char d[1100], np_path[1200];
        if (pdir(dir, i, d, sizeof d)) { need = 0; break; }
        snprintf(np_path, sizeof np_path, "%s/main.npdm", d);
        if (img) img(i);
        uint64_t ni = f(np_path);
        if (img) img(0);
        LOG("地址窗口：多程序合集序号 %d 要 %llu MB（序号 0 要 %llu MB）", i, (unsigned long long)(ni >> 20), (unsigned long long)(need0 >> 20));
        if (!ni) { snprintf(g_npdm, sizeof g_npdm, "%s", np_path); need = 0; break; }
        if (ni > need) need = ni;
    }
    return need;
}
// 多款容器（launchctx.c ③，启动器线 11-07）：窗口必须在构造期、UIKit 之前占好，那时玩家还没选游戏——对 <App>/Games/ 下每一款按单款同一个 need_dir 算，取最大值。
//   iOS 上各款模块的非 FAR 补丁区长度取该款镜像包 Frameworks/S2AImages-<游戏号>.dylib 的偏移表（loader.c s2a_loader_span_images：只读表、不注册签名、不冻结上下文），
//   Mac 取模块目录的 <名>.patched.bin（同单款）。各款 NPDM 地址空间类型须一致（不同类型的窗口上界不同，装不进同一个窗口，组装侧 pack/ship_ext.py 同一判据先拒）：
//   不一致 / 任何一款读不到或算不出 / Games/ 下没有游戏 → 0（报红、不占窗口，自检页拦）。构造期逐款读：main.npdm 头 16 字节（类型）+ NPDM 头 0x80、ACID +0x300 处 4 字节、
//   ACI0 0x38（svc_mem.c npdm_read 不写本局状态的读法）+ 各模块 <名>.fixups.tsv（只有表头几行，实测约 240 字节）+ 镜像包头与偏移表（32 + load commands + 16 + 88 × 模块数）。
//   应用池（Switch 2 9 GiB）在每款算完后放回读之前的值：别款的池不带进下一款的算法，也不带进玩家选的那款（起局时 layout_prepare 按本款 NPDM 重新设）
uint64_t s2a_window_container_need(const char *bundle) {
    g_ctr_astype = -1; g_ctr_pool = 0;
    char gd[1100]; snprintf(gd, sizeof gd, "%s/Games", bundle);
    DIR *d = opendir(gd);
    if (!d) { LOG("【红】地址窗口：多款容器读不了 %s（errno %d），不知道要多大，不占窗口", gd, errno); return 0; }
    int (*span)(const char *, char *, size_t) = (int (*)(const char *, char *, size_t))dlsym(RTLD_DEFAULT, "s2a_loader_span_images");
    uint64_t (*poolf)(void) = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "s2a_app_pool");
    void (*pools)(uint64_t) = (void (*)(uint64_t))dlsym(RTLD_DEFAULT, "s2a_app_pool_set");
    uint64_t (*native_pool)(void) = (uint64_t (*)(void))dlsym(RTLD_DEFAULT, "s2a_app_pool_native");
    uint64_t pool0 = native_pool ? native_pool() : poolf ? poolf() : 0, top = 0, span_max = 0; int n = 0, ast = -1, ok = 1, span_unknown = 0; char first[256] = ""; struct dirent *e;
    while (ok && (e = readdir(d))) {
        char dir[1400], img[1400], why[400] = ""; struct stat st;
        if (e->d_name[0] == '.' || strlen(e->d_name) > 200) continue;
        snprintf(dir, sizeof dir, "%s/%s", gd, e->d_name);
        if (stat(dir, &st) || !S_ISDIR(st.st_mode)) continue;
        snprintf(g_npdm, sizeof g_npdm, "%s/main.npdm", dir);
        int t = astype_of(g_npdm);
        if (t < 0) { LOG("【红】地址窗口：多款容器里 %s 读不到 main.npdm（或不是 META），不知道要多大，不占窗口", e->d_name); ok = 0; break; }
        if (ast >= 0 && t != ast) {
            LOG("【红】地址窗口：多款容器里各款 NPDM 地址空间类型不一致（%s 类型 %d（%s）、%s 类型 %d（%s）），装不进同一个窗口，不占窗口",
                first, ast, s2a_as_type_bits((uint32_t)ast), e->d_name, t, s2a_as_type_bits((uint32_t)t));
            ast = -1; ok = 0; break; }
        if (ast < 0) { ast = t; snprintf(first, sizeof first, "%s", e->d_name); }
        snprintf(img, sizeof img, "%s/Frameworks/S2AImages-%s.dylib", bundle, e->d_name);
        if (span && span(img, why, sizeof why)) { LOG("【红】地址窗口：多款容器里 %s 的镜像包读不了偏移表：%s，不占窗口", e->d_name, why); ok = 0; break; }
        uint64_t ni = need_dir(dir);
        if (span) span(NULL, NULL, 0);
        { uint64_t pg = poolf ? poolf() : 0; if (pg > g_ctr_pool) g_ctr_pool = pg; }
        if (pools && pool0) pools(pool0);
        if (!ni) { LOG("【红】地址窗口：多款容器里 %s 的跨度算不出（类型 %d（%s）；%s 读不到、模块段读不到或类型不支持），不占窗口", e->d_name, t, s2a_as_type_bits((uint32_t)t), g_npdm); ok = 0; break; }
        LOG("地址窗口：多款容器 %s 要 %llu MB（地址空间类型 %d）", e->d_name, (unsigned long long)(ni >> 20), t);
        { uint64_t sl = s2a_window_span_seen(strtoull(e->d_name, NULL, 16)); if (!sl) span_unknown = 1; else if (sl > span_max) span_max = sl; }
        if (ni > top) top = ni;
        n++;
    }
    closedir(d);
    if (ok && !n) LOG("【红】地址窗口：多款容器 %s 下没有游戏，不占窗口", gd);
    g_ctr_astype = ast;
    if (!ok || !n) return 0;
    g_span_learned = span_unknown ? 0 : span_max;
    g_npdm[0] = 0;
    LOG("地址窗口：多款容器 %d 款取最大 %llu MB（地址空间类型 %d）", n, (unsigned long long)(top >> 20), ast);
    return top;
}
static uint64_t need_from_npdm(void) {
    const char *e = getenv("S2A_WIN_NEED_MB");
    if (e && atoll(e) > 0) { char sp[1024]; if (getenv("S2A_WIN_SPAN_PEAK") && span_path(sp, sizeof sp, 0)) g_span_learned = read_u64(sp); return (uint64_t)atoll(e) << 20; }   // 单测：跨度与学到的跨度都直接给
    char dir[1024] = "";
#if TARGET_OS_IPHONE
    // iOS：main.npdm 在启动上下文的模块目录（单款兼容 = 可执行文件同目录，同改造前）
    // 多款容器（launchctx.c ③）：构造期玩家还没选游戏、上下文不冻结——对包内每一款算，取最大（s2a_window_container_need）
    if (s2a_launch_ctx_container()) { g_ctr = 1; return s2a_window_container_need(s2a_launch_ctx_bundle_dir()); }
    const s2a_launch_ctx *lc = s2a_launch_ctx_get();
    if (!lc) { LOG("【红】地址窗口：启动上下文不可用（%s）", s2a_launch_ctx_error()); return 0; }
    strlcpy(dir, lc->module_dir, sizeof dir);
#else
    { int ac = *_NSGetArgc(); char **av = *_NSGetArgv(); if (ac < 2) return 0; strlcpy(dir, av[1], sizeof dir); }   // Mac：s2arm-host <模块目录>
#endif
    { uint64_t (*pf)(const char *) = (uint64_t (*)(const char *))dlsym(RTLD_DEFAULT, "s2a_npdm_pid"); char np[1100]; snprintf(np, sizeof np, "%s/main.npdm", dir);
      g_ctor_pid = pf ? pf(np) : 0; }   // 单款：文件后备按它找本款实测峰值 / 死亡标记（mem_peak_path）
    g_span_learned = s2a_window_span_seen(g_ctor_pid);
    return need_dir(dir);
}
// 跨度为 0 的红行按事实分（11-05 Minecraft: Story Mode 的 NPDM 是地址空间类型 1，被报成「读不到 main.npdm」）：
//   读不到 / 不是 META → 读不到；读得到、类型不是 3 → 报类型与位宽（布局只支持 39 位，layout.c）；类型 3 仍为 0 → 模块段算不出
static int g_astype = -1;   // 跨度为 0 时读到的 NPDM 地址空间类型（-1 = 没读到）：自检页按它说「暂不支持 36 位地址空间」还是「资源不完整」（selfcheck.c）
int s2a_window_astype(void) { return g_astype; }
static int npdm_astype(void) { return g_ctr ? g_ctr_astype : astype_of(g_npdm); }   // 本款（多款容器 = 包内各款一致的）地址空间类型
static void need_zero_red(void) {
    int t = npdm_astype(); g_astype = t;
    if (g_ctr) return;   // 多款容器：s2a_window_container_need 已按款报过红
    if (t < 0) { LOG("【红】地址窗口：读不到本款 main.npdm（可执行文件同目录 / 模块目录），不知道要多大，不占窗口"); return; }
    if (!s2a_as_type_top((uint32_t)t)) LOG("【红】地址窗口：NPDM 地址空间类型 %d（%s）暂不支持（布局只支持类型 1 = 36 位、3 = 39 位），不占窗口", t, s2a_as_type_bits((uint32_t)t));
    else LOG("【红】地址窗口：main.npdm 是类型 %d（%s），但算不出本款跨度（模块段读不到或太大），不占窗口", t, s2a_as_type_bits((uint32_t)t));
}
// 2^39（或地址上限）以下的空洞，按 1 GB 对齐收成可用段；挑能放下 want 的地址最高的一段（都放不下 → *sz = 0），*fit / *fit_at 记最大一段（同大取地址高的），
//   *low_at 记放得下 low_want 的地址最低的一段（low_want = 0 不找）
static void pick_hole(uint64_t hi, uint64_t want, uint64_t *at, uint64_t *sz, uint64_t *fit, uint64_t *fit_at, uint64_t low_want, uint64_t *low_at) {
    const uint64_t G = 1ull << 30; uint64_t prev = 0x100000000ull; vm_address_t a = prev; *at = *sz = *fit = *fit_at = *low_at = 0;
    for (;;) {
        vm_size_t rs = 0; vm_region_basic_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        int ok = vm_region_64(mach_task_self(), &a, &rs, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &cnt, &obj) == KERN_SUCCESS;
        uint64_t ge = ok && a < hi ? a : hi, b = (prev + G - 1) & ~(G - 1), e = ge & ~(G - 1);
        if (ge > prev && e > b) { if (e - b >= *fit) { *fit = e - b; *fit_at = b; } if (e - b >= want && b >= *at) { *at = b; *sz = e - b; } if (low_want && e - b >= low_want && !*low_at) *low_at = b; }
        if (!ok || a >= hi) break;
        if (a + rs > prev) prev = a + rs;
        a += rs;
    }
}
static void cmd_arena_reserve(void);
static void vawin_reserve(void) {
    const char *e = getenv("S2A_VAWIN_NORESERVE"); g_noreserve = e && *e == '1';
    if (g_noreserve) { s2a_window_probe("构造函数（不占窗口）"); vaguard_release(); return; }
    g_need = need_from_npdm();
    {   // 只读日志（11-03 大乱斗首局定因 / 宿主预留按实测补足的依据）：构造函数时低区 [4 GB, 6 GB) 空余，与主可执行文件映射大小（各段 vmsize，不含 __PAGEZERO）
        uint64_t lt = 0, ll = 0, ex = 0; holes_in(0x100000000ull, 0x180000000ull, &lt, &ll);
        const struct mach_header_64 *mh = (const struct mach_header_64 *)_NSGetMachExecuteHeader();   // 主可执行文件（crt_externs.h；构造函数时刻 dyld 映像表的序号 0 不一定是它）
        const struct load_command *lc = mh ? (const struct load_command *)(mh + 1) : NULL;
        for (uint32_t i = 0; lc && i < mh->ncmds; i++, lc = (const struct load_command *)((const char *)lc + lc->cmdsize))
            if (lc->cmd == LC_SEGMENT_64 && strcmp(((const struct segment_command_64 *)lc)->segname, "__PAGEZERO")) ex += ((const struct segment_command_64 *)lc)->vmsize;
        LOG("地址窗口前：低区 [4 GB, 6 GB) 空余合计 %llu MB、最大一块 %llu MB；主可执行文件映射 %llu MB", (unsigned long long)(lt >> 20), (unsigned long long)(ll >> 20), (unsigned long long)(ex >> 20)); }
    if (!g_need) { vaguard_release(); need_zero_red(); return; }
    // 窗口顶不超过本款地址空间上界（as_type.h s2a_as_type_top）：36 位款（老 SDK 的 HIPC 描述符只编 36 位地址）取 2^36 以下的空洞，39 位款 2^39；
    //   S2A_WIN_NEED_MB 直接给跨度（没有 NPDM）按 39 位
    int ast = npdm_astype(); uint64_t astop = ast >= 0 && s2a_as_type_top((uint32_t)ast) ? s2a_as_type_top((uint32_t)ast) : 1ull << 39;
    const char *hb = astop == 1ull << 36 ? "2^36" : "2^39";
    uint64_t top = s2a_va_top(), hi = astop, at, sz; if (top && top < hi) hi = top;
    // S2A_VA_CAP_MB（Mac 诊断）：复现小地址机型（iOS 26 不开扩展寻址约 17.4 GiB）——取地址最低、放得下这么大的空洞当「本机最大一块」，
    //   窗口照下面「放不下」的取法占，之后到 2^39 的空洞占死：别名区伸出段落进 Mac 的 GPU 保留区（不可访问），同设备上伸出段越过地址上限
    const char *ce = getenv("S2A_VA_CAP_MB"); uint64_t cap = ce && atoll(ce) > 0 ? (uint64_t)atoll(ce) << 20 : 0, fat, lat, want;
    pick_hole(hi, g_need, &at, &sz, &g_fit, &fat, cap, &lat);
    if (cap) { if (lat) { fat = lat; g_fit = cap; } else g_fit = 0; sz = 0; }
    // S2A_VA_IOS26=1（Mac 诊断 / iOS 27 测试设备复现）：模拟 iOS 26 大地址档——最大空洞 [0x300000000, 0xfc0000000)（共享区末到大地址档上限，52224 MiB = #61 读数），其上越过地址上限。
    //   Mac 上取同位置的 [0x3_0000_0000, 0xF_C000_0000)（护栏库拦住 xzm 的 24 GB 保留后构造函数时刻是空的），之上到 2^39 占死
    //   macOS 27（gate-host / Spare-host）的共享缓存铺满 [6, 57) GB，低区没有这段：改在 0x70 那块 64 GB 空洞开头模拟同样大小（别名区承诺末端会越过 2^39，
    //   游戏碰到的地址在 2^39 以内；QueryMemory 的地址空间上界按别名区末放宽，svc_mem.c free_span）
    { const char *e6 = getenv("S2A_VA_IOS26"); if (e6 && *e6 == '1') {
        const uint64_t lo = 0x300000000ull, n = 0xFC0000000ull - 0x300000000ull;
        void *t = mmap((void *)lo, n, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0); int low = t == (void *)lo; if (t != MAP_FAILED) munmap(t, n);
        fat = low ? lo : 0x7000000000ull; g_fit = cap = n; sz = 0;
        LOG("模拟 iOS 26 大地址档（S2A_VA_IOS26）：空洞放在 %#llx（%s）+%llu MB", (unsigned long long)fat, low ? "同 iOS 26 位置" : "macOS 27 / iOS 27 低区被共享缓存占满，改用 0x70 空洞开头", (unsigned long long)(n >> 20)); } }
    // 放不下标准布局不再起不了局（docs/方案_地址空间根修.md）：占最大一块、下方留 HOST_BELOW（3 GiB）给宿主（Metal / GC），布局小区在前、别名区伸出窗口（layout.c 乙）。
    //   宿主保留段不能放窗口上方：别名区伸出段覆盖那里，宿主放进去的东西会被游戏的远端访问静默读写
    if (!sz && g_fit >= MIN_WIN + HOST_BELOW) { uint64_t below = s2a_window_host_below(g_fit, g_span_learned); at = fat + below; want = g_fit - below; g_keep_lo = fat;
        LOG("地址窗口按需：本款标准布局要 %llu MB，本机 %s 以下最大一块 %llu MB（%#llx 起，地址上限 %#llx）——照样起局，下方 %llu MB 留宿主、其余作窗口（本机学到的跨度 %llu MB，0 = 没学到）",
            (unsigned long long)(g_need >> 20), hb, (unsigned long long)(g_fit >> 20), (unsigned long long)fat, (unsigned long long)top, (unsigned long long)(below >> 20),
            (unsigned long long)(g_span_learned >> 20)); }
    else if (!sz) { vaguard_release();
        LOG("【红】地址窗口不足：本机 %s 以下最大能放的一块 %llu MB，连模块与小区都放不下（本款标准布局要 %llu MB，地址上限 %#llx），起不了局", hb, (unsigned long long)(g_fit >> 20), (unsigned long long)(g_need >> 20), (unsigned long long)top);
        s2a_window_probe("窗口放不下"); return; }
    else want = g_need + TL_TAKE <= sz ? g_need + TL_TAKE : sz;   // 尾部统一分配最多 2 GB，空洞里剩多少给多少（63.25 GB 的款在 64 GB 空洞里只剩 766 MB）
    void *p = mmap((void *)at, want, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);   // 不带 MAP_FIXED：核对落点，不盖别人
    // errno 紧接 mmap 取：后面的 dlsym / 打日志会改它（10-24 #100 作者指出）；映射成功但落在别处时 errno 是旧值，不报
    int er = p == MAP_FAILED ? errno : 0;
    vaguard_release();   // 占过了（成或不成）才放行护栏（Mac：占之前它拒掉 macOS 27 malloc 落进窗口的大块保留）
    if (p != (void *)at) { if (p != MAP_FAILED) munmap(p, want);
        LOG("【红】地址窗口：空洞 %#llx +%llu MB 占不到（%s errno=%d）", (unsigned long long)at, (unsigned long long)(want >> 20), p == MAP_FAILED ? "失败" : "落在别处", er); s2a_window_probe("窗口没占到"); return; }
    g_ok = 1; g_base = at; g_size = g_res = want;
    guest_file_attach();
    LOG("窗口已占 %#llx +%llu MB（本款要 %llu MB + 尾部统一分配 %llu MB；所在空洞 %llu MB、%s 以下最大一块 %llu MB、地址上限 %#llx）", (unsigned long long)at, (unsigned long long)(want >> 20),
        (unsigned long long)(g_need >> 20), (unsigned long long)((want > g_need ? want - g_need : 0) >> 20), (unsigned long long)(sz >> 20), hb, (unsigned long long)(g_fit >> 20), (unsigned long long)top);
    if (cap) { uint64_t ft = 0; int fn = 0, fb = 0; fence_holes(at + want, 1ull << 39, &ft, &fn, &fb);   // 宿主保留段（窗口下方）由 iphone_va_fence 按低区规则处理
        LOG("地址窗口压到 %llu MB（S2A_VA_CAP_MB）：窗口之后到 2^39 的空洞 %d 段 %llu GB 已占死%s", (unsigned long long)(want >> 20), fn, (unsigned long long)(ft >> 30), fb ? "【红】有段没占上" : ""); }
    cmd_arena_reserve();   // 要在 iPhone 地址围栏之前：围栏把 2^39 之上的空洞几乎全占死（11-05 旷野之息录 / 放都报「2^39 之上没有 1024 MB 的空洞」）
#if TARGET_OS_OSX
    iphone_va_fence();
#endif
    BOOT_MARK("进程创建 → 占窗口（dyld 装载 + 构造函数）");
}

void s2a_window_reserve(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, vawin_reserve);
}
// ---------- 命令记录区（帧录放专用，Mac）----------
// 帧录（S2A_FRAME_REC）把 NVN 命令记录宿主块（graphics/nvn hle_nvn.c 影子块）按原地址存进录像，帧回放（S2A_FRAME_REPLAY）是另一个进程、要在原地址放回。
//   块原先 mmap(NULL) 落在内核挑的低区，回放进程同址常被它自己的库 / 堆 / Metal 占着（7df29fdfc 后回放全红）；放窗口尾部也不够：窗口放不下标准布局的款没有尾部（11-05 哆啦A梦 1350 高，尾部 0 MB）。
//   所以录 / 放两种进程（S2A_CMD_ARENA=1 也开，给单测用）在构造期、窗口之后再占一块 CMD_ARENA：2^39 之上（客体地址够不着）、地址上限以下最高的空洞，同一台机器同一个宿主两次起进程落在同一处。
//   录的进程按顺序切块（s2a_cmd_arena_map）；放的进程只占不切（切了会占掉要放回的地址），回放按映射段 MAP_FIXED 放回。其余进程不占，命令记录照旧 mmap(NULL)
#define CMD_ARENA (1ull << 30)
// 紧接着同一块保留里再放 VP_ARENA 给虚拟池（graphics/nvn hle_nvn.c vpool_reserve）：虚拟池各有一段自己的地址（贴图 / 缓冲地址 = 池基址 + 偏移，写在游戏内存里），
//   原先 mmap(NULL) 落在内核挑的低区，回放进程同址占不回（11-05 旷野之息唯一的虚拟池 0x131310000+0x7300000，回放读到别的映射或 SIGBUS 在 pkg_upload）。只给地址、不建页
#define VP_ARENA (64ull << 30)
static uint64_t g_ca_base, g_ca_used, g_va_used, g_va_cap = VP_ARENA; static int g_ca_cut;
static pthread_mutex_t g_ca_mu = PTHREAD_MUTEX_INITIALIZER;
static void cmd_arena_reserve(void) {   // 占窗口那一步在围栏前调；窗口没占到提前返回的路径由 vawin_boot 补调（只占一次）
    static int done; if (done++) return;
#if TARGET_OS_OSX
    const char *rec = getenv("S2A_FRAME_REC"), *rp = getenv("S2A_FRAME_REPLAY"), *on = getenv("S2A_CMD_ARENA");
    int r = rec && *rec, p = rp && *rp; if (!r && !p && !(on && *on == '1')) return;
    uint64_t top = s2a_va_top(), at, sz, fit, fat, lat; if (!top) top = 1ull << 47;
    pick_hole(top, CMD_ARENA + VP_ARENA, &at, &sz, &fit, &fat, 0, &lat);
    if (sz) at = at + sz - CMD_ARENA - VP_ARENA;   // 最高那个空洞的顶端一段（pick_hole 给的是空洞起点）
    if (!sz || at < (1ull << 39)) { LOG("【红】命令记录区：2^39 之上没有 %llu MB 的空洞，帧录的命令记录 / 虚拟池回放放不回", (unsigned long long)((CMD_ARENA + VP_ARENA) >> 20)); return; }
    void *m = mmap((void *)at, CMD_ARENA + VP_ARENA, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (m != (void *)at) { if (m != MAP_FAILED) munmap(m, CMD_ARENA + VP_ARENA); LOG("【红】命令记录区：%#llx 占不到", (unsigned long long)at); return; }
    g_ca_base = at; g_ca_cut = !p;
    LOG("命令记录区：%#llx +%llu MB，其后虚拟池区 +%llu GB（%s）", (unsigned long long)at, (unsigned long long)(CMD_ARENA >> 20), (unsigned long long)(VP_ARENA >> 30),
        p ? "帧回放：只占不切，录像里的块 / 虚拟池放回原地址" : "帧录：命令记录宿主块、虚拟池地址从这里按顺序切");
#else
    // iOS 帧录（11-06 旷野之息测试设备1）：命令记录块原先 mmap(NULL) 落在低区（0x169800000 一带），Mac 回放进程这段是它自己的库，放不回、整帧回放不了。
    //   录的进程同样占一块区，放在地址上限以下最高空洞的顶端（窗口尾之上；Mac 回放进程复现 iPhone 地址约束时这里是不可访问的保留，按原地址盖得上）。
    //   iOS 地址空间小（上限 2^39），虚拟池区按空洞剩余给，最多 16 GB；占不到就照旧不占（块回到 mmap(NULL)，回放可能放不回）
    const char *rec = getenv("S2A_FRAME_REC"); if (!rec || !*rec) return;
    uint64_t top = s2a_va_top(), at, sz, fit, fat, lat, vp = 16ull << 30; if (!top) return;
    pick_hole(top, CMD_ARENA + (1ull << 30), &at, &sz, &fit, &fat, 0, &lat);
    if (!sz) { LOG("【红】命令记录区（iOS 帧录）：没有 %llu MB 的空洞，命令记录块照旧落低区，Mac 回放可能放不回", (unsigned long long)((CMD_ARENA + (1ull << 30)) >> 20)); return; }
    if (sz - CMD_ARENA < vp) vp = (sz - CMD_ARENA) & ~((1ull << 30) - 1);
    at = at + sz - CMD_ARENA - vp;
    void *m = mmap((void *)at, CMD_ARENA + vp, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (m != (void *)at) { if (m != MAP_FAILED) munmap(m, CMD_ARENA + vp); LOG("【红】命令记录区（iOS 帧录）：%#llx 占不到", (unsigned long long)at); return; }
    g_ca_base = at; g_ca_cut = 1; g_va_cap = vp;
    LOG("命令记录区（iOS 帧录）：%#llx +%llu MB，其后虚拟池区 +%llu GB（命令记录宿主块、虚拟池地址从这里按顺序切，Mac 回放按原地址放回）", (unsigned long long)at, (unsigned long long)(CMD_ARENA >> 20), (unsigned long long)(vp >> 30));
#endif
}
void *s2a_cmd_arena_map(uint64_t len) {   // 录的进程：切一段可读写的；没有区 / 放的进程 / 切满返回 NULL（调用方退回 mmap(NULL)）
    if (!g_ca_base || !g_ca_cut || !len) return NULL;
    uint64_t n = (len + 16383) & ~16383ull; void *r = NULL;
    pthread_mutex_lock(&g_ca_mu);
    if (g_ca_used + n <= CMD_ARENA) {
        void *m = mmap((void *)(g_ca_base + g_ca_used), n, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
        if (m == (void *)(g_ca_base + g_ca_used)) { r = m; g_ca_used += n; }
    } else { static int once; if (!once++) LOG("【红】命令记录区 %llu MB 切满：之后的命令记录宿主块回放放不回", (unsigned long long)(CMD_ARENA >> 20)); }
    pthread_mutex_unlock(&g_ca_mu);
    return r;
}
void *s2a_vp_arena_map(uint64_t len) {   // 录的进程：给一段不可访问的地址（区里本来就是本进程的 PROT_NONE 保留）；没有区 / 放的进程 / 切满返回 NULL
    if (!g_ca_base || !g_ca_cut || !len) return NULL;
    uint64_t n = (len + 16383) & ~16383ull; void *r = NULL;
    pthread_mutex_lock(&g_ca_mu);
    if (g_va_used + n <= g_va_cap) { r = (void *)(g_ca_base + CMD_ARENA + g_va_used); g_va_used += n; }
    else { static int once; if (!once++) LOG("【红】虚拟池区 %llu GB 切满：之后的虚拟池回放放不回", (unsigned long long)(g_va_cap >> 30)); }
    pthread_mutex_unlock(&g_ca_mu);
    return r;
}
int s2a_vp_arena_has(const void *p, uint64_t n) { uint64_t a = (uint64_t)(uintptr_t)p, b = g_ca_base + CMD_ARENA; return g_ca_base && a >= b && a + n <= b + g_va_cap; }
int s2a_cmd_arena_has(const void *p, uint64_t n) { uint64_t a = (uint64_t)(uintptr_t)p; return g_ca_base && a >= g_ca_base && a + n <= g_ca_base + CMD_ARENA; }
// 区里的块还回：盖回不可访问（地址不再切，录局里会话重建才走到）
void s2a_cmd_arena_unmap(void *p, uint64_t len) { if (s2a_cmd_arena_has(p, len)) mmap(p, len, PROT_NONE, MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0); else munmap(p, len); }

// 纯虚拟地址预留不提交客体物理页；预热也必须赶在 UIKit / CoreAnimation 的大块预留之前占到整窗。
// 解包专用局（S2A_PACK_APPLY_ONLY=1，host_main.c：只解开推送来的资源包就退出，不起 C# 运行时、不装载游戏）不占客体窗口、不起命令记录区。
//   理由只有一条：解包局用不到客体内存，不占最省（地址、构造期时间）。11-07 曾把测试设备1 解包慢（16 GB 约 300 秒）归因到「匿名窗口在」，
//   14:39 同进程复测证否：匿名窗口在时 1 GB 写 2833 MB/s、解 16 GB 18.7 秒；上午慢局全在 05:46–06:51、快局全在 07:37 之后，窗口有无与时段完全重合（坑记录 11-07「机上解包约 50 MB/秒」）
static int apply_only(void) { const char *e = getenv("S2A_PACK_APPLY_ONLY"); return e && *e == '1'; }
__attribute__((constructor(101))) static void vawin_boot(void) {
    if (apply_only()) { vaguard_release(); LOG("地址窗口：解包专用局（S2A_PACK_APPLY_ONLY=1）不占客体窗口、不起命令记录区"); return; }   // 不占也要放行 Mac 护栏（同 S2A_VAWIN_NORESERVE）
    s2a_window_reserve();
    cmd_arena_reserve();
}

// 布局只用窗口前 size 字节时，把尾部还给系统（Metal 的大缓冲要用，见 layout.c）
// ---------- 窗口尾部统一分配（10-24 维护者批：异度神剑3 测试设备2 低区耗尽 OOM）----------
// GC 段模式只能用低区（新段落到尾部要扩卡表覆盖约 508 GB 跨度，必然失败，见坑记录 10-24），所以尾部留给没有簿记表的使用者：
//   Metal 共享缓冲（graphics/metal）、Ryujinx MemoryBlock（Ryujinx.Memory 补丁）、游戏线程宿主栈、信号备用栈、写跟踪页表叶子（graphics/track）。
// 做法（底子是帧率能耗线 perf/buf-tail 的 buftail.c，统一成这一个入口）：窗口收缩时尾部不还系统，保持窗口占位的 PROT_NONE；
//   分配 = 在保留段里 MAP_FIXED 映射匿名页（虚存标签按使用者，地址账可分开认出），释放 = MAP_FIXED 映射回 PROT_NONE（物理页随之归还）。
//   首次适配，空闲段按地址排序并合并。放不下 / 没接管时退回普通匿名映射（落低区），计「退回」；带 S2A_TAIL_ONLY 的调用方要 NULL 自己处理。
// 缺省开（地址摆放，不改语义）；S2A_TAIL=0 应急关：尾部照旧还系统，全部走退回路径
enum { TL_MAXSEG = 4096 };
#define TL_PAGE 16384ull
typedef struct { uint64_t a, n; } tl_seg;
static pthread_mutex_t g_tl_mu = PTHREAD_MUTEX_INITIALIZER;
static tl_seg g_tl_free[TL_MAXSEG]; static int g_tl_nfree;
static uint64_t g_tl_base, g_tl_size, g_tl_used, g_tl_peak, g_tl_segfull;
static struct { uint64_t live, peak, n, fb_n, fb_bytes; } g_tl_u[S2A_TAIL_NUSER];
static const char *const g_tl_uname[S2A_TAIL_NUSER] = {"Metal 缓冲", "Ryujinx 内存块", "线程栈", "信号备用栈", "写跟踪页表", "托管大块暂存"};
static int tail_on(void) { static int v = -1; if (v < 0) { const char *e = getenv("S2A_TAIL"); v = !(e && *e == '0'); } return v; }
static int tl_map(uint64_t a, uint64_t n, int prot, int user) {   // user < 0 = 还回（PROT_NONE、不打标签）
    void *p = mmap((void *)a, n, prot, MAP_PRIVATE | MAP_ANON | MAP_FIXED, user >= 0 ? VM_MAKE_TAG(S2A_TAIL_TAG0 + user) : -1, 0);
    return p == (void *)a ? 0 : -1;
}
void s2a_tail_init(uint64_t base, uint64_t size) {   // 接管 [base, base + size)：调用方保证是本进程的 PROT_NONE 保留；只接管一次
    pthread_mutex_lock(&g_tl_mu);
    uint64_t a = (base + TL_PAGE - 1) & ~(TL_PAGE - 1), e = (base + size) & ~(TL_PAGE - 1);
    if (!g_tl_size && e > a) { g_tl_base = a; g_tl_size = e - a; g_tl_free[0] = (tl_seg){a, e - a}; g_tl_nfree = 1; }
    pthread_mutex_unlock(&g_tl_mu);
}
int s2a_tail_has(const void *p) { uint64_t a = (uint64_t)p; return g_tl_size && a >= g_tl_base && a < g_tl_base + g_tl_size; }
void *s2a_tail_map(uint64_t len, int user, int prot) {
    int only = user & S2A_TAIL_ONLY; user &= ~S2A_TAIL_ONLY; if (user < 0 || user >= S2A_TAIL_NUSER) user = 0;
    if (!len) return NULL;
    uint64_t n = (len + TL_PAGE - 1) & ~(TL_PAGE - 1); void *r = NULL;
    pthread_mutex_lock(&g_tl_mu);
    for (int i = 0; i < g_tl_nfree; i++) if (g_tl_free[i].n >= n) {
        uint64_t a = g_tl_free[i].a;
        if (tl_map(a, n, prot, user)) break;
        if (g_tl_free[i].n == n) { memmove(&g_tl_free[i], &g_tl_free[i + 1], (size_t)(g_tl_nfree - i - 1) * sizeof *g_tl_free); g_tl_nfree--; }
        else { g_tl_free[i].a += n; g_tl_free[i].n -= n; }
        g_tl_used += n; if (g_tl_used > g_tl_peak) g_tl_peak = g_tl_used;
        g_tl_u[user].live += n; if (g_tl_u[user].live > g_tl_u[user].peak) g_tl_u[user].peak = g_tl_u[user].live; g_tl_u[user].n++; r = (void *)a; break;
    }
    if (!r) { g_tl_u[user].fb_n++; g_tl_u[user].fb_bytes += n; }
    pthread_mutex_unlock(&g_tl_mu);
    if (r || only) return r;
    void *p = mmap(NULL, len, prot, MAP_PRIVATE | MAP_ANON, -1, 0);   // 退回：普通匿名映射（落低区）
    return p == MAP_FAILED ? NULL : p;
}
void s2a_tail_unmap(void *p, uint64_t len, int user) {   // 尾部里的映射回 PROT_NONE 并还进空闲表；不在尾部的（退回路径给的）照常 munmap
    if (!p || !len) return;
    if (!s2a_tail_has(p)) { munmap(p, len); return; }
    user &= ~S2A_TAIL_ONLY; if (user < 0 || user >= S2A_TAIL_NUSER) user = 0;
    uint64_t a = (uint64_t)p, n = (len + TL_PAGE - 1) & ~(TL_PAGE - 1);
    pthread_mutex_lock(&g_tl_mu);
    tl_map(a, n, PROT_NONE, -1);
    int i = 0; while (i < g_tl_nfree && g_tl_free[i].a < a) i++;
    int ml = i > 0 && g_tl_free[i - 1].a + g_tl_free[i - 1].n == a, mr = i < g_tl_nfree && a + n == g_tl_free[i].a;
    if (ml && mr) { g_tl_free[i - 1].n += n + g_tl_free[i].n; memmove(&g_tl_free[i], &g_tl_free[i + 1], (size_t)(g_tl_nfree - i - 1) * sizeof *g_tl_free); g_tl_nfree--; }
    else if (ml) g_tl_free[i - 1].n += n;
    else if (mr) { g_tl_free[i].a = a; g_tl_free[i].n += n; }
    else if (g_tl_nfree < TL_MAXSEG) { memmove(&g_tl_free[i + 1], &g_tl_free[i], (size_t)(g_tl_nfree - i) * sizeof *g_tl_free); g_tl_free[i] = (tl_seg){a, n}; g_tl_nfree++; }
    else g_tl_segfull++;   // 空闲段表满：这段地址不再复用（只丢地址、不丢物理页），收局可见
    g_tl_used -= n; g_tl_u[user].live = g_tl_u[user].live >= n ? g_tl_u[user].live - n : 0;
    pthread_mutex_unlock(&g_tl_mu);
}
// 尾部账一行：接管、已用 / 剩余 / 最大空闲块、峰值；按使用者：在用 / 峰值 / 次数 / 退回（次数、字节）
void s2a_tail_note(char *o, size_t cap) {
    pthread_mutex_lock(&g_tl_mu);
    if (!g_tl_size) { snprintf(o, cap, "窗口尾部分配：未接管（%s）", tail_on() ? "尾部为 0 或窗口没占到" : "S2A_TAIL=0 应急关"); pthread_mutex_unlock(&g_tl_mu); return; }
    uint64_t big = 0; for (int i = 0; i < g_tl_nfree; i++) if (g_tl_free[i].n > big) big = g_tl_free[i].n;
    int k = snprintf(o, cap, "窗口尾部分配：接管 %llu MB，已用 %.1f MB、剩余 %.1f MB（最大空闲块 %.1f MB、空闲段 %d）、峰值 %.1f MB",
                     (unsigned long long)(g_tl_size >> 20), g_tl_used / 1048576.0, (g_tl_size - g_tl_used) / 1048576.0, big / 1048576.0, g_tl_nfree, g_tl_peak / 1048576.0);
    for (int u = 0; u < S2A_TAIL_NUSER && k > 0 && (size_t)k < cap; u++)
        if (g_tl_u[u].n || g_tl_u[u].fb_n)
            k += snprintf(o + k, cap - k, "；%s 在用 %.1f MB 峰值 %.1f MB 共 %llu 次、退回低区 %llu 次 %.1f MB", g_tl_uname[u], g_tl_u[u].live / 1048576.0,
                          g_tl_u[u].peak / 1048576.0, (unsigned long long)g_tl_u[u].n, (unsigned long long)g_tl_u[u].fb_n, g_tl_u[u].fb_bytes / 1048576.0);
    if (g_tl_segfull && k > 0 && (size_t)k < cap) snprintf(o + k, cap - k, "；空闲段表满丢地址 %llu 次", (unsigned long long)g_tl_segfull);
    pthread_mutex_unlock(&g_tl_mu);
}
void s2a_window_trim(uint64_t size) {
    if (!g_ok || size >= g_size) return;
    if (tail_on()) {   // 尾部前 TL_TAKE 留着占位时的 PROT_NONE，交给 s2a_tail_map；再往后还系统
        // 只接管 TL_TAKE（10-24 怪猎包 ef1e9bde9 开局即崩 3/3：整段 32 GB 都接管后，Metal 自己建缓冲（不走 s2a_tail_map）只剩低区 ~1 GB，建 4 MB 共享块失败；
        //   九款实测尾部峰值 ≤ 202 MB，2 GB 够用，其余照旧还系统给 Metal）
        // 窗口顶到空洞末尾（系统资源非 0 的款，窗口 63.25 GB 在 64 GB 空洞里只剩 766 MB）时只接管 TL_SMALL：尾部占着的 PROT_NONE Metal / malloc 用不上，
        //   10-24 八方2 包 b6c1d4192 iPhone 尾部接管 766 MB、只用 121.8 MB，低区账少 644 MB → 命令分配器 5 MB ×6、管线归档 ×2 腾不出（以前的包这 766 MB 还系统）。
        //   窗口之上还有 ≥ 4 GB 空闲（系统资源为 0 的款）才接管 TL_TAKE。尾部用满退回低区，s2a_tail_note 记「退回」
        uint64_t above = 0, al = 0; holes_in(g_base + g_res, 1ull << 39, &above, &al);
        uint64_t cap = above >= (4ull << 30) ? TL_TAKE : TL_SMALL;
        uint64_t take = g_size - size < cap ? g_size - size : cap;
        s2a_tail_init(g_base + size, take);
        if (take < g_size - size && munmap((void *)(g_base + size + take), g_size - size - take)) die("还窗口尾部失败 errno=%d", errno);
        LOG("窗口收到前 %llu MB，尾部 %llu MB 留作统一尾部分配（Ryujinx 内存块 / 线程栈 / 备用栈；S2A_TAIL=0 关）、再往后 %llu MB 还给系统（Metal 缓冲）", (unsigned long long)(size >> 20),
            (unsigned long long)(take >> 20), (unsigned long long)((g_size - size - take) >> 20));
        g_size = size; return; }
    if (munmap((void *)(g_base + size), g_size - size)) die("还窗口尾部失败 errno=%d", errno);
    LOG("窗口收到前 %llu MB，尾部 %llu MB 还给系统", (unsigned long long)(size >> 20), (unsigned long long)((g_size - size) >> 20));
    g_size = size;
}

// 客体窗口常驻（10-23 维护者：巫师3 实占 4.8 GB 里客体约 3.2 GB 只是推算，要读数）：mincore 按 1 GB 一段扫整个窗口，
//   数「在内存」页与「已压缩换出」页（客体内存是窗口里的匿名页，两者都计入进程实占）。向量用 64 KB 静态缓冲，不在低区另申请；没占窗口时两者 0
//   「在内存」有正对照（t_vawin：写 40 MB → +40960 KB）；「已压缩换出」靠 MINCORE_PAGED_OUT，未经正对照——
//   单测里逼不出压缩页（本机 madvise(MADV_PAGEOUT) 返回 ENOTSUP），读这一项时照实标「未经正对照」
// [lo, lo + len) 与窗口的交集里「在内存」/「已压缩换出」的字节（同一扫法；S2A_MEM_SPLIT 心跳分区账按堆区 / 物理映射区各扫一次）
static pthread_mutex_t g_resident_mu = PTHREAD_MUTEX_INITIALIZER;   // vec 是静态缓冲：心跳（主线程）与跳变采样线程（S2A_MEM_SPLIT）都会扫
static void range_resident_locked(uint64_t lo, uint64_t len, uint64_t *res, uint64_t *out);
void s2a_range_resident(uint64_t lo, uint64_t len, uint64_t *res, uint64_t *out) { pthread_mutex_lock(&g_resident_mu); range_resident_locked(lo, len, res, out); pthread_mutex_unlock(&g_resident_mu); }
static void range_resident_locked(uint64_t lo, uint64_t len, uint64_t *res, uint64_t *out) {
    static unsigned char vec[(1u << 30) / 16384];
    uint64_t pg = (uint64_t)getpagesize(), seg = sizeof vec * pg, r = 0, o = 0;
    if (seg > (1ull << 30)) seg = 1ull << 30;
    *res = *out = 0; if (!g_ok || !len) return;
    uint64_t a0 = lo > g_base ? lo : g_base, a1 = lo + len < g_base + g_size ? lo + len : g_base + g_size;
    a0 &= ~(pg - 1);
    for (uint64_t a = a0; a < a1; a += seg) {
        uint64_t n = a1 - a < seg ? a1 - a : seg;
        if (mincore((void *)a, n, (char *)vec)) continue;
        for (uint64_t i = 0, np = (n + pg - 1) / pg; i < np; i++) { if (vec[i] & MINCORE_INCORE) r++; else if (vec[i] & MINCORE_PAGED_OUT) o++; }
    }
    *res = r * pg; *out = o * pg;
}
void s2a_window_resident(uint64_t *res, uint64_t *out) { s2a_range_resident(g_base, g_size, res, out); }

// [lo, hi) 里没被映射的地址：合计与最大一块
static void holes_in(uint64_t lo, uint64_t hi, uint64_t *total, uint64_t *largest) {
    // 小地址档上限以上可能未被 Mach 映射表覆盖，不代表进程真能映射；GC 不得把它算成可用预算。
    uint64_t top = s2a_va_top();
    if (top && hi > top) hi = top;
    if (lo >= hi) return;
    uint64_t prev = lo; vm_address_t a = lo;
    for (;;) {
        vm_size_t sz = 0; vm_region_basic_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        int ok = vm_region_64(mach_task_self(), &a, &sz, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &cnt, &obj) == KERN_SUCCESS;
        uint64_t ge = ok && a < hi ? a : hi;
        if (ge > prev) { *total += ge - prev; if (ge - prev > *largest) *largest = ge - prev; }
        if (!ok || a >= hi) break;
        prev = a + sz; a += sz;
    }
}
// 宿主可用空洞（名字沿用「低区」）：4 GB 到窗口底，加上窗口收尾后还给系统的那段尾部（10-21 占满窗口款缩尾部还回约 766 MB，宿主映射在低区满了后落进去）。
// iPhone 上 Metal ≤256 MB 的共享缓冲、文件映射、线程栈都从这两段取；起局 / 心跳 / 崩溃现场 / 低区账都按它
void s2a_low_holes(uint64_t *total, uint64_t *largest) {
    *total = *largest = 0;
    holes_in(0x100000000ull, g_ok ? g_base : 1ull << 39, total, largest);
    if (g_ok) holes_in(g_base + g_size, 1ull << 39, total, largest);   // 窗口之上到 2^39：收尾还回的那段 + 所在空洞的其余部分（Metal 大缓冲落这里）
}
// 宿主高位区：窗口外、GC 新段用不上的宿主地址（GC 段模式的新段要和已有段连成一个跨度，落到这里簿记表要几 GB 连续地址、必然 OOM，见坑记录 10-24 异度神剑3）。
//   乙（窗口放不下标准布局，g_keep_lo）：窗口下方留给宿主的 [g_keep_lo, g_base)；窗口之上是别名区伸出段（远端），不给。
//   甲：收尾后的窗口之上到 2^39 / 地址上限；尾部统一分配占着的那段已映射，带提示的 mmap 自然跳过。
//   内核给 mmap(NULL) 挑最低的空洞，这两段要等 4 GB 起那段低区满了才轮到：大块、GC 之外的宿主映射（直连库段，graphics/nvn/lib_pack.inc lp_map）
//   带地址提示 mmap（不带 MAP_FIXED，内核从提示往上找第一个放得下的空洞）并核落点。不预先占住：占住了 Metal / malloc 在低区满后就落不进来
//   （10-24 怪猎尾部整段接管、开局即崩，坑记录）。没占到窗口回 0。调用方各自声明（graphics/nvn nvn_mtl.m 弱定义），不进 native.h：它是抽取阶段的冷输入
int s2a_host_hi_range(uint64_t *lo, uint64_t *hi) {
    *lo = *hi = 0; if (!g_ok) return 0;
    if (g_keep_lo) { *lo = g_keep_lo; *hi = g_base; return 1; }
    uint64_t top = s2a_va_top(), h = 1ull << 39; if (top && top < h) h = top;
    if (g_base + g_size >= h) return 0;
    *lo = g_base + g_size; *hi = h; return 1;
}

// 文件句柄用量：已开句柄数（fcntl 逐号探到 min(软上限, 4096)，信号处理里也能调）+ RLIMIT_NOFILE 软 / 硬上限。
// 10-21 巫师3 归档随机开不了：地址与句柄两种耗尽都要现场读数；按需开分片的片数上限按「软上限 − 已开」算（gal 层 dlsym 取）
void s2a_fd_usage(int *open_n, uint64_t *soft, uint64_t *hard) {
    struct rlimit rl = {0, 0}; getrlimit(RLIMIT_NOFILE, &rl); *soft = rl.rlim_cur; *hard = rl.rlim_max;
    int lim = rl.rlim_cur < 4096 ? (int)rl.rlim_cur : 4096, n = 0;
    for (int fd = 0; fd < lim; fd++) if (fcntl(fd, F_GETFD) != -1) n++;
    *open_n = n;
}

// 窗口外映射归账（诊断，起局打一次）：iPhone 上 VAMM 游戏占满窗口时窗口外只剩约 1.7 GB，C# 初始化吃掉约 1 GB，之后建线程 / 开着色器库 / 暂存缓冲相继失败
// （10-20 巫师3 测试设备2：C# 初始化后 589 MB，到第 103 号线程只剩 58 MB）。打最大的 12 块（地址、大小、当前 / 最大权限、内核用途标签）与按标签合计前 8 类
void s2a_vm_top(const char *when) {
    enum { TOPN = 12, NTAG = 256 };
    struct { uint64_t a, n; int p, mp; unsigned tag; } top[TOPN]; int nt = 0; uint64_t bytag[NTAG] = {0}, tot = 0;
    uint64_t wlo = g_ok ? g_base : 0, whi = g_ok ? g_base + g_size : 0;
    vm_address_t a = 0x100000000ull;
    for (;;) {
        vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        if (vm_region_recurse_64(mach_task_self(), &a, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) != KERN_SUCCESS) break;
        if (a >= wlo && a < whi) { a = whi; continue; }   // 窗口本身不算（本进程占位 / 游戏地址空间）
        unsigned tag = info.user_tag < NTAG ? info.user_tag : 0; bytag[tag] += sz; tot += sz;
        int k = nt < TOPN ? nt++ : -1;
        if (k < 0) { int m = 0; for (int i = 1; i < TOPN; i++) if (top[i].n < top[m].n) m = i; if (top[m].n < sz) k = m; }
        if (k >= 0) { top[k].a = a; top[k].n = sz; top[k].p = info.protection; top[k].mp = info.max_protection; top[k].tag = info.user_tag; }
        a += sz;
    }
    char b[1600]; int o = snprintf(b, sizeof b, "窗口外映射 [%s]：合计 %llu MB；最大 %d 块：", when, (unsigned long long)(tot >> 20), nt);
    for (int r = 0; r < nt; r++) { int m = r; for (int i = r + 1; i < nt; i++) if (top[i].n > top[m].n) m = i; if (m != r) { __typeof__(top[0]) x = top[r]; top[r] = top[m]; top[m] = x; }
        o += snprintf(b + o, sizeof b - (size_t)o, " %#llx %llu MB p%d/%d 标签 %u；", (unsigned long long)top[r].a, (unsigned long long)(top[r].n >> 20), top[r].p, top[r].mp, top[r].tag); }
    LOG("%s", b);
    o = snprintf(b, sizeof b, "窗口外映射 [%s] 按用途标签合计前 8：", when);
    for (int r = 0; r < 8; r++) { int m = -1; for (int i = 0; i < NTAG; i++) if (bytag[i] && (m < 0 || bytag[i] > bytag[m])) m = i; if (m < 0) break;
        o += snprintf(b + o, sizeof b - (size_t)o, " 标签 %d %llu MB；", m, (unsigned long long)(bytag[m] >> 20)); bytag[m] = 0; }
    LOG("%s", b);
}

// 低区文件映射按目录合计（10-21 巫师3：只读文件映射比账上的归档多约 335 MB，要知道是谁的文件）：逐块（只认文件页）proc_regionfilename，按所在目录累加字节与文件块数，打前 12。
// proc_regionfilename 不在 iOS SDK 头文件里：第一次（C# 初始化后，非信号上下文）按名字取，取不到就不打；崩溃处理里只用已取到的指针、不再 dlsym
static int (*g_regfn)(int, uint64_t, void *, uint32_t); static int g_regfn_tried;
// 按目录 + 扩展名合计（10-21 巫师3：同一 shaders 目录里管线归档 .bin 与离线库 .metallib 要分开看）；扫 [lo, hi) 与窗口尾部 [lo2, hi2)（还给系统的那段，没有就传 0, 0）
static void s2a_vm_low_files(const char *when, uint64_t lo, uint64_t hi, uint64_t lo2, uint64_t hi2) {
    if (!g_regfn_tried && strcmp(when, "崩溃时")) { g_regfn_tried = 1; g_regfn = (int (*)(int, uint64_t, void *, uint32_t))dlsym(RTLD_DEFAULT, "proc_regionfilename"); }
    if (!g_regfn) return;
    enum { NDIR = 48 }; static struct { char dir[200]; uint64_t bytes; int n; } t[NDIR]; int nt = 0; uint64_t other = 0;
    memset(t, 0, sizeof t);
    char path[1024];
    for (int seg = 0; seg < 2; seg++) {
    vm_address_t a = seg ? lo2 : lo; uint64_t end = seg ? hi2 : hi;
    for (; a < end;) {
        vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        if (vm_region_recurse_64(mach_task_self(), &a, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) != KERN_SUCCESS || a >= end || (!seg && info.user_tag == 32)) break;
        // 只认文件页（external_pager）：proc_regionfilename 对匿名区返回它后面那个文件映射的名字（Mac 实测：malloc / Metal 区被记到下一个文件名下，
        // 8 MB 的文件映射合计出 148 MB），10-21 之前这里的按目录合计因此虚高
        int r = info.external_pager ? g_regfn(getpid(), a, path, sizeof path) : 0;
        if (r > 0) {
            path[r < (int)sizeof path ? r : (int)sizeof path - 1] = 0;
            char *sl = strrchr(path, '/'), *dot = sl ? strrchr(sl, '.') : NULL; char ext[16] = "";
            if (dot && strlen(dot) < sizeof ext) snprintf(ext, sizeof ext, "%s", dot);
            if (sl && sl != path) { *sl = 0; if (ext[0] && strlen(path) + strlen(ext) + 3 < sizeof path) strcat(strcat(path, "/*"), ext); }
            int i = 0; for (; i < nt && strncmp(t[i].dir, path, sizeof t[i].dir - 1); i++) {}
            if (i == nt) { if (nt < NDIR) { snprintf(t[nt].dir, sizeof t[nt].dir, "%s", path); nt++; } else { other += sz; a += sz; continue; } }
            t[i].bytes += sz; t[i].n++;
        }
        a += sz;
    }
    }
    for (int k = 0; k < 12 && k < nt; k++) {   // 选出最大的打（就地选择，不分配）
        int m = k; for (int j = k + 1; j < nt; j++) if (t[j].bytes > t[m].bytes) m = j;
        if (m != k) { typeof(t[0]) x = t[k]; t[k] = t[m]; t[m] = x; }
        if (t[k].bytes < (1ull << 20)) break;
        LOG("  低区文件映射 [%s] %6llu MB（%d 块）%s", when, (unsigned long long)(t[k].bytes >> 20), t[k].n, t[k].dir);
    }
    if (other) LOG("  低区文件映射 [%s] 其余目录（超过 %d 个）%llu MB", when, NDIR, (unsigned long long)(other >> 20));
}

// 低区 + 窗口尾部按用途标签合计（10-21 巫师3 测试设备2 进场骤降 1.2 GB，Metal 记账的只涨 68 MB：要分清 GPU 驱动区 100 / 无标签 0 / 线程栈 30 / malloc 的各自涨多少）：
// 前 6 个标签 + 文件页合计写进 out，一行。只读 vm_region，不分配，低区账骤降时调
void s2a_low_tags(char *out, size_t cap) {
    enum { NTAG = 256 }; uint64_t bytag[NTAG] = {0}, file = 0;
    uint64_t lo2 = g_ok ? g_base + g_size : 0;
    for (int seg = 0; seg < 2; seg++) {
        vm_address_t a = seg ? lo2 : 0x100000000ull; uint64_t end = seg ? (lo2 ? 1ull << 39 : 0) : g_ok ? g_base : 1ull << 39;
        while (a < end) {
            vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
            if (vm_region_recurse_64(mach_task_self(), &a, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) != KERN_SUCCESS || a >= end || (!seg && info.user_tag == 32)) break;
            uint64_t e = a + sz < end ? sz : end - a; bytag[info.user_tag < NTAG ? info.user_tag : 0] += e; if (info.external_pager) file += e;
            a += sz;
        }
    }
    int o = snprintf(out, cap, "按标签（含尾部）：文件页 %llu MB", (unsigned long long)(file >> 20));
    for (int r = 0; r < 6 && o > 0 && (size_t)o < cap; r++) { int m = -1; for (int i = 0; i < NTAG; i++) if (bytag[i] && (m < 0 || bytag[i] > bytag[m])) m = i; if (m < 0) break;
        o += snprintf(out + o, cap - (size_t)o, "、标签 %d %llu MB", m, (unsigned long long)(bytag[m] >> 20)); bytag[m] = 0; }
}

// 低区文件映射按目录合计单独打（低区账骤降时调；10-26 巫师3 测试设备1：文件页 60 秒涨约 400 MB，只在 C# 初始化后列过一次、崩溃时宿主自己崩了没打出来，
//   看不出是谁的文件）。范围同低区全列：4 GB 起到窗口，加窗口尾部
void s2a_low_files(const char *when) {
    uint64_t hi = g_ok ? g_base : 1ull << 39, tlo = g_ok && g_size < g_res ? g_base + g_size : 0, thi = tlo ? g_base + g_res : 0;
    s2a_vm_low_files(when, 0x100000000ull, hi, tlo, thi);
}

// 低区全列（10-20 八方2 / 巫师3 iPhone 地址耗尽）：iPhone 上窗口外能用的只有 4 GB 起到 dyld 共享缓存区（标签 32，0x1_8000_0000 起约 57 GB）之间，
// 再往上到窗口是内核保护区（标签 31）。把这段逐块列全（同标签同权限的相邻块合并，空洞也列），不截断，按块对上是谁的：GC 保留 / Ryujinx DRAM / 服务堆 / 游戏模块 / Metal / 线程栈
void s2a_vm_low(const char *when) {
    uint64_t lo = 0x100000000ull, hi = g_ok ? g_base : 1ull << 39, prev = lo;
    uint64_t ca = 0, cn = 0; int cp = -1, cmp_ = -1; unsigned ctag = 0; int nb = 0, ns = 0; uint64_t used = 0, hole = 0, small = 0;
    LOG("低区全列 [%s]：起 %#llx（同标签同权限相邻块合并，≥1 MB 逐块列、更小的只计数；p 当前/最大权限；空 = 未映射）", when, (unsigned long long)lo);
    #define FLUSH() do { if (cn >= (1ull << 20)) { LOG("  低区 %#llx %6llu MB p%d/%d 标签 %u", (unsigned long long)ca, (unsigned long long)(cn >> 20), cp, cmp_, ctag); nb++; } else if (cn) { small += cn; ns++; } cn = 0; } while (0)
    vm_address_t a = lo;
    for (;;) {
        vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        int ok = vm_region_recurse_64(mach_task_self(), &a, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) == KERN_SUCCESS;
        int stop = !ok || a >= hi || info.user_tag == 32;   // 到共享缓存区 / 窗口为止
        uint64_t ge = stop ? (ok && a < hi ? a : hi) : a;
        if (ge > prev) { FLUSH(); if (ge - prev >= (1ull << 20)) LOG("  低区 %#llx %6llu MB 空", (unsigned long long)prev, (unsigned long long)((ge - prev) >> 20)); hole += ge - prev; }
        if (stop) break;
        if (cn && ca + cn == a && cp == info.protection && cmp_ == info.max_protection && ctag == info.user_tag) cn += sz;
        else { FLUSH(); ca = a; cn = sz; cp = info.protection; cmp_ = info.max_protection; ctag = info.user_tag; }
        used += sz; prev = a + sz; a += sz;
    }
    FLUSH();
    #undef FLUSH
    { void (*gn)(char *, size_t) = (void (*)(char *, size_t))dlsym(RTLD_DEFAULT, "nxgal_va_note"); if (gn) { char g[1400]; gn(g, sizeof g); LOG("渲染器地址账 [%s]：%s", when, g); } }
    // 窗口尾部（缩尾部后还给系统的那段）：低区满了宿主映射落进去，崩溃现场要看它还剩多少
    uint64_t tlo = g_ok && g_size < g_res ? g_base + g_size : 0, thi = tlo ? g_base + g_res : 0;
    if (tlo) { uint64_t th = 0, tl = 0; holes_in(tlo, thi, &th, &tl);
        LOG("窗口尾部 [%s]：%#llx +%llu MB，已映射 %llu MB、空 %llu MB（最大一块 %llu MB）", when, (unsigned long long)tlo, (unsigned long long)((thi - tlo) >> 20),
            (unsigned long long)((thi - tlo - th) >> 20), (unsigned long long)(th >> 20), (unsigned long long)(tl >> 20)); }
    { char tb[900]; s2a_tail_note(tb, sizeof tb); LOG("%s [%s]", tb, when); }
    s2a_vm_low_files(when, lo, hi, tlo, thi);
    { void (*mn)(const char *) = (void (*)(const char *))dlsym(RTLD_DEFAULT, "s2a_msample_note"); if (mn) mn(when); }   // malloc 按调用点采样（S2A_MALLOC_SAMPLE=1 才有，见 msample.c）
    LOG("低区全列 [%s] 完：止于 %#llx，已映射 %llu MB（逐块列 %d 块；<1 MB 的 %d 块合计 %llu MB 未列）、空 %llu MB", when, (unsigned long long)prev, (unsigned long long)(used >> 20), nb, ns, (unsigned long long)(small >> 20), (unsigned long long)(hole >> 20));
}

// 探测：列出窗口内的全部映射。
// 占到时窗口归本进程独占（内核不会把别人的映射放进已占的地址），只核「整 64 GB 仍在」——内核按最多 128 MB 一段记账，所以是连续多段；
// 没占（诊断模式）时列出谁映射进来了：这就是 5b-1 要量的「运行时 / Metal 会不会抢窗口」
// 系统给本进程的地址上限（TASK_VM_INFO 的 max_address，rev2 起有）；读不到回 0
uint64_t s2a_va_top(void) {
    task_vm_info_data_t vi; mach_msg_type_number_t c = TASK_VM_INFO_COUNT;
    return task_info(mach_task_self(), TASK_VM_INFO, (task_info_t)&vi, &c) == KERN_SUCCESS && c >= TASK_VM_INFO_REV2_COUNT ? vi.max_address : 0;
}
void s2a_window_probe(const char *when) {
    if (!g_ok) { g_probe_n = 0; LOG("窗口探测 [%s]：没有窗口", when); return; }
    uint64_t wb = g_base, ws = g_size;
    vm_address_t a = wb; uint64_t end = wb + ws, covered = 0, expect = wb; int n = 0, contiguous = 1;
    char buf[768]; size_t k = 0; buf[0] = 0;
    while (a < end) {
        vm_size_t sz = 0; vm_region_basic_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64; mach_port_t obj = MACH_PORT_NULL;
        if (vm_region_64(mach_task_self(), &a, &sz, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &cnt, &obj) != KERN_SUCCESS || a >= end) break;
        n++; if (a != expect) contiguous = 0;
        uint64_t e = a + sz > end ? end : a + sz; covered += e - a; expect = e;
        if (!g_ok && k < sizeof buf - 64) k += (size_t)snprintf(buf + k, sizeof buf - k, " %#lx+%#lx/p%d", (unsigned long)a, (unsigned long)sz, info.protection);
        a += sz;
    }
    g_probe_n = g_ok ? -1 : n;
    if (g_ok) LOG("窗口探测 [%s]：本进程占位%s（%d 段，覆盖 %llu MB）", when, contiguous && covered == ws ? "完整" : "【红】不完整", n, (unsigned long long)(covered >> 20));
    else LOG("窗口探测 [%s]：未占窗口，窗口内别人的映射 %d 段 %llu MB%s", when, n, (unsigned long long)(covered >> 20), buf);
}

// 地址余量走势（诊断，每 30 秒一行）：低区空洞合计 / 最大块 + 渲染器地址账——看低区是缓涨到顶还是有界
static void *va_watch(void *a) { s2a_thread_name("s2a-va-watch");
    (void)a; void (*gn)(char *, size_t) = (void (*)(char *, size_t))dlsym(RTLD_DEFAULT, "nxgal_va_note");
    void (*rr)(void) = (void (*)(void))dlsym(RTLD_DEFAULT, "s2a_direct_res_report");   // direct_host.c；只链 vawin 的单测里取不到就不调
    for (int t = 30;; t += 30) { sleep(30); uint64_t ht, hl; s2a_low_holes(&ht, &hl); char g[1400] = ""; if (gn) gn(g, sizeof g);
        LOG("地址余量 第 %d 秒：低区空洞合计 %llu MB、最大一块 %llu MB；%s", t, (unsigned long long)(ht >> 20), (unsigned long long)(hl >> 20), g);
        if (rr) rr(); }   // 直连模式：资源行（s2a_res_report_register 登记），跟着地址余量每 30 秒一次
    return NULL;
}
void s2a_va_watch_start(void) { static int started; if (started) return; pthread_t th; if (!pthread_create(&th, NULL, va_watch, NULL)) { started = 1; pthread_detach(th); } }

// 托管堆 OutOfMemoryException 现场（服务层 MemDiag.InstallOomDump 第一次撞到时按名字调；10-24 异度神剑3 真机：低区还有 580 MB 整块、GC 却连 32 MB 新段都拿不到）。
//   打低区全列、窗口尾部到 2^39 的逐块（GC 新段若落进窗口尾部，卡表 / 标记位图要覆盖到这里）、窗口外最大块与按标签合计。只读 vm_region、不在托管堆上分配
void s2a_oom_dump(const char *when) {
    s2a_vm_low(when);
    uint64_t lo = g_ok ? g_base + g_size : 1ull << 39, hi = 1ull << 39;
    LOG("窗口尾部逐块 [%s]：%#llx 起到 2^39（窗口收尾还给系统的那段；同标签同权限相邻块合并，≥1 MB 逐块列）", when, (unsigned long long)lo);
    vm_address_t a = lo; uint64_t prev = lo;
    for (;;) {
        vm_size_t sz = 0; natural_t depth = 0; vm_region_submap_info_data_64_t info; mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
        int ok = vm_region_recurse_64(mach_task_self(), &a, &sz, &depth, (vm_region_recurse_info_t)&info, &cnt) == KERN_SUCCESS;
        uint64_t ge = ok && a < hi ? a : hi;
        if (ge > prev && ge - prev >= (1ull << 20)) LOG("  尾部 %#llx %6llu MB 空", (unsigned long long)prev, (unsigned long long)((ge - prev) >> 20));
        if (!ok || a >= hi) break;
        if (sz >= (1ull << 20)) LOG("  尾部 %#llx %6llu MB p%d/%d 标签 %u", (unsigned long long)a, (unsigned long long)(sz >> 20), info.protection, info.max_protection, info.user_tag);
        prev = a + sz; a += sz;
    }
    s2a_vm_top(when);
    char b[512]; s2a_low_tags(b, sizeof b); LOG("低区账 [%s]：%s", when, b);
}
#endif
