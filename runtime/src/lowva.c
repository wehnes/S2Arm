// 低区统一记账（接口与规则见 runtime/include/s2a_lowva.h）：判定只看实时扫描，账面只用来归因。
// 事件驱动：申请时扫；巡检线程只在占满窗口的款起，余量 < 2 × 保留量时每秒扫、否则每 10 秒扫（拦不到的分配没有事件，要有人看）；
// 不设地址上限的款用峰值巡检；iOS 物理余量不足时同样触发腾退并加快采样。
#include "native.h"
#include "../include/s2a_lowva.h"
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <malloc/malloc.h>
#endif
#if defined(__IPHONE_OS_VERSION_MIN_REQUIRED)
#include <os/proc.h>
#endif

#define MB (1ull << 20)
#define GB (1ull << 30)
enum { NUSER = 16, WIN_S = 60, NRATE = 128, SLOW_S = 10, CREDIT_NS = 2000000000 };
static const uint64_t CONTIG_FLOOR = 256 * MB, R_MIN = 256 * MB;
static const int FD_HEADROOM = 64;

static struct { char name[48]; s2a_lowva_evict_fn evict; void *ctx; _Atomic int64_t held, inflight; _Atomic int opt; } U[NUSER + 1];   // opt：做过可选申请（可拒绝）
static _Atomic int g_nuser;
#if defined(__ANDROID__)
static pthread_mutex_t g_mu;
static pthread_once_t g_mu_once = PTHREAD_ONCE_INIT;
static _Atomic int g_mu_ready;
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal-path readiness must be lock-free");
static void lowva_mutex_init(void) {
    pthread_mutexattr_t attr;
    int error = pthread_mutexattr_init(&attr);
    if (error) die("Android 低区账互斥属性初始化失败 errno=%d", error);
    error = pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
    if (!error) error = pthread_mutex_init(&g_mu, &attr);
    pthread_mutexattr_destroy(&attr);
    if (error) die("Android 低区账递归互斥初始化失败 errno=%d", error);
    atomic_store_explicit(&g_mu_ready, 1, memory_order_release);
}
static void lowva_lock(void) {
    int error = pthread_once(&g_mu_once, lowva_mutex_init);
    if (!error) error = pthread_mutex_lock(&g_mu);
    if (error) die("Android 低区账互斥加锁失败 errno=%d", error);
}
static int lowva_trylock(void) {
    return atomic_load_explicit(&g_mu_ready, memory_order_acquire) && pthread_mutex_trylock(&g_mu) == 0;
}
#else
static pthread_mutex_t g_mu = PTHREAD_RECURSIVE_MUTEX_INITIALIZER;   // 护登记、保留量学习、腾退；note 不拿
#define lowva_lock() pthread_mutex_lock(&g_mu)
#define lowva_trylock() (pthread_mutex_trylock(&g_mu) == 0)
#endif
static void (*g_scan)(uint64_t *, uint64_t *) = s2a_low_holes;       // 单测换成假扫描
static uint64_t (*g_now)(void);                                      // 单测换成假钟（纳秒）
static uint64_t g_reserve = R_MIN, g_prev_u, g_prev_ns;
// 拦不到部分的基准（第一次扫描时记）：U = 起账以来空洞的减少 − 账面的增加。4 GB 到窗口底这段里还有系统的几百 GB 保留区，
// 不能拿「整段宽度 − 空洞」当已映射（10-21 丝之歌那样算出 453894 MB）
static uint64_t g_base_t; static int64_t g_base_tr; static int g_have_base;
static struct { uint64_t ns, rise; } g_rate[NRATE]; static int g_nrate;   // 最近的单秒涨幅（相邻扫描间隔 ≥ 1 秒折算），保留量按最近 WIN_S 秒取最大
static uint64_t g_credit, g_credit_t0, g_credit_ns;                  // 腾退回调已放掉强引用、扫描还没看到回落的字节（另一线程建管线时最多晚一次建完）
static const uint64_t MEMORY_RESERVE = 512 * MB;
static uint64_t g_memory_credit, g_memory_credit_ns, g_memory_previous = UINT64_MAX;
static int g_memory_warned;

// UINT64_MAX 表示平台无此读数；iOS 返回 0 时仍要处理临界压力。
__attribute__((weak)) uint64_t s2a_lowva_memory_headroom(void) {
#if defined(__IPHONE_OS_VERSION_MIN_REQUIRED)
    return os_proc_available_memory();
#else
    return UINT64_MAX;
#endif
}
static int g_have_prev, g_deficit_logged, g_watch_started;
static uint64_t g_drop_t;                                            // 骤降读数的起点（上次打读数时的 T）
// 峰值读数（宿主在窗口外最多占过多少地址，收局 / 崩溃各打一行）：整局最低 T、最低 B 及其时刻（秒，相对第一次扫描），第一次扫描的 T 记作起点 T0。
// T 比上次快照时低 ≥ 64 MB 才重存一份按标签合计（不是每次扫描都走 vm_region）；双缓冲：崩溃处理里读的那份不会被写到一半
enum { PEAK_S = 5 };
static const uint64_t PK_SNAP = 64 * MB;
static uint64_t g_pk_ns0, g_pk_t0, g_pk_tmin, g_pk_tmin_s, g_pk_bmin, g_pk_bmin_s; static int g_pk_have, g_peak_watch;
static struct { uint64_t t; char tags[400]; } g_pk_snap[2]; static _Atomic int g_pk_cur;   // 快照时的 T 与按标签合计；g_pk_cur 指向已写完的那份
static void ledger(const char *why, const char *stuck);

static uint64_t lv_now(void) { if (g_now) return g_now(); struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec; }
// 峰值记一次（持锁）：第一次记起点 T0（快照基准也是 T0，快照串空）；T 创新低且比上次快照低 ≥ 64 MB 才重存按标签合计，先写另一份再切过去
static void peak_note(uint64_t t, uint64_t b, uint64_t ns) {
    if (!g_pk_have) { g_pk_have = 1; g_pk_ns0 = ns; g_pk_t0 = g_pk_tmin = t; g_pk_bmin = b; g_pk_tmin_s = g_pk_bmin_s = 0; g_pk_snap[atomic_load(&g_pk_cur)].t = t; return; }
    uint64_t s = (ns - g_pk_ns0) / 1000000000ull; int cur = atomic_load(&g_pk_cur);
    if (t < g_pk_tmin) { g_pk_tmin = t; g_pk_tmin_s = s;
        if (g_pk_snap[cur].t - t >= PK_SNAP) { int n = cur ^ 1; g_pk_snap[n].t = t; s2a_low_tags(g_pk_snap[n].tags, sizeof g_pk_snap[n].tags); atomic_store(&g_pk_cur, n); } }
    if (b < g_pk_bmin) { g_pk_bmin = b; g_pk_bmin_s = s; }
}
// 设限 = 占了窗口且窗口之外的大块余量 < 4 GB（系统资源非 0 的款窗口顶到空洞末，只剩约 766 MB，要记账；为 0 的款剩约 32 GB，不设限）
static int limited(void) { return s2a_window_ok() && s2a_window_spare() < 4 * GB; }
// 可拒绝的持有 E：做过可选申请（optional = 1：拒了调用方有退路，如归档片不开、首遇现建）的使用者的账面 + 申请中
static int64_t capped(void) { int64_t t = 0; int n = atomic_load(&g_nuser); for (int i = 1; i <= n; i++) if (atomic_load(&U[i].opt)) t += atomic_load(&U[i].held) + atomic_load(&U[i].inflight); return t; }
static int64_t tracked(void) { int64_t t = 0; int n = atomic_load(&g_nuser); for (int i = 1; i <= n; i++) t += atomic_load(&U[i].held) + atomic_load(&U[i].inflight); return t; }
static uint64_t untracked(uint64_t holes) { if (!g_have_base) return 0; int64_t u = ((int64_t)g_base_t - (int64_t)holes) - (tracked() - g_base_tr); return u > 0 ? (uint64_t)u : 0; }

// 扫一次（持锁）：顺带学拦不到部分的涨幅（相邻两次扫描间隔 ≥ 1 秒才折成单秒涨幅）、热身后更新保留量、结算腾退待回落
static void scan(uint64_t *t, uint64_t *b) {
    g_scan(t, b); uint64_t ns = lv_now(); peak_note(*t, *b, ns);
    if (!g_have_base) { g_base_t = *t; g_base_tr = tracked(); g_have_base = 1; }
    uint64_t u = untracked(*t);
    if (!g_have_prev) { g_prev_u = u; g_prev_ns = ns; g_have_prev = 1; }
    else if (ns - g_prev_ns >= 1000000000ull) {
        double sec = (double)(ns - g_prev_ns) / 1e9; uint64_t rise = u > g_prev_u ? (uint64_t)((double)(u - g_prev_u) / sec) : 0;
        if (g_nrate == NRATE) { memmove(g_rate, g_rate + 1, sizeof g_rate[0] * (NRATE - 1)); g_nrate--; }
        g_rate[g_nrate].ns = ns; g_rate[g_nrate].rise = rise; g_nrate++;
        g_prev_u = u; g_prev_ns = ns;
    }
    // 保留量 = 巡检来不及反应的那一下拦不到部分能涨多少：最近 WIN_S 秒单秒最大涨幅 × 2，下限 256 MB（没数据时就是 256）。
    // 只看最近：载入时的突发过去后降回来（不被开局那一下永远卡住）；要防的只是一拍之内，账本放行的都是可腾退的，涨起来巡检腾掉
    uint64_t mx = 0; for (int i = 0; i < g_nrate; i++) if (ns - g_rate[i].ns <= (uint64_t)WIN_S * 1000000000ull && g_rate[i].rise > mx) mx = g_rate[i].rise;
    g_reserve = 2 * mx > R_MIN ? 2 * mx : R_MIN;
    // 骤降读数（10-21 巫师3 两局：第 60 秒 T 1295 / 1323 MB、按 A 进场后不到 1 秒崩时 0 / 35，中间没有任何读数）：比上次打读数时少了 ≥ 200 MB 就打一行账（含各家账面），
    // 回升则起点跟上；申请时也扫，进场高峰里开片频繁，这行能把骤降逐段记下来
    if (!g_drop_t || *t > g_drop_t) g_drop_t = *t;
    else if (g_drop_t - *t >= 200 * MB) { g_drop_t = *t; ledger("骤降", NULL); char tg[400]; s2a_low_tags(tg, sizeof tg); LOG("低区账 [骤降]：%s", tg);
#if defined(__APPLE__)
        s2a_low_files("骤降");   // Mach external_pager / proc_regionfilename 明细；Android 仍用上面的真实 maps 总账
#endif
    }
    if (g_credit) { uint64_t back = *t > g_credit_t0 ? *t - g_credit_t0 : 0;
        if (back >= g_credit || ns - g_credit_ns > CREDIT_NS) g_credit = 0; else { g_credit -= back; g_credit_t0 = *t; } }
}

static void ledger(const char *why, const char *stuck) {
    uint64_t t, b; g_scan(&t, &b); int fn; uint64_t fs, fh; s2a_fd_usage(&fn, &fs, &fh);
    char buf[900]; size_t k = 0; buf[0] = 0; int n = atomic_load(&g_nuser);
    for (int i = 1; i <= n && k < sizeof buf - 80; i++)
        k += (size_t)snprintf(buf + k, sizeof buf - k, "%s%s %lld MB", i > 1 ? "、" : "", U[i].name, (long long)((atomic_load(&U[i].held) + atomic_load(&U[i].inflight)) / (int64_t)MB));
    char ms[160] = "";
#if defined(__APPLE__)
    // malloc 总账（各区合计）：iPhone 上 malloc 大块落低区、Mac 上落窗口之上——Mac 局判「iPhone 低区够不够」要它（10-29 IML 档巫师3：
    //   Mac 的 iPhone 低区模拟只给 malloc 留 512 MB，calloc 4 MB 失败时低区还有 1.9 GB）。取各区的锁：崩溃处理里不取
    if (strcmp(why, "崩溃时")) { malloc_statistics_t st; malloc_zone_statistics(NULL, &st);
        snprintf(ms, sizeof ms, "；malloc 在用 %llu MB、峰值 %llu MB、占地址 %llu MB", (unsigned long long)(st.size_in_use / MB), (unsigned long long)(st.max_size_in_use / MB), (unsigned long long)(st.size_allocated / MB)); }
#endif
    LOG("低区账 [%s]%s%s：空洞合计 T %llu MB、最大一块 B %llu MB、保留量 R %llu MB；文件句柄已开 n %d / 软上限 S %llu；%s%s拦不到的（Metal 内部 / malloc / 运行时）%llu MB%s",
        why, stuck ? "，卡在" : "", stuck ? stuck : "", (unsigned long long)(t / MB), (unsigned long long)(b / MB), (unsigned long long)(g_reserve / MB), fn, (unsigned long long)fs,
        buf, n ? "；" : "", (unsigned long long)(untracked(t) / MB), ms);
}

// 叫可腾退使用者腾 want 字节：按账面持有从多到少，一家腾不够轮下一家；返回合计腾出（计入待回落）
static uint64_t evict(uint64_t want) {
    uint64_t got = 0, t0, t1, b; int done[NUSER + 1] = {0}, n = atomic_load(&g_nuser);
    g_scan(&t0, &b);
    while (got < want) {
        int pick = 0;
        for (int i = 1; i <= n; i++) if (U[i].evict && !done[i] && atomic_load(&U[i].held) > 0 && (!pick || atomic_load(&U[i].held) > atomic_load(&U[pick].held))) pick = i;
        if (!pick) break;
        done[pick] = 1; got += U[pick].evict(U[pick].ctx, want - got);
    }
    if (got) {   // 已回落的当场结清，没回落的记待回落（基准取腾后这次扫描）
        g_scan(&t1, &b); uint64_t back = t1 > t0 ? t1 - t0 : 0;
        if (got > back) { g_credit += got - back; g_credit_t0 = t1; g_credit_ns = lv_now(); } }
    if (got) {
        uint64_t room = MEMORY_RESERVE - g_memory_credit;
        g_memory_credit += got < room ? got : room;
        g_memory_credit_ns = lv_now();
    }
    return got;
}

// 与地址空洞分开判定。只调用登记过的腾退回调，沿用其引用与 GPU 完成约束。
// 放掉强引用到进程脚印下降可能有延迟，最多等 2 秒再重复请求同一份余量。
static int memory_tick(void) {
    uint64_t available = s2a_lowva_memory_headroom(), now = lv_now();
    if (available == UINT64_MAX) {
        g_memory_credit = 0;
        g_memory_previous = UINT64_MAX;
        g_memory_warned = 0;
        return 0;
    }
    if (g_memory_previous != UINT64_MAX && available > g_memory_previous) {
        uint64_t returned = available - g_memory_previous;
        g_memory_credit -= returned < g_memory_credit ? returned : g_memory_credit;
    }
    g_memory_previous = available;
    if (now - g_memory_credit_ns >= CREDIT_NS) g_memory_credit = 0;
    uint64_t deficit = available < MEMORY_RESERVE ? MEMORY_RESERVE - available : 0;
    if (deficit > g_memory_credit) {
        uint64_t want = deficit - g_memory_credit, got = evict(want);
        if (got || !g_memory_warned) {
            LOG("进程内存余量 %llu MB：请求腾退 %llu MB，放掉引用 %llu MB（实际脚印回落待后续采样）",
                (unsigned long long)(available / MB), (unsigned long long)(want / MB), (unsigned long long)(got / MB));
        }
        g_memory_warned = !got;
    } else if (!deficit) g_memory_warned = 0;
    return available < 2 * MEMORY_RESERVE;
}

// 申请 bytes（连续 contig）够不够：地址按 T + 待回落判；返回缺口（0 = 够），*why = 卡在地址 / 句柄
// 可选申请用的保留量：学到的 R 不超过当前空洞的一半。R 按最近 60 秒拦不到部分单秒最大涨幅 × 2 学，载入时涨到超过空洞本身
//（10-21 暗黑3 冷启动三局：T 420–820 MB 时 R 866–1194），T − R 为负，0.4 MB 的归档片也一律拒；拒了那批管线要现建（每条 30–90 ms），
// 现建本身也占地址（编译产物进 Metal 内部），拒小片省不下地址。封顶 T/2、下限仍是 R_MIN（空洞小于 512 MB 时照旧按 256 MB 保留）：
// 载入期可选申请仍按「保留量之上富余的一半」放，R 不大时（巫师3 第 60 秒 R 478 < T/2 647）与原规则相同。必需申请与巡检照用学到的 R
uint64_t s2a_lowva_opt_reserve(uint64_t learned, uint64_t t) { uint64_t r = learned < t / 2 ? learned : t / 2; return r > R_MIN ? r : R_MIN; }
static uint64_t opt_reserve(uint64_t t) { return s2a_lowva_opt_reserve(g_reserve, t); }
// 判定本身（纯函数，单测直接代实数）：t / b 已含待回落，r 是本次用的保留量。连续块保底只管要连续的申请（contig > 0）：别让它吃掉最后一块大洞。
// contig = 0（调用方声明不要连续，如命令分配器多托一个命令缓冲）只判合计——这一项 256 − B 与本次申请无关，拒了 B 也回不来，
// 没有可腾退者时 B 一跌破 256 就此后次次拒（10-26 双人成行 itt_r2：B 178 时 5 MB 申请 613 次全拒，T 642 ≥ 5 + 321）
uint64_t s2a_lowva_need(uint64_t t, uint64_t b, uint64_t r, int fn, uint64_t fs, uint64_t bytes, uint64_t contig, const char **why) {
    uint64_t nt = t >= bytes + r ? 0 : bytes + r - t, nb = !contig || b >= contig + CONTIG_FLOOR ? 0 : contig + CONTIG_FLOOR - b, need = nt > nb ? nt : nb;
    int fd_short = (int64_t)fs - fn - 1 < FD_HEADROOM;
    *why = need ? (fd_short ? "地址与句柄" : "地址") : fd_short ? "句柄" : NULL;
    return need ? need : fd_short ? 1 : 0;   // 句柄不够时让可腾退的放掉一片（按需开的分片各占句柄时有用）
}
static uint64_t shortfall(uint64_t bytes, uint64_t contig, int optional, const char **why) {
    uint64_t t, b; scan(&t, &b); int fn; uint64_t fs, fh; s2a_fd_usage(&fn, &fs, &fh);
    t += g_credit; b += g_credit;
    return s2a_lowva_need(t, b, optional ? opt_reserve(t) : g_reserve, fn, fs, bytes, contig, why);
}

// 比例上限：可选申请要 E + bytes ≤ T − bytes − R（T 含待回落）。保留量之上的富余，可拒绝的最多占一半，另一半留给拦不到的分配。
// 10-21 巫师3 witcher3_1021192354_2：进场一批新管线让归档开到只剩 R，同时到来的拦不到的骤增（不到 1 秒，巡检和申请时的扫描都赶不上）吃光余下的。
// 超了只拒不腾：归档在 iPhone 上关片不还地址（画面·着色器线探针 witcher3_1021201918_2：放掉归档对象 2 秒后那一块原样在），腾了只是销账、再开同一片多映射一份。
// 不设常数下限，按比例随 T 缩放（丝之歌起局 T 约 750 MB 照常放行）
int s2a_lowva_over_cap(int64_t e, uint64_t bytes, uint64_t t, uint64_t r) { return e + (int64_t)bytes > (int64_t)t - (int64_t)bytes - (int64_t)r; }
static int over_cap(uint64_t bytes) {
    uint64_t t, b; scan(&t, &b); t += g_credit;
    return s2a_lowva_over_cap(capped(), bytes, t, opt_reserve(t));
}
static int api_user(const char *name, s2a_lowva_evict_fn ev, void *ctx) {
    lowva_lock();
    if (g_nuser == NUSER) die("低区账：使用者超过 %d 个（登记 %s）", NUSER, name);
    int id = g_nuser + 1; snprintf(U[id].name, sizeof U[id].name, "%s", name); U[id].evict = ev; U[id].ctx = ctx; atomic_store(&g_nuser, id);
    pthread_mutex_unlock(&g_mu); LOG("低区账：登记使用者 %d「%s」（%s腾退）", id, name, ev ? "可" : "不可"); return id;
}
static int api_acquire(int id, uint64_t bytes, uint64_t contig, int optional, const char *what) {
    if (id < 1 || id > atomic_load(&g_nuser)) die("低区账：acquire 使用者号 %d 未登记（%s）", id, what);
    if (!limited()) { atomic_fetch_add(&U[id].inflight, (int64_t)bytes); return 0; }
    lowva_lock(); const char *why;
    if (optional) {
        atomic_store(&U[id].opt, 1);
        // 只卡在比例上限：设计好的退路（调用方首遇现建），不报红；按 1、2、4、8… 次打一行
        if (over_cap(bytes)) { static uint64_t nc; uint64_t k = ++nc;
            if (!(k & (k - 1))) { LOG("低区账：「%s」申请 %llu MB（%s）不给：可拒绝的已占满保留量之上富余的一半（第 %llu 次）", U[id].name, (unsigned long long)(bytes / MB), what, (unsigned long long)k); ledger("比例上限", NULL); }
            pthread_mutex_unlock(&g_mu); return -1; }
    }
    while (shortfall(bytes, contig, optional, &why)) {
        if (!evict(shortfall(bytes, contig, optional, &why))) {
            if (optional) { static int reds; if (reds++ < 8) { LOG("【红】低区账：「%s」申请 %llu MB（%s）腾不出，这次跳过", U[id].name, (unsigned long long)(bytes / MB), what); ledger("申请跳过", why); }
                pthread_mutex_unlock(&g_mu); return -1; }
            LOG("【红】低区账：「%s」申请 %llu MB（连续 %llu MB，%s）腾不出", U[id].name, (unsigned long long)(bytes / MB), (unsigned long long)(contig / MB), what);
            ledger("申请不到", why); die("低区耗尽（卡在%s）：「%s」要 %llu MB（%s），见上一行低区账", why, U[id].name, (unsigned long long)(bytes / MB), what);
        }
    }
    atomic_fetch_add(&U[id].inflight, (int64_t)bytes); pthread_mutex_unlock(&g_mu); return 0;
}
// 无锁：开片成功后在调用方自己的锁里调也不会和巡检互锁
static void api_note(int id, int64_t d) {
    if (id < 1 || id > atomic_load(&g_nuser)) return;
    atomic_fetch_add(&U[id].held, d);
    if (d > 0) { int64_t f = atomic_load(&U[id].inflight); while (f > 0 && !atomic_compare_exchange_weak(&U[id].inflight, &f, f > d ? f - d : 0)) {} }   // 申请过的那部分转成实占
}
static void api_fail(int id, uint64_t bytes, const char *what) {
    lowva_lock(); const char *why; shortfall(0, 0, 0, &why);
    LOG("【红】低区账：「%s」申请过的 %llu MB 映射仍失败（%s）", id >= 1 && id <= atomic_load(&g_nuser) ? U[id].name : "?", (unsigned long long)(bytes / MB), what);
    ledger("映射失败", why); die("低区映射失败：%s，见上一行低区账", what);
}
static void api_snapshot(uint64_t *t, uint64_t *b, uint64_t *r, uint64_t *u, uint64_t *tr) {
    lowva_lock(); scan(t, b); *r = g_reserve; *u = untracked(*t); int64_t x = tracked(); *tr = x > 0 ? (uint64_t)x : 0; pthread_mutex_unlock(&g_mu);
}
static const s2a_lowva_api API = { sizeof(s2a_lowva_api), S2A_LOWVA_VERSION, api_user, api_acquire, api_note, api_fail, api_snapshot };
const s2a_lowva_api *s2a_lowva(void) { return &API; }

// 巡检一拍：余量不够（按 T + 待回落）主动腾退；返回下一拍间隔秒数（余量 < 2R 时 1 秒，否则 10 秒）
int s2a_lowva_tick(void) {
    lowva_lock();
    int memory_low = memory_tick();
    uint64_t t, b; scan(&t, &b); uint64_t te = t + g_credit, be = b + g_credit;
    if (te < g_reserve || be < CONTIG_FLOOR) {
        uint64_t want = te < g_reserve ? g_reserve - te : 0, wb = be < CONTIG_FLOOR ? CONTIG_FLOOR - be : 0; if (wb > want) want = wb;
        uint64_t got = evict(want);
        // 预警、不报红：这一拍只是余量低于保留量 / 连续块保底，没有任何申请失败（必需申请拿不到在 api_acquire 里报红退出，映射失败 api_fail 报红退出，
        // 崩溃另有现场）。10-21 暗黑3 d3_1021220544_2（载入骤增把学到的 R 推到 872 MB，T 594）、八方2 octopath2_1021213255_2（B 253 < 256）各一次，
        // 之后都照常到 MARK、收局，没有申请被拒以外的后果；归档登记为不可腾退后这里腾出恒为 0，红行只是把预测当成故障
        if (got < want && !g_deficit_logged) { g_deficit_logged = 1; LOG("【预警】低区账：余量低于%s，可腾退的腾出 %llu MB / 差 %llu MB（没有申请失败；真失败在申请 / 映射处报红）",
            te < g_reserve ? "保留量" : "连续块保底", (unsigned long long)(got / MB), (unsigned long long)(want / MB)); ledger("余量偏紧", "地址"); }
    } else g_deficit_logged = 0;
    // 余量 < 2R，或可拒绝的已过上限的一半（E > (T − R) / 2）时每秒一拍：拦不到的涨起来，申请那一刻的扫描要尽量新
    int next = memory_low || t < 2 * g_reserve || 2 * capped() > (int64_t)t - (int64_t)g_reserve ? 1 : SLOW_S;
    pthread_mutex_unlock(&g_mu); return next;
}
static void *watch(void *a) { s2a_thread_name("s2a-lowva-watch"); (void)a; for (int s = 0;;) { int d = s2a_lowva_tick(); s += d; if (s % 30 < d) { lowva_lock(); ledger("巡检", NULL); pthread_mutex_unlock(&g_mu); } sleep((unsigned)d); } return NULL; }
// 不设地址上限款仍检查 iOS 物理余量；地址扫描只记峰值，不学地址保留量。
int s2a_lowva_peak_tick(void) {
    lowva_lock();
    int memory_low = memory_tick();
    uint64_t t, b;
    g_scan(&t, &b);
    peak_note(t, b, lv_now());
    pthread_mutex_unlock(&g_mu);
    return memory_low ? 1 : PEAK_S;
}
static void *peak_watch(void *a) { s2a_thread_name("s2a-lowva-peak"); (void)a; for (;;) sleep((unsigned)s2a_lowva_peak_tick()); return NULL; }
// 宿主地址峰值一行（收局 / 崩溃）：只 trylock 不等锁、不分配、不扫，按标签只读已存好的快照（信号处理里也调）
void s2a_lowva_peak_report(const char *when) {
    int lk = lowva_trylock();   // 收局时拿得到就拿（峰值巡检不会写到一半）；崩溃时拿不到不等，读到半新不旧也只是诊断
    if (!g_pk_have) { LOG("宿主地址 [%s]：没扫过（巡检没起），无峰值读数", when); if (lk) pthread_mutex_unlock(&g_mu); return; }
    const char *tg = g_pk_snap[atomic_load(&g_pk_cur)].tags;
    LOG("宿主地址 [%s]：起点空洞 T0 %llu MB、最低 Tmin %llu MB（第 %llu 秒）、峰值占用 T0−Tmin %llu MB、最大一块最低 Bmin %llu MB（第 %llu 秒）；最低点按标签：%s", when,
        (unsigned long long)(g_pk_t0 / MB), (unsigned long long)(g_pk_tmin / MB), (unsigned long long)g_pk_tmin_s, (unsigned long long)((g_pk_t0 - g_pk_tmin) / MB),
        (unsigned long long)(g_pk_bmin / MB), (unsigned long long)g_pk_bmin_s, tg[0] ? tg : "（比起点低不到 64 MB，没存快照）");
    if (lk) pthread_mutex_unlock(&g_mu);
}
// 起局（C# 初始化后）调：未设地址限额时用峰值巡检，iOS 物理压力下同样缩短采样间隔。
void s2a_lowva_start(void) {
    if (!limited()) { LOG("低区账：窗口未占满，不设地址限额；常态每 %d 秒记录峰值，并检查进程内存余量", PEAK_S);
        pthread_t th; if (!pthread_create(&th, NULL, peak_watch, NULL)) { pthread_detach(th); g_peak_watch = 1; } return; }
    lowva_lock(); ledger("起账", NULL); pthread_mutex_unlock(&g_mu);
    pthread_t th; if (!pthread_create(&th, NULL, watch, NULL)) { pthread_detach(th); g_watch_started = 1; }
}
// 崩溃现场（信号处理里调，不拿锁：账面是原子量，判定状态读到旧值也只影响这一行）
void s2a_lowva_crash_note(void) { if (g_have_base) ledger("崩溃时", NULL); s2a_lowva_peak_report("崩溃"); }
// 单测：换扫描 / 钟、清状态；查巡检线程起没起
void s2a_lowva_test_reset(void (*sc)(uint64_t *, uint64_t *), uint64_t (*clk)(void)) {
    g_memory_credit = g_memory_credit_ns = 0; g_memory_previous = UINT64_MAX; g_memory_warned = 0;
    g_scan = sc ? sc : s2a_low_holes; g_now = clk; memset(U, 0, sizeof U); atomic_store(&g_nuser, 0); g_reserve = R_MIN; g_prev_u = g_prev_ns = 0; g_base_t = 0; g_base_tr = 0; g_have_base = 0; g_nrate = 0;
    g_credit = g_credit_t0 = g_credit_ns = 0; g_have_prev = g_deficit_logged = g_watch_started = 0; g_drop_t = 0;
    g_pk_have = g_peak_watch = 0; g_pk_ns0 = g_pk_t0 = g_pk_tmin = g_pk_tmin_s = g_pk_bmin = g_pk_bmin_s = 0; memset(g_pk_snap, 0, sizeof g_pk_snap); atomic_store(&g_pk_cur, 0);
}
int s2a_lowva_test_watching(void) { return g_watch_started; }
int s2a_lowva_test_peak_watching(void) { return g_peak_watch; }
const char *s2a_lowva_test_peak(uint64_t *t0, uint64_t *tmin, uint64_t *tmin_s, uint64_t *bmin, uint64_t *bmin_s) {
    *t0 = g_pk_t0; *tmin = g_pk_tmin; *tmin_s = g_pk_tmin_s; *bmin = g_pk_bmin; *bmin_s = g_pk_bmin_s; return g_pk_snap[atomic_load(&g_pk_cur)].tags;
}
void *s2a_lowva_test_mutex(void) {
#if defined(__ANDROID__)
    int error = pthread_once(&g_mu_once, lowva_mutex_init);
    if (error) die("Android 低区账测试互斥初始化失败 errno=%d", error);
#endif
    return &g_mu;
}
