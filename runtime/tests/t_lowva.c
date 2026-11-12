// 低区账单测：假扫描（空洞合计 T / 最大一块 B 由用例摆）+ 假钟 + 假归档使用者（每片 10 MB，腾一片句柄 −1；即时模式下 T、B 各 +10 MB，
// 迟放模式下映射还没真放、T 不动）；期望按 s2a_lowva.h 的规则手算（保留量 R = max(256 MB, 2 × 最近 60 秒拦不到部分单秒最大涨幅)）
#include "../src/native.h"
#include "../include/s2a_lowva.h"
#include <sys/wait.h>

#define MB (1ull << 20)
#define SEC 1000000000ull
static uint64_t T, B, CLK; static int FDN = 40; static uint64_t FDS = 256; static uint64_t WSIZE = 64ull << 30;
static uint64_t memory_headroom = UINT64_MAX;
uint64_t s2a_lowva_memory_headroom(void) { return memory_headroom; }
void s2a_low_holes(uint64_t *t, uint64_t *b) { *t = T; *b = B; }
static int g_tags_n;   // 按标签合计被调了几次（峰值快照只在 T 创新低 ≥ 64 MB 时调）
void s2a_low_tags(char *o, size_t n) { g_tags_n++; snprintf(o, n, "按标签：（单测桩第 %d 次）", g_tags_n); }
void s2a_low_files(const char *w) { (void)w; }
void s2a_window_get(uint64_t *base, uint64_t *size) { *base = 0x7000000000ull; *size = WSIZE; }
int s2a_window_ok(void) { return 1; }
uint64_t s2a_window_spare(void) { return (64ull << 30) - WSIZE; }   // 窗口在 64 GB 空洞开头：余量 = 空洞剩下的
void s2a_fd_usage(int *n, uint64_t *s, uint64_t *h) { *n = FDN; *s = FDS; *h = 10240; }
static uint64_t clk(void) { return CLK; }

static const s2a_lowva_api *A; static int me, slices, evicted, lag;
static uint64_t ev(void *ctx, uint64_t want) { (void)ctx; uint64_t got = 0;
    while (got < want && slices > 0) { slices--; evicted++; got += 10 * MB; if (!lag) { T += 10 * MB; B += 10 * MB; } FDN--; A->note(me, -(int64_t)(10 * MB)); }
    return got; }
static void setup(int n) { s2a_lowva_test_reset(s2a_low_holes, clk); A = s2a_lowva(); me = A->user("管线归档", ev, NULL);
    slices = n; evicted = 0; lag = 0; CLK = SEC; memory_headroom = UINT64_MAX;
    for (int i = 0; i < n; i++) A->note(me, 10 * MB); }   // 预置的片只记账、不走申请（申请会按当时余量腾）
static volatile int g_noted;
static void *note_th(void *a) { (void)a; A->note(me, 10 * MB); g_noted = 1; return NULL; }
static int bad;
#define CK(c, ...) do { if (!(c)) { printf("✗ "); printf(__VA_ARGS__); printf("\n"); bad++; } } while (0)

int main(void) {
    uint64_t r, u, tr, t, b; int iv = 0;
    // ① 余量够：T 1300、B 1000、保留量 256（没数据）→ 申请 10 MB 直接过、不腾
    T = 1300 * MB; B = 1000 * MB; setup(5);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "①") == 0 && evicted == 0, "① 余量够应直接过（腾了 %d 片）", evicted);
    // ② T 260：要 10 + 256 − 260 = 6 MB → 腾 1 片（10 MB）后 T 270 过（必需申请：腾退只在地址 / 句柄不够时用；可选申请此时先被比例上限拒，见 ⑳）
    T = 260 * MB; B = 1000 * MB; setup(5);
    CK(A->acquire(me, 10 * MB, 10 * MB, 0, "②") == 0 && evicted == 1, "② 应腾 1 片后过（腾 %d 片）", evicted);
    // ③ 最大一块不够：B 260 → 要 10 + 256 − 260 = 6 MB → 腾 1 片
    T = 1300 * MB; B = 260 * MB; setup(5);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "③") == 0 && evicted == 1, "③ 最大块不够应腾 1 片（腾 %d 片）", evicted);
    // ④ 没可腾的：T 200 < 256、0 片 → optional 返回 -1
    T = 200 * MB; B = 200 * MB; setup(0);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "④") == -1, "④ 腾不出 optional 应返回 -1");
    // ⑤ 腾不出且非 optional → 列账报红并中止（子进程里跑，期望 SIGABRT）
    { pid_t p = fork(); if (!p) { fclose(stdout); stdout = fopen("/dev/null", "w"); T = 200 * MB; setup(0); A->acquire(me, 10 * MB, 10 * MB, 0, "⑤"); _exit(0); }
      int st = 0; waitpid(p, &st, 0); CK(WIFSIGNALED(st) && WTERMSIG(st) == SIGABRT, "⑤ 非 optional 腾不出应 abort（状态 %#x）", st); }
    // ⑥ 句柄：软上限 256、已开 200 → 256 − 200 − 1 = 55 < 64，要降到 191 → 腾 9 片（每片 −1 句柄）后过
    T = 5000 * MB; B = 2000 * MB; FDN = 200; setup(20);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "⑥") == 0 && evicted == 9, "⑥ 句柄不够应腾 9 片后过（腾 %d 片）", evicted); FDN = 40;
    // ⑦ 迟放：回调放了强引用、映射还没真放（T 不动）。T 260：要 10 + 256 − 260 = 6 MB → 腾 1 片（待回落 10 MB）就过，不多腾、不退出
    T = 260 * MB; B = 2000 * MB; setup(10); lag = 1;
    CK(A->acquire(me, 10 * MB, 10 * MB, 0, "⑦") == 0 && evicted == 1, "⑦ 迟放应腾 1 片后过（腾 %d 片）", evicted);
    //   待回落超过 2 秒没回落就不再计入：3 秒后同样申请，T 仍 260 → 再腾 1 片
    CLK += 3 * SEC; evicted = 0;
    CK(A->acquire(me, 10 * MB, 10 * MB, 0, "⑦b") == 0 && evicted == 1, "⑦ 待回落过期后应再腾 1 片（腾 %d 片）", evicted);
    // ⑧ 保留量实测（假钟每拍 +1 秒）：第 1 拍 T 5000（起账基准）；第 2–11 拍每拍 −50 MB（拦不到每秒涨 50）、第 12 拍 −200 MB、之后不动：
    //   第 11 拍 R = max(256, 2 × 50) = 256；第 12 拍起 = 2 × 200 = 400；最近 60 秒窗口在第 72 拍滑过第 12 拍的 200 → 第 73 拍回到 256；
    //   T 4300 ≥ 2R → 间隔 10 秒
    T = 5000 * MB; B = 2000 * MB; setup(0);
    for (int i = 1; i <= 73; i++) { CLK = (uint64_t)i * SEC; if (i >= 2 && i <= 11) T -= 50 * MB; else if (i == 12) T -= 200 * MB;
        iv = s2a_lowva_tick(); A->snapshot(&t, &b, &r, &u, &tr);
        if (i == 11) CK(r == 256 * MB, "⑧ 每秒 50 MB 时保留量应为 256（%llu）", (unsigned long long)(r / MB));
        if (i == 12) CK(r == 400 * MB, "⑧ 单秒 200 MB 后保留量应为 400（%llu）", (unsigned long long)(r / MB));
        if (i == 72) CK(r == 400 * MB, "⑧ 60 秒内仍按 200 记、应为 400（%llu）", (unsigned long long)(r / MB));
        if (i == 73) CK(r == 256 * MB && iv == 10, "⑧ 滑出 60 秒后应回 256、间隔 10 秒（%llu MB、%d 秒）", (unsigned long long)(r / MB), iv); }
    // ⑨ 巡检主动腾：保留量 256、T 200（缺 56 MB）、持 10 片 → 一拍腾 6 片（60 MB）、T 到 260；200 < 2 × 256 → 下一拍间隔 1 秒
    T = 200 * MB; B = 2000 * MB; setup(10); iv = s2a_lowva_tick();
    CK(evicted == 6 && T == 260 * MB && iv == 1, "⑨ 巡检应腾 6 片、T 到 260 MB、间隔 1 秒（腾 %d 片、T %llu、%d 秒）", evicted, (unsigned long long)(T / MB), iv);
    // ⑩ 拦不到部分按起账基准：起账 T 200、账面 100 MB；腾 6 片后 T 260、账面 40 → U = (200 − 260) − (40 − 100) = 0（腾退本身不算拦不到）
    A->snapshot(&t, &b, &r, &u, &tr);
    CK(tr == 40 * MB && u == 0, "⑩ 账面应 40 MB、拦不到 0（%llu / %llu MB）", (unsigned long long)(tr / MB), (unsigned long long)(u / MB));
    // ⑪ note 无锁：本线程持着账本锁（巡检持锁调回调的情形）时，别的线程 note 照样返回
    { pthread_mutex_t *m = (pthread_mutex_t *)s2a_lowva_test_mutex(); pthread_t th; g_noted = 0;
      pthread_mutex_lock(m); pthread_create(&th, NULL, note_th, NULL);
      for (int i = 0; i < 200 && !g_noted; i++) usleep(5000);
      int ok = g_noted; pthread_mutex_unlock(m); pthread_join(th, NULL);
      CK(ok, "⑪ 持账本锁时别的线程 note 应不阻塞"); }
    // ⑭ 10-21 丝之歌 silksong_1021154925_1 原数：起账 T 1160、B 896；写跟踪快照池登记 32 MB（不可腾退）；之后 20 秒里拦不到的涨到 T 751 / B 545（每秒约 20 MB）；
    //   再开 6 片归档（4.8 MB 一片，共 28.6 MB）。期望：拦不到 = (1160 − 751) − 32 = 377 MB（改前算成 453 GB），R = max(256, 2 × ~20) = 256，
    //   6 片全放行（751 − 28.6 = 722 ≥ 256、545 − 4.8 ≥ 256），一片都不拒。改前初值 768 > 751：全拒（反证）
    { s2a_lowva_test_reset(s2a_low_holes, clk); A = s2a_lowva(); T = 1160 * MB; B = 896 * MB; CLK = SEC; FDN = 20;
      int arch = A->user("管线归档", ev, NULL), snap = A->user("写跟踪快照池", NULL, NULL); me = arch; slices = 0; evicted = 0;
      s2a_lowva_tick(); A->note(snap, 32 * MB); T -= 32 * MB;
      for (int i = 2; i <= 21; i++) { CLK = (uint64_t)i * SEC; T -= (uint64_t)((1128.0 - 751) / 20 * MB); B = 545 * MB; s2a_lowva_tick(); }
      T = 751 * MB; int rej = 0; uint64_t sz = (uint64_t)(4.77 * MB);
      for (int k = 0; k < 6; k++) { if (A->acquire(arch, sz, sz, 1, "丝之歌片") == 0) { A->note(arch, (int64_t)sz); T -= sz; B -= sz; } else rej++; }
      A->snapshot(&t, &b, &r, &u, &tr);
      CK(rej == 0, "⑭ 丝之歌 6 片应全放行（拒 %d 片，保留量 %llu MB）", rej, (unsigned long long)(r / MB));
      CK(r == 256 * MB, "⑭ 丝之歌保留量应为 256（%llu）", (unsigned long long)(r / MB));
      CK(u / MB >= 370 && u / MB <= 380, "⑭ 拦不到应约 (1160 − 751) − 32 = 377 MB（实为 %llu MB）", (unsigned long long)(u / MB)); FDN = 40; }
    // ⑱ 10-21 巫师3 witcher3_1021192354_2 原数：第 60 秒 T 1295、R 478（前一秒拦不到的涨 239 MB → 2 × 239）、归档已开 70 MB；归档登记为不可腾退
    //   （iPhone 上关片不还地址，画面·着色器线探针 witcher3_1021201918_2），进场连开 100 片 10 MB（可选申请）。期望：E + 10 ≤ T − 10 − 478，
    //   E = 70 + 10k、T = 1295 − 10k；保留量按 max(256, min(R 478, T/2))：T ≥ 956 时 478，之后 T/2。逐片：k ≤ 33 时按 478 放；
    //   k = 34–37（T 955 / 945 / 935 / 925，保留 477 / 472 / 467 / 462）都满足 E + 10 ≤ T − 10 − 保留；k = 38（T 915、保留 457）：460 > 448 → 拒。
    //   → 放 38 片（E 450、T 915），后 62 片拒、不腾。T 915 之后拦不到的骤增 550 MB 还剩 365。
    //   改前只判「T − 片 ≥ R」：开到 T 485、放 81 片（反证）
    { s2a_lowva_test_reset(s2a_low_holes, clk); A = s2a_lowva(); T = 1534 * MB; B = 2000 * MB; CLK = SEC; FDN = 40;
      int arch = A->user("管线归档", NULL, NULL); A->note(arch, 70 * MB); s2a_lowva_tick(); CLK = 2 * SEC; T = 1295 * MB; B = 766 * MB; s2a_lowva_tick();
      A->snapshot(&t, &b, &r, &u, &tr); CK(r == 478 * MB, "⑱ 保留量应学到 478（%llu）", (unsigned long long)(r / MB));
      int ok = 0, rej = 0;
      for (int k = 0; k < 100; k++) { if (A->acquire(arch, 10 * MB, 10 * MB, 1, "巫师3片") == 0) { A->note(arch, (int64_t)(10 * MB)); T -= 10 * MB; ok++; } else rej++; }
      A->snapshot(&t, &b, &r, &u, &tr);
      CK(ok == 38 && rej == 62 && tr == 450 * MB && T == 915 * MB, "⑱ 应放 38 拒 62、账面 450、T 915（放 %d 拒 %d、账面 %llu、T %llu）", ok, rej,
         (unsigned long long)(tr / MB), (unsigned long long)(T / MB));
      // ⑲ 必需申请（optional = 0，如宿主线程栈）不受比例上限，照「T − 申请 ≥ R」判：925 − 100 ≥ 478 → 过
      int hard = A->user("宿主线程栈", NULL, NULL);
      CK(A->acquire(hard, 100 * MB, 1 * MB, 0, "⑲") == 0, "⑲ 必需申请不受比例上限，应过"); }
    // ㉑ 10-21 暗黑3 冷启动（画面·着色器线 d3_1021224951_2 等三局）：载入时拦不到的每秒涨 500 MB → R = 1000，空洞 T 600、归档已开 150 MB。
    //   可选申请的保留量 = max(256, min(1000, 300)) = 300：1 MB 片 151 ≤ 600 − 1 − 300 = 299 → 放；再 6 MB 片 157 ≤ 599 − 6 − 300 = 293 → 放。
    //   空洞降到 T 420（保留 = max(256, min(1000, 210)) = 256）：E 157，6 MB 片 163 ≤ 420 − 6 − 256 = 158？否 → 拒；1 MB 片 158 ≤ 163 → 放。
    //   改前按 R 1000 判，T − R 为负，三片全拒（反证）
    { s2a_lowva_test_reset(s2a_low_holes, clk); A = s2a_lowva(); T = 1100 * MB; B = 700 * MB; CLK = SEC; FDN = 40;
      int arch = A->user("管线归档", NULL, NULL); A->note(arch, 150 * MB); s2a_lowva_tick(); CLK = 2 * SEC; T = 600 * MB; s2a_lowva_tick();
      A->snapshot(&t, &b, &r, &u, &tr); CK(r == 1000 * MB, "㉑ 保留量应学到 1000（%llu）", (unsigned long long)(r / MB));
      int g1 = A->acquire(arch, 1 * MB, 1 * MB, 1, "暗黑3 小片"); if (!g1) { A->note(arch, MB); T -= MB; }
      int g2 = A->acquire(arch, 6 * MB, 6 * MB, 1, "暗黑3 片"); if (!g2) { A->note(arch, 6 * MB); T -= 6 * MB; }
      T = 420 * MB;
      int g3 = A->acquire(arch, 6 * MB, 6 * MB, 1, "暗黑3 片（空洞 420）");
      int g4 = A->acquire(arch, 1 * MB, 1 * MB, 1, "暗黑3 小片（空洞 420）");
      CK(g1 == 0 && g2 == 0 && g3 == -1 && g4 == 0, "㉑ 载入期应放 1 / 6 MB、空洞 420 时拒 6 放 1（%d %d %d %d）", g1, g2, g3, g4); }
    // ⑳ 比例上限只拒不腾：可腾退使用者（预置 30 片 300 MB）做可选申请，T 700、R 256 → 300 + 10 > 690 − 256 = 434？否 → 过；
    //   再把 T 压到 500：310 + 10 > 490 − 256 = 234 → 拒，腾退回调 0 次（地址本身够：500 ≥ 266）；巡检一拍同样不腾
    T = 700 * MB; B = 2000 * MB; setup(30);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "⑳a") == 0 && evicted == 0, "⑳ 比例内应直接过（腾 %d）", evicted);
    A->note(me, 10 * MB); T = 500 * MB; evicted = 0;
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "⑳b") == -1 && evicted == 0, "⑳ 超比例应拒且不腾（腾 %d）", evicted);
    s2a_lowva_tick(); CK(evicted == 0, "⑳ 巡检不为比例上限腾（腾 %d）", evicted);
    // ㉒ 宿主地址峰值（峰值巡检一拍 5 秒，直接调 s2a_lowva_peak_tick）：假扫描依次 T 8000 / 7000 / 7500 / 6000 / 6100 MB、B 3000 / 2500 / 2600 / 2700 / 2000 MB，
    //   假钟第 0 / 5 / 10 / 15 / 20 秒（相对第一次扫描）。手算：T0 = 8000；Tmin = 6000 在第 15 秒；峰值占用 T0 − Tmin = 2000；Bmin = 2000 在第 20 秒；间隔 5 秒。
    //   按标签快照（基准起点 8000，起点本身不存）：7000 比基准低 1000 ≥ 64 → 存第 1 份（基准 7000）；7500 不是新低；6000 比 7000 低 1000 → 存第 2 份（基准 6000）；
    //   6100 不是新低 → 共调 2 次、当前是第 2 份。
    //   再降到 5950（第 25 秒）：Tmin 刷新为 5950 / 第 25 秒，但比基准 6000 只低 50 < 64 → 不重存（仍 2 次、仍第 2 份）；
    //   再到 5936（第 30 秒）：比 6000 低 64 ≥ 64 → 存第 3 份（边界含等号）。
    //   峰值巡检只记峰值：T 100 远低于保留量 256 时也不腾（预置 5 片、腾 0 片）
    { static const uint64_t TS[] = {8000, 7000, 7500, 6000, 6100}, BS[] = {3000, 2500, 2600, 2700, 2000};
      uint64_t t0 = 0, tmin = 0, tmin_s = 0, bmin = 0, bmin_s = 0; const char *tg; setup(5); g_tags_n = 0;
      for (int i = 0; i < 5; i++) { CLK = SEC + (uint64_t)i * 5 * SEC; T = TS[i] * MB; B = BS[i] * MB; iv = s2a_lowva_peak_tick();
          if (!i) { tg = s2a_lowva_test_peak(&t0, &tmin, &tmin_s, &bmin, &bmin_s); CK(!tg[0] && g_tags_n == 0, "㉒ 起点不应存快照（调 %d 次、串「%s」）", g_tags_n, tg); } }
      tg = s2a_lowva_test_peak(&t0, &tmin, &tmin_s, &bmin, &bmin_s);
      CK(t0 == 8000 * MB && tmin == 6000 * MB && tmin_s == 15 && t0 - tmin == 2000 * MB && bmin == 2000 * MB && bmin_s == 20 && iv == 5,
         "㉒ 应 T0 8000、Tmin 6000 第 15 秒、峰值占用 2000、Bmin 2000 第 20 秒、间隔 5（%llu、%llu 第 %llu 秒、%llu、%llu 第 %llu 秒、%d）",
         (unsigned long long)(t0 / MB), (unsigned long long)(tmin / MB), (unsigned long long)tmin_s, (unsigned long long)((t0 - tmin) / MB),
         (unsigned long long)(bmin / MB), (unsigned long long)bmin_s, iv);
      CK(g_tags_n == 2 && !strcmp(tg, "按标签：（单测桩第 2 次）"), "㉒ 应存 2 次快照、当前第 2 份（调 %d 次、串「%s」）", g_tags_n, tg);
      CLK = SEC + 25 * SEC; T = 5950 * MB; s2a_lowva_peak_tick(); tg = s2a_lowva_test_peak(&t0, &tmin, &tmin_s, &bmin, &bmin_s);
      CK(tmin == 5950 * MB && tmin_s == 25 && g_tags_n == 2 && !strcmp(tg, "按标签：（单测桩第 2 次）"),
         "㉒ 降 50 MB 应刷新 Tmin 5950 第 25 秒、不重存快照（%llu 第 %llu 秒、调 %d 次、串「%s」）", (unsigned long long)(tmin / MB), (unsigned long long)tmin_s, g_tags_n, tg);
      CLK = SEC + 30 * SEC; T = 5936 * MB; s2a_lowva_peak_tick(); tg = s2a_lowva_test_peak(&t0, &tmin, &tmin_s, &bmin, &bmin_s);
      CK(tmin_s == 30 && g_tags_n == 3 && !strcmp(tg, "按标签：（单测桩第 3 次）"), "㉒ 比上份低满 64 MB 应重存（第 %llu 秒、调 %d 次、串「%s」）", (unsigned long long)tmin_s, g_tags_n, tg);
      CLK = SEC + 35 * SEC; T = 100 * MB; s2a_lowva_peak_tick(); CK(evicted == 0, "㉒ 峰值巡检不应腾（腾 %d 片）", evicted);
      s2a_lowva_peak_report("单测"); }
    // ㉓ 10-26 双人成行 itt_r2 原数（host.log 行 1099）：T 642、B 178、学到的 R 481、可拒绝的 E（命令分配器）5 MB，命令分配器申请 5 MB、不要连续（contig 0）。
    //   手算：可选保留 = max(256, min(481, 642/2 = 321)) = 321；比例上限 5 + 5 ≤ 642 − 5 − 321 = 316 → 过；合计 642 ≥ 5 + 321 → 过；
    //   contig 0 不看最大一块 → 缺口 0、放行。改前连续块项 256 − 178 = 78 MB、无人可腾 → 拒（反证）。
    //   同一实数下要连续的 5 MB（如归档片）：178 < 5 + 256 → 缺口 83 MB 照旧拒（保底对要连续的申请不放松）
    { const char *w; uint64_t ro = s2a_lowva_opt_reserve(481 * MB, 642 * MB);
      CK(ro == 321 * MB, "㉓ 可选保留应 321（%llu）", (unsigned long long)(ro / MB));
      CK(!s2a_lowva_over_cap(5 * MB, 5 * MB, 642 * MB, ro), "㉓ 比例上限应过（10 ≤ 316）");
      uint64_t n0 = s2a_lowva_need(642 * MB, 178 * MB, ro, 39, 10240, 5 * MB, 0, &w);
      CK(n0 == 0 && !w, "㉓ contig 0 的 5 MB 应放行（缺口 %llu MB、%s）", (unsigned long long)(n0 / MB), w ? w : "无");
      uint64_t n1 = s2a_lowva_need(642 * MB, 178 * MB, ro, 39, 10240, 5 * MB, 5 * MB, &w);
      CK(n1 == 83 * MB && w && !strcmp(w, "地址"), "㉓ 要连续的 5 MB 应缺 83 MB、卡在地址（%llu MB、%s）", (unsigned long long)(n1 / MB), w ? w : "无");
      // 收局前最低处（行 1302：T 580、B 172）：可选保留 290，5 + 5 ≤ 580 − 5 − 290 = 285、580 ≥ 295 → 放
      ro = s2a_lowva_opt_reserve(481 * MB, 580 * MB);
      CK(ro == 290 * MB && !s2a_lowva_over_cap(9 * MB, 5 * MB, 580 * MB, ro) && s2a_lowva_need(580 * MB, 172 * MB, ro, 39, 10240, 5 * MB, 0, &w) == 0,
         "㉓ T 580 / B 172 时 contig 0 的 5 MB 应放行（保留 %llu）", (unsigned long long)(ro / MB));
      // 整条申请路径：本局登记的两家都不可腾退（写跟踪快照池 32 MB、命令分配器 5 MB），起账 T 943 → 1 秒后 T 642（拦不到 264 MB / 秒 → R 528，可选保留封顶 321）、B 178
      s2a_lowva_test_reset(s2a_low_holes, clk); A = s2a_lowva(); T = 943 * MB; B = 468 * MB; CLK = SEC; FDN = 39;
      int snap = A->user("写跟踪快照池", NULL, NULL), ca = A->user("命令分配器", NULL, NULL); s2a_lowva_tick();
      A->note(snap, 32 * MB); A->note(ca, 5 * MB); CLK = 2 * SEC; T = 642 * MB; B = 178 * MB; s2a_lowva_tick();
      A->snapshot(&t, &b, &r, &u, &tr);
      int ok = 0; for (int k = 0; k < 20; k++) if (A->acquire(ca, 5 * MB, 0, 1, "㉓ 命令分配器") == 0) { A->note(ca, 5 * MB); A->note(ca, -(int64_t)(5 * MB)); ok++; }
      CK(u == 264 * MB && r == 528 * MB && ok == 20, "㉓ 拦不到 264、R 528 时 20 次 contig 0 申请应全放（拦不到 %llu、R %llu、放 %d）",
         (unsigned long long)(u / MB), (unsigned long long)(r / MB), ok);
      CK(A->acquire(ca, 5 * MB, 5 * MB, 1, "㉓ 要连续") == -1, "㉓ 同状态下要连续的 5 MB 无人可腾应拒"); FDN = 40; }
    // 物理余量与地址空洞独立：512 MiB 保留量，452 MiB 可用应腾 60 MiB。
    T = 5000 * MB; B = 2000 * MB; setup(10); memory_headroom = 452 * MB;
    iv = s2a_lowva_tick();
    CK(evicted == 6 && iv == 1, "物理余量 452 MiB 应腾 60 MiB、每秒巡检（%d、%d）", evicted, iv);
    CLK += SEC; memory_headroom = 482 * MB; s2a_lowva_tick();
    CK(evicted == 6, "回落 30 MiB、仍待回落 30 MiB 时不应重复腾退（%d）", evicted);
    CLK += 2 * SEC; s2a_lowva_tick();
    CK(evicted == 9, "待回落过期仍差 30 MiB 时应再腾 3 片（%d）", evicted);
    T = 5000 * MB; B = 2000 * MB; FDN = 100; setup(60); memory_headroom = 0;
    s2a_lowva_tick();
    CK(evicted == 52, "物理余量为零是有效读数，应腾至少 512 MiB（%d）", evicted);
    FDN = 40;
    T = 5000 * MB; B = 2000 * MB; setup(10); memory_headroom = 512 * MB;
    s2a_lowva_tick(); CK(evicted == 0, "达到物理保留量时不应腾退（%d）", evicted);
    T = 5000 * MB; B = 2000 * MB; setup(0); memory_headroom = 100 * MB;
    CK(s2a_lowva_tick() == 1, "无可腾资源时仍应每秒观察物理余量");
    WSIZE = 32ull << 30; T = 5000 * MB; B = 2000 * MB; setup(10);
    memory_headroom = 452 * MB; iv = s2a_lowva_peak_tick();
    CK(evicted == 6 && iv == 1, "不设地址上限的峰值巡检也应处理物理压力（%d、%d）", evicted, iv);
    memory_headroom = UINT64_MAX; iv = s2a_lowva_peak_tick();
    CK(evicted == 6 && iv == 5, "物理余量未知时恢复原峰值巡检间隔（%d、%d）", evicted, iv);
    WSIZE = 64ull << 30; FDN = 40; T = 200 * MB; B = 2000 * MB; setup(10);
    memory_headroom = 452 * MB; s2a_lowva_tick();
    CK(evicted == 6 && T == 260 * MB, "物理与地址同时不足时，同一批腾退应满足两者（%d）", evicted);
    FDN = 40;
    // ⑫ 不占满窗口（尾部已还给系统）：不设限（T 100 也直接过）、起账不起巡检线程，只起峰值巡检
    WSIZE = 32ull << 30; T = 100 * MB; B = 50 * MB; setup(3);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "⑫") == 0 && evicted == 0, "⑫ 窗口未占满应不设限（腾 %d 片）", evicted);
    s2a_lowva_start(); CK(!s2a_lowva_test_watching(), "⑫ 窗口未占满不应起巡检线程");
    CK(s2a_lowva_test_peak_watching(), "⑫ 窗口未占满应起峰值巡检线程");
    // ⑬ 占满窗口：起账起巡检线程（正对照），不另起峰值巡检（巡检的每次扫描已记峰值）
    WSIZE = 64ull << 30; T = 5000 * MB; B = 2000 * MB; setup(0);
    s2a_lowva_start(); CK(s2a_lowva_test_watching(), "⑬ 窗口占满应起巡检线程");
    CK(!s2a_lowva_test_peak_watching(), "⑬ 窗口占满不应另起峰值巡检线程");
    // ⑮ 缩尾部后的占满窗口款（10-21）：窗口用到 63 GB + 258 MB、还给系统约 766 MB（< 4 GB）→ 仍设限、起巡检；T 200 < 256 时 optional 申请腾不出返回 -1
    WSIZE = 63ull * (1ull << 30) + 258 * MB; T = 200 * MB; B = 200 * MB; setup(0);
    CK(A->acquire(me, 10 * MB, 10 * MB, 1, "⑮") == -1, "⑮ 缩尾部后仍应设限（余量不够返回 -1）");
    s2a_lowva_start(); CK(s2a_lowva_test_watching(), "⑮ 缩尾部后仍应起巡检线程"); WSIZE = 64ull << 30;
    printf("%s t_lowva：%d 处不符\n", bad ? "✗" : "✓", bad);
    return bad != 0;
}
