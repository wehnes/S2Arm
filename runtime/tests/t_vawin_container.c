// t_vawin_container：多款容器构造期窗口需求（vawin.c s2a_window_container_need，启动器线 11-07）——宿主自己对 <App>/Games/ 下每一款按单款同一个 need_dir 算、取最大，
//   不再读组装期写的窗口表。链生产同一份 svc_mem.c / loader.c / layout.c / programs.c（Mac 口径：非 FAR 补丁区长度取 <名>.patched.bin），另链 imgpack.c 测 iOS 用的只读偏移表。
//   期望全部按 runtime/src/layout.c 公式手算（与 tests/test_ship_ext.py ContainerTest 同一组夹具），不取被测输出：
//     模块 main：PATCH_OFF 0xC000 ≥ 0 → 跨度 = 圆整 16K(patched.bin 0xD000) = 0x10000 → 按 2 MB 取整 = 2 MB
//     A：类型 3、SystemResourceSize 0（堆模式）→ 32 GB + 2 MB = 32770 MB
//     B：类型 3、SystemResourceSize 0x1000（VAMM）→ 别名 63 GB + 2 MB + 栈 2 GB + 堆（应用池 0xCD500000 按 2 MB 向下 = 3284 MB）+ 共享余量 96 MB + 模块 2 MB = 69944 MB
//     D：同 B 但 ACID +0x300 处是 "ACID"（Switch 2，应用池 9 GiB = 9216 MB）→ 64512 + 2 + 2048 + 9216 + 96 + 2 = 75876 MB
//     C：类型 1（36 位）
//   ① 单款（子进程，构造函数按 argv[1] 走 need_dir）：A → 32770 MB、B → 69944 MB（单款口径不变）
//   ② 容器 {A, B} → 69944 MB；{A} → 32770 MB
//   ③ 容器 {B, D} → 75876 MB，算完应用池放回 0xCD500000；之后容器 {B} 仍 69944 MB（D 的 9 GiB 池没带进别款）
//   ④ 容器 {A, C}（类型 3 与 1 混装）→ 0，红行「地址空间类型不一致」；空 Games/ → 0，红行「下没有游戏」；某款缺 main.npdm → 0
//   ⑤ 只读偏移表 s2a_imgpack_index：embed.py 出的包里 main 的 x1 块长 0x4000（[0xC000, 0x10000)，同 test_ship_ext EmbedExtTest 手算）；包不在 → S2A_IMG_ENOFILE
#include "../src/native.h"
#include "../src/imgpack.h"
#include <fcntl.h>
#include <spawn.h>
#include <sys/stat.h>
#include <sys/wait.h>
extern char **environ;
uint64_t s2a_window_container_need(const char *bundle);   // vawin.c
uint64_t s2a_app_pool_native(void);
uint64_t s2a_npdm_window_need(const char *npdm);
static int bad;
static void ck(int ok, const char *what) { printf("%s %s\n", ok ? "✓" : "✗", what); if (!ok) bad++; }
static void put(const char *path, const void *b, size_t n) { FILE *f = fopen(path, "wb"); if (!f) { perror(path); exit(1); } fwrite(b, 1, n, f); fclose(f); }
// 一款：<dir>/main.npdm（类型 / 系统资源 / 是否 Switch 2）+ main 模块（fixups 表头 + patched.bin 0xD000 字节）
static void game(const char *dir, int as_type, uint32_t sysres, int ounce) {
    mkdir(dir, 0755); char p[1200];
    uint8_t m[0x500] = {0}; memcpy(m, "META", 4); m[0x0C] = (uint8_t)(as_type << 1);
    memcpy(m + 0x14, &sysres, 4); uint32_t stk = 0x100000, aci = 0x80, acid = ounce ? 0x100 : 0; memcpy(m + 0x1C, &stk, 4); memcpy(m + 0x70, &aci, 4); memcpy(m + 0x78, &acid, 4);
    memcpy(m + 0x80, "ACI0", 4); if (ounce) memcpy(m + 0x100 + 0x300, "ACID", 4);
    snprintf(p, sizeof p, "%s/main.npdm", dir); put(p, m, sizeof m);
    static uint8_t blob[0xD000]; for (size_t i = 0; i < sizeof blob; i++) blob[i] = (uint8_t)(i * 7);
    snprintf(p, sizeof p, "%s/main.patched.bin", dir); put(p, blob, sizeof blob);
    const char *fx = "# TEXT_END 0x5000\n# PATCH_OFF 0xc000\n# KEY_PAGE_OFF 0x8000\n# KEY_PAGE_SIZE 0x4000\n";
    snprintf(p, sizeof p, "%s/main.fixups.tsv", dir); put(p, fx, strlen(fx));
}
static void bundle(const char *b, const char *const *gids, const int *kind, int n) {   // kind：0 = A、1 = B、2 = C、3 = D、4 = 缺 main.npdm
    char p[1200]; mkdir(b, 0755); snprintf(p, sizeof p, "%s/Games", b); mkdir(p, 0755);
    for (int i = 0; i < n; i++) {
        snprintf(p, sizeof p, "%s/Games/%s", b, gids[i]);
        if (kind[i] == 0) game(p, 3, 0, 0); else if (kind[i] == 1) game(p, 3, 0x1000, 0); else if (kind[i] == 2) game(p, 1, 0, 0); else if (kind[i] == 3) game(p, 3, 0x1000, 1);
        else { game(p, 3, 0, 0); char q[1300]; snprintf(q, sizeof q, "%s/main.npdm", p); unlink(q); }
    }
}
static char g_log[16384];
static uint64_t ctr(const char *b, const char *tmp) {   // 调被测函数，期间 stderr（LOG）进文件，读回 g_log
    char lp[1200]; snprintf(lp, sizeof lp, "%s/ctr.log", tmp);
    fflush(stderr); int keep = dup(2), fd = open(lp, O_WRONLY | O_CREAT | O_TRUNC, 0644); dup2(fd, 2); close(fd);
    uint64_t r = s2a_window_container_need(b);
    fflush(stderr); dup2(keep, 2); close(keep);
    FILE *f = fopen(lp, "r"); size_t k = f ? fread(g_log, 1, sizeof g_log - 1, f) : 0; if (f) fclose(f); g_log[k] = 0;
    return r >> 20;
}
static unsigned long long single(const char *self, const char *dir) {   // 子进程：构造函数按 argv[1] = dir 算（单款路径），回 s2a_window_need 的跨度（MB）
    char out[1200]; snprintf(out, sizeof out, "%s/need.txt", dir);
    posix_spawn_file_actions_t fa; posix_spawn_file_actions_init(&fa);
    posix_spawn_file_actions_addopen(&fa, 1, out, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    posix_spawn_file_actions_addopen(&fa, 2, "/dev/null", O_WRONLY, 0);
    char *av[] = {(char *)self, (char *)dir, "child", NULL}; pid_t p; int st = -1;
    if (posix_spawn(&p, self, &fa, NULL, av, environ) || waitpid(p, &st, 0) != p) st = -1;
    posix_spawn_file_actions_destroy(&fa);
    FILE *f = fopen(out, "r"); unsigned long long v = 0; if (!f || fscanf(f, "%llu", &v) != 1) v = 0; if (f) fclose(f);
    return v;
}
// ⑥ 解包专用局（S2A_PACK_APPLY_ONLY=1）构造期不占窗口（解包局用不到客体内存；11-07「匿名窗口拖慢解包」的归因已证否，见 vawin.c）：子进程带 / 不带这个变量各起一次，
//   读 s2a_window_ok 与窗口长度。期望：带 → 0 / 0；不带（对照）→ 窗口照占（1、长度 > 0）
static int winok(const char *self, const char *dir, int apply_only, unsigned long long *size_mb) {
    char out[1200]; snprintf(out, sizeof out, "%s/winok.txt", dir);
    posix_spawn_file_actions_t fa; posix_spawn_file_actions_init(&fa);
    posix_spawn_file_actions_addopen(&fa, 1, out, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    posix_spawn_file_actions_addopen(&fa, 2, "/dev/null", O_WRONLY, 0);
    if (apply_only) setenv("S2A_PACK_APPLY_ONLY", "1", 1); else unsetenv("S2A_PACK_APPLY_ONLY");
    char *av[] = {(char *)self, (char *)dir, "winok", NULL}; pid_t p; int st = -1;
    if (posix_spawn(&p, self, &fa, NULL, av, environ) || waitpid(p, &st, 0) != p) st = -1;
    posix_spawn_file_actions_destroy(&fa); unsetenv("S2A_PACK_APPLY_ONLY");
    FILE *f = fopen(out, "r"); int ok = -1; *size_mb = 0; if (!f || fscanf(f, "%d %llu", &ok, size_mb) != 2) ok = -1; if (f) fclose(f);
    return ok;
}
static int reduced_budget(void) {
    char tmp[] = "/tmp/t_vawin_budget.XXXXXX";
    if (!mkdtemp(tmp)) return 1;
    char path[1200];
    const char *ids[] = {"0100000000020000", "0100000000040000"};
    ck(s2a_app_pool() == 2048ull << 20, "reduced budget is active");
    for (int order = 0; order < 2; order++) {
        snprintf(path, sizeof path, "%s/mix%d", tmp, order);
        const int kinds[] = {order ? 3 : 1, order ? 1 : 3};
        bundle(path, ids, kinds, 2);
        ck(ctr(path, tmp) == 68708, "mixed container uses 2048 MiB pool in both game orders");
        ck(s2a_app_pool_native() == 0xCD500000ull, "container restores native capacity independently of budget");
        ck(s2a_app_pool() == 2048ull << 20, "container keeps effective budget");
    }
    snprintf(path, sizeof path, "%s/switch1", tmp);
    bundle(path, ids, (const int[]){1}, 1);
    ck(ctr(path, tmp) == 68708 && s2a_app_pool_native() == 0xCD500000ull, "Switch container after mixed scan has correct native pool");
    snprintf(path, sizeof path, "%s/mix1/Games/%s/main.npdm", tmp, ids[0]);
    ck(s2a_npdm_window_need(path) == 68708ull << 20 && s2a_app_pool_native() == 9ull << 30, "Switch 2 NPDM selects its native pool");
    snprintf(path, sizeof path, "%s/mix1/Games/%s/main.npdm", tmp, ids[1]);
    ck(s2a_npdm_window_need(path) == 68708ull << 20 && s2a_app_pool_native() == 0xCD500000ull, "Switch NPDM after Switch 2 restores its own native pool");
    snprintf(path, sizeof path, "rm -rf '%s'", tmp); if (system(path)) {}
    printf("%s reduced-budget container: %d failures\n", bad ? "FAIL" : "PASS", bad);
    return bad != 0;
}
int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--budget")) return reduced_budget();
    if (argc == 3 && !strcmp(argv[2], "winok")) { uint64_t base, size; s2a_window_get(&base, &size); printf("%d %llu\n", s2a_window_ok(), (unsigned long long)(size >> 20)); return 0; }
    if (argc == 3 && !strcmp(argv[2], "child")) { uint64_t nd, fit; s2a_window_need(&nd, &fit); printf("%llu\n", (unsigned long long)(nd >> 20)); return 0; }
    unsetenv("S2A_WIN_NEED_MB"); unsetenv("S2A_VAWIN_NORESERVE"); unsetenv("S2A_VA_CAP_MB"); unsetenv("S2A_VA_IOS26");
    char tmp[] = "/tmp/t_vawin_container.XXXXXX"; if (!mkdtemp(tmp)) { printf("✗ mkdtemp\n"); return 1; }
    char b[1200], p[1300];
    const char *A = "0100000000010000", *B = "0100000000020000", *C = "0100000000030000", *D = "0100000000040000";
    // ① 单款
    snprintf(b, sizeof b, "%s/s", tmp); bundle(b, (const char *[]){A, B}, (const int[]){0, 1}, 2);
    snprintf(p, sizeof p, "%s/Games/%s", b, A); unsigned long long sa = single(argv[0], p);
    snprintf(p, sizeof p, "%s/Games/%s", b, B); unsigned long long sb = single(argv[0], p);
    printf("  单款 A %llu MB、B %llu MB\n", sa, sb);
    ck(sa == 32770 && sb == 69944, "① 单款（构造函数按模块目录）：A 32770 MB、B 69944 MB，口径不变");
    // ⑥
    { unsigned long long sz_on = 0, sz_off = 0; snprintf(p, sizeof p, "%s/Games/%s", b, A);
      int on = winok(argv[0], p, 1, &sz_on), off = winok(argv[0], p, 0, &sz_off);
      printf("  解包专用局 窗口 %d / %llu MB；对照 %d / %llu MB\n", on, sz_on, off, sz_off);
      ck(on == 0 && sz_on == 0 && off == 1 && sz_off > 0, "⑥ 解包专用局（S2A_PACK_APPLY_ONLY=1）构造期不占窗口；不带时照占（对照）"); }
    // ②
    uint64_t pool0 = s2a_app_pool(), r;
    snprintf(b, sizeof b, "%s/ab", tmp); bundle(b, (const char *[]){A, B}, (const int[]){0, 1}, 2);
    r = ctr(b, tmp); printf("  容器 {A, B} %llu MB\n", (unsigned long long)r);
    ck(r == 69944 && strstr(g_log, "2 款取最大 69944 MB"), "② 容器 {A, B}：取最大 69944 MB");
    snprintf(b, sizeof b, "%s/a", tmp); bundle(b, (const char *[]){A}, (const int[]){0}, 1);
    ck(ctr(b, tmp) == 32770, "② 容器 {A}：32770 MB");
    // ③
    snprintf(b, sizeof b, "%s/bd", tmp); bundle(b, (const char *[]){B, D}, (const int[]){1, 3}, 2);
    r = ctr(b, tmp); printf("  容器 {B, D} %llu MB，算完应用池 %#llx（算前 %#llx）\n", (unsigned long long)r, (unsigned long long)s2a_app_pool(), (unsigned long long)pool0);
    ck(r == 75876, "③ 容器 {B, D（Switch 2）}：75876 MB");
    ck(pool0 == 0xCD500000ull && s2a_app_pool() == pool0, "③ 算完应用池放回 0xCD500000（D 的 9 GiB 不留下）");
    { uint64_t s2a_window_container_pool(void); ck(s2a_window_container_pool() == 9216ull << 20, "③ 文件后备按包内最大的池判：{B, D} 记 9 GiB（#103）"); }
    snprintf(b, sizeof b, "%s/b", tmp); bundle(b, (const char *[]){B}, (const int[]){1}, 1);
    ck(ctr(b, tmp) == 69944, "③ 之后容器 {B}：仍 69944 MB");
    // ④
    snprintf(b, sizeof b, "%s/ac", tmp); bundle(b, (const char *[]){A, C}, (const int[]){0, 2}, 2);
    r = ctr(b, tmp);
    ck(r == 0 && strstr(g_log, "地址空间类型不一致") && strstr(g_log, "类型 3") && strstr(g_log, "类型 1"), "④ 容器 {A 类型 3, C 类型 1}：0、红行「地址空间类型不一致」并列出两款类型");
    if (bad) printf("  日志：%s\n", g_log);
    snprintf(b, sizeof b, "%s/empty", tmp); bundle(b, NULL, NULL, 0);
    ck(ctr(b, tmp) == 0 && strstr(g_log, "下没有游戏"), "④ 空 Games/：0、红行「下没有游戏」");
    snprintf(b, sizeof b, "%s/miss", tmp); bundle(b, (const char *[]){A, B}, (const int[]){0, 4}, 2);
    ck(ctr(b, tmp) == 0 && strstr(g_log, "读不到 main.npdm"), "④ 某款缺 main.npdm：0、红行「读不到 main.npdm」");
    // ⑤ 只读偏移表（iOS 上 s2a_loader_span_images 用它取各款 x1 块长）
    snprintf(b, sizeof b, "%s/img", tmp); mkdir(b, 0755); game(b, 3, 0, 0);
    snprintf(p, sizeof p, "python3 ios/embed.py '%s' '%s/S2AImages.dylib' main >/dev/null", b, b);
    int er = system(p);
    s2a_imgpack *pk = NULL; uint64_t off = 0, len = 0; char why[300] = "";
    snprintf(p, sizeof p, "%s/S2AImages.dylib", b);
    int rc = er ? -1 : s2a_imgpack_index(p, &pk, why, sizeof why);
    ck(rc == 0 && pk && s2a_imgpack_find(pk, "main", S2A_IMG_X1, &off, &len) && len == 0x4000, "⑤ s2a_imgpack_index：main 的 x1 块长 0x4000");
    if (rc) printf("  embed.py 返回 %d，index 返回 %d：%s\n", er, rc, why);
    s2a_imgpack_free(pk);
    snprintf(p, sizeof p, "%s/none.dylib", b);
    ck(s2a_imgpack_index(p, &pk, why, sizeof why) == S2A_IMG_ENOFILE && !pk, "⑤ 包不在：S2A_IMG_ENOFILE");
    snprintf(p, sizeof p, "rm -rf '%s'", tmp); if (system(p)) {}
    setenv("S2A_APP_POOL_MB", "2048", 1);
    setenv("S2A_VAWIN_NORESERVE", "1", 1);
    char *child_args[] = {argv[0], "--budget", NULL}; pid_t child; int status = -1;
    int spawn = posix_spawn(&child, argv[0], NULL, NULL, child_args, environ);
    ck(!spawn && waitpid(child, &status, 0) == child && WIFEXITED(status) && !WEXITSTATUS(status), "reduced-budget mixed container regression");
    unsetenv("S2A_APP_POOL_MB"); unsetenv("S2A_VAWIN_NORESERVE");
    printf("%s t_vawin_container：%d 处不符\n", bad ? "✗" : "✓", bad);
    return bad != 0;
}
