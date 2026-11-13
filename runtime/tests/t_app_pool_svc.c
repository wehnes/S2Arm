// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
// Reuse the memory SVC fixture and its isolated dependency providers.
#define main existing_memory_regression_main
#include "t_svc_mem.c"
#undef main

#define BUDGET_MB (1ull << 20)
static int check_budget(const char *setting, uint64_t native_pool, uint64_t expected) {
    setenv("S2A_APP_POOL_MB", setting, 1);
    setenv("S2A_PHYS_LIMIT", "1", 1);
    s2a_app_pool_set(native_pool);
    uint64_t heap = (expected - 42 * BUDGET_MB) & ~(2 * BUDGET_MB - 1);
    uint64_t physical = expected - heap - 34 * BUDGET_MB;
    uint8_t *alias = mmap(NULL, 64 * BUDGET_MB, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    uint8_t *base = mmap(NULL, 8 * BUDGET_MB, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    CHECK(alias != MAP_FAILED && base != MAP_FAILED, "fixture mappings");
    if (alias == MAP_FAILED || base == MAP_FAILED) return 1;
    s2a_mem_test_setup((uint64_t)alias, 64 * BUDGET_MB, (uint64_t)alias, 64 * BUDGET_MB, base, heap);
    s2a_mem_test_sysres(32 * BUDGET_MB, heap + 2 * BUDGET_MB);
    g_nmod = 2; memset(g_mod, 0, 2 * sizeof *g_mod);
    g_mod[0].patch_off = BUDGET_MB; g_mod[0].size = 3 * BUDGET_MB;
    g_mod[1].patch_off = -0x4000; g_mod[1].image_size = BUDGET_MB; g_mod[1].size = BUDGET_MB;
    uint64_t regs[8] = {(uint64_t)alias, physical};
    svc_mem(0x2c, regs, 0);
    CHECK(regs[0] == 0 && s2a_mem_test_phys() == physical, "fill remaining guest pool");
    memset(regs, 0, sizeof regs); regs[0] = (uint64_t)alias + physical; regs[1] = 0x1000;
    svc_mem(0x2c, regs, 0);
    CHECK(regs[0] == 0x10801 && s2a_mem_test_phys() == physical, "reject extra page without changing accounting");
    if (regs[0] != 0x10801) return 1;   // negative control must not grow the synthetic heap
    const unsigned ids[] = {6, 7, 21, 22};
    const uint64_t values[] = {expected, expected, expected - 32 * BUDGET_MB, expected - 32 * BUDGET_MB};
    for (unsigned index = 0; index < 4; index++) {
        memset(regs, 0, sizeof regs); regs[1] = ids[index]; regs[2] = 0xffff8001u;
        svc_mem(0x29, regs, 0);
        CHECK(regs[0] == 0 && regs[1] == values[index], "GetInfo %u follows application budget", ids[index]);
    }
    memset(regs, 0, sizeof regs); svc_mem(0x6f, regs, 0);
    CHECK(regs[0] == 0 && regs[1] == expected, "GetSystemInfo application total follows budget");
    memset(regs, 0, sizeof regs); regs[1] = 1; svc_mem(0x6f, regs, 0);
    CHECK(regs[0] == 0 && regs[1] == 0, "GetSystemInfo application free is zero when full");
    memset(regs, 0, sizeof regs); regs[1] = heap + 2 * BUDGET_MB; svc_mem(0x01, regs, 0);
    CHECK(regs[0] == 0x10801, "heap growth obeys the same full pool");
    return bad != 0;
}

int main(void) {
    const struct { const char *setting; uint64_t native, expected; } cases[] = {
        {"6144", 9ull << 30, 6144 * BUDGET_MB},
        {"2048", 0xCD500000ull, 2048 * BUDGET_MB},
        {"6144", 0xCD500000ull, 0xCD500000ull},
        {"0", 9ull << 30, 9ull << 30},
    };
    int failures = 0;
    for (unsigned index = 0; index < sizeof cases / sizeof *cases; index++) {
        pid_t child = fork();
        if (child < 0) return 2;
        if (!child) {
            int result = check_budget(cases[index].setting, cases[index].native, cases[index].expected);
            fflush(NULL);
            _exit(result);
        }
        int status;
        if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status)) failures++;
    }
    printf("%s t_app_pool_svc：%zu cases, %d failed\n", failures ? "✗" : "✓", sizeof cases / sizeof *cases, failures);
    return failures != 0;
}
