// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
#include "../src/native.h"
#include <sys/wait.h>
#include <stdatomic.h>

#define MB (1ull << 20)
#define GB (1ull << 30)
#define NATIVE_SWITCH 0xCD500000ull
static uint64_t process_limit;
static _Atomic int provider_calls;
uint64_t s2a_app_pool_native(void);
uint64_t s2a_app_pool_process_limit(void) { atomic_fetch_add(&provider_calls, 1); return process_limit; }
static int failed;
#define EQ(a, b) do { uint64_t actual_ = (a), expected_ = (b); if (actual_ != expected_) { fprintf(stderr, "%s = %llu, expected %llu\n", #a, (unsigned long long)actual_, (unsigned long long)expected_); failed++; } } while (0)

typedef struct {
    const char *setting;
    const char *reserve;
    uint64_t limit;
    uint64_t expected_switch;
    uint64_t expected_switch2;
} budget_case;

static void *read_pool(void *expected) {
    return (void *)(uintptr_t)(s2a_app_pool() != *(uint64_t *)expected);
}

static int check(const budget_case *item) {
    process_limit = item->limit;
    pthread_t readers[8]; uint64_t expected = item->expected_switch;
    for (unsigned index = 0; index < 8; index++) if (pthread_create(&readers[index], NULL, read_pool, &expected)) return 1;
    for (unsigned index = 0; index < 8; index++) {
        void *result;
        if (pthread_join(readers[index], &result)) return 1;
        EQ((uintptr_t)result, 0);
    }
    EQ(atomic_load(&provider_calls) > 1, 0);
    EQ(s2a_app_pool(), item->expected_switch);
    s2a_app_pool_set(9 * GB);
    EQ(s2a_app_pool_native(), 9 * GB);
    EQ(s2a_app_pool(), item->expected_switch2);
    EQ(S2A_HEAP_DEFAULT, item->expected_switch2 & ~(2 * MB - 1));
    s2a_layout layout; uint64_t module, shadow;
    if (item->expected_switch2 > 80 * MB) {
        EQ(s2a_layout_need(3, 80 * MB, 300 * MB), 63 * GB + (2 + 2048 + 96 + 300) * MB + (item->expected_switch2 & ~(2 * MB - 1)));
        EQ(s2a_layout_compute(3, 80 * MB, 300 * MB, 0, 64 * GB, 80 * GB, &layout, &module, &shadow), 0);
        EQ(layout.heap_size, item->expected_switch2 & ~(2 * MB - 1));
    } else {
        EQ(s2a_layout_need(3, 80 * MB, 300 * MB), 0);
        EQ(s2a_layout_compute(3, 80 * MB, 300 * MB, 0, 64 * GB, 80 * GB, &layout, &module, &shadow), (uint64_t)-3);
    }
    // Once a game's layout can use the budget, changes to environment or OS
    // limits cannot resize its already advertised pool.
    setenv("S2A_APP_POOL_MB", "4096", 1);
    setenv("S2A_APP_POOL_RESERVE_MB", "0", 1);
    process_limit = 16 * GB;
    int calls = atomic_load(&provider_calls);
    EQ(s2a_app_pool(), item->expected_switch2);
    EQ(atomic_load(&provider_calls), calls);
    s2a_app_pool_set(NATIVE_SWITCH);
    EQ(s2a_app_pool_native(), NATIVE_SWITCH);
    EQ(s2a_app_pool(), item->expected_switch);
    s2a_app_pool_set(9 * GB);
    EQ(s2a_app_pool(), item->expected_switch2);
    return failed != 0;
}

int main(void) {
    const budget_case cases[] = {
        {NULL, NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"0", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"00", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"5632", NULL, 0, NATIVE_SWITCH, 5632 * MB},
        {"6144", NULL, 0, NATIVE_SWITCH, 6 * GB},
        {"5633", NULL, 0, NATIVE_SWITCH, 5633 * MB},
        {"2048", NULL, 0, 2 * GB, 2 * GB},
        {"1", NULL, 0, MB, MB},
        {"4095", NULL, 0, NATIVE_SWITCH, 4095 * MB},
        {"9216", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"65537", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"17592186044415", NULL, 0, NATIVE_SWITCH, 9 * GB},
        {"17592186044416", NULL, 0, 0, 0},
        {"18446744073709551616", NULL, 0, 0, 0},
        {"-5632", NULL, 0, 0, 0},
        {"+5632", NULL, 0, 0, 0},
        {" 5632", NULL, 0, 0, 0},
        {"5632MB", NULL, 0, 0, 0},
        {"AUTO", NULL, 0, 0, 0},
        {"auto", NULL, UINT64_MAX, 0, 0},
        {"auto", NULL, 0, 0, 0},
        {"auto", NULL, 2 * GB, 0, 0},
        {"auto", NULL, 2560 * MB, 0, 0},
        {"auto", NULL, 4 * GB, 1536 * MB, 1536 * MB},
        {"auto", NULL, 6 * GB, NATIVE_SWITCH, 3584 * MB},
        {"auto", NULL, 8 * GB, NATIVE_SWITCH, 5632 * MB},
        {"auto", NULL, 12 * GB, NATIVE_SWITCH, 9 * GB},
        {"auto", "2048", 8 * GB, NATIVE_SWITCH, 6 * GB},
        {"auto", "3072", 8 * GB, NATIVE_SWITCH, 5 * GB},
        {"auto", "0", 8 * GB, NATIVE_SWITCH, 8 * GB},
        {"auto", "-1", 8 * GB, 0, 0},
        {"auto", "xyz", 8 * GB, 0, 0},
        {"auto", "17592186044416", 8 * GB, 0, 0},
        {"auto", NULL, 8191 * MB, NATIVE_SWITCH, 5630 * MB},
        {"6144", "xyz", UINT64_MAX, NATIVE_SWITCH, 6 * GB},
    };
    for (size_t index = 0; index < sizeof cases / sizeof *cases; index++) {
        const budget_case *item = &cases[index];
        if (item->setting) setenv("S2A_APP_POOL_MB", item->setting, 1); else unsetenv("S2A_APP_POOL_MB");
        if (item->reserve) setenv("S2A_APP_POOL_RESERVE_MB", item->reserve, 1); else unsetenv("S2A_APP_POOL_RESERVE_MB");
        pid_t child = fork();
        if (child < 0) return 2;
        if (!child) { failed = 0; _exit(check(item)); }
        int status;
        if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status)) {
            fprintf(stderr, "case %zu failed (%s)\n", index, item->setting ? item->setting : "unset");
            failed++;
        }
    }
    printf("Application budget: %zu cases, %d failed\n", sizeof cases / sizeof *cases, failed);
    return failed != 0;
}
