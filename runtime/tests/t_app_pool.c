// Copyright 2026 S2Arm contributors
// SPDX-License-Identifier: Apache-2.0
// Each fork starts before the process-wide budget has been initialized.
#include "../src/native.h"
#include <sys/wait.h>

#define MB (1ull << 20)
#define GB (1ull << 30)
static int bad;
#define EQ(a, b) do { uint64_t actual_ = (a), expected_ = (b); if (actual_ != expected_) { fprintf(stderr, "%s = %llu, expected %llu\n", #a, (unsigned long long)actual_, (unsigned long long)expected_); bad++; } } while (0)

static int check(uint64_t expected) {
    // An experimental cap must never enlarge the original Switch pool.
    EQ(s2a_app_pool(), 0xCD500000ull);
    s2a_app_pool_set(9 * GB);
    EQ(s2a_app_pool(), expected);
    EQ(S2A_HEAP_DEFAULT, expected & ~(2 * MB - 1));
    EQ(s2a_layout_need(3, 80 * MB, 300 * MB), 63 * GB + (2 + 2048 + 96 + 300) * MB + (expected & ~(2 * MB - 1)));
    s2a_layout layout; uint64_t module, shadow;
    EQ(s2a_layout_compute(3, 80 * MB, 300 * MB, 0, 64 * GB, 80 * GB, &layout, &module, &shadow), 0);
    EQ(layout.heap_size, expected & ~(2 * MB - 1));
    // A running game's capacity must stay fixed even if its environment changes.
    setenv("S2A_APP_POOL_MB", "4096", 1);
    EQ(s2a_app_pool(), expected);
    s2a_app_pool_set(0xCD500000ull);
    EQ(s2a_app_pool(), 0xCD500000ull);
    s2a_app_pool_set(9 * GB);
    EQ(s2a_app_pool(), expected);
    return bad != 0;
}

int main(void) {
    const struct { const char *value; uint64_t expected; } cases[] = {
        {NULL, 9 * GB}, {"", 9 * GB}, {"0", 9 * GB},
        {"5632", 5632 * MB}, {"5633", 5633 * MB}, {"4096", 4 * GB},
        {"9216", 9 * GB}, {"12288", 9 * GB}, {"65536", 9 * GB},
        {"4095", 9 * GB}, {"65537", 9 * GB}, {"-5632", 9 * GB},
        {"+5632", 9 * GB}, {" 5632", 9 * GB}, {"5632MB", 9 * GB},
        {"18446744073709551616", 9 * GB},
    };
    for (size_t i = 0; i < sizeof cases / sizeof *cases; i++) {
        if (cases[i].value) setenv("S2A_APP_POOL_MB", cases[i].value, 1);
        else unsetenv("S2A_APP_POOL_MB");
        pid_t child = fork();
        if (child < 0) return 2;
        if (!child) { bad = 0; _exit(check(cases[i].expected)); }
        int status;
        if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status)) {
            fprintf(stderr, "budget case %zu failed\n", i);
            bad++;
        }
    }
    printf("Application pool: 16 cases, %d failed\n", bad);
    return bad != 0;
}
