// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
#include "../src/guest_failure_diag.h"
#include <stdio.h>

static int bad, checks;
#define CHECK(condition, message) do { checks++; if (!(condition)) { fprintf(stderr, "FAIL %s\n", message); bad++; } } while (0)
enum { DATA_BYTES = 8192 };
static unsigned char memory[DATA_BYTES];
static const uint64_t start = 0x5000000000ull;
static unsigned emits, second_level;
static int read_words(void *ctx, uint64_t address, uint64_t *out, unsigned count) {
    (void)ctx;
    if (address < start || count > DATA_BYTES / 8 || address - start > DATA_BYTES - count * 8) return 0;
    memcpy(out, memory + address - start, count * 8);
    return 1;
}
static void emit(void *ctx, unsigned depth, uint64_t address, const uint64_t *words, unsigned count) {
    (void)ctx;
    emits++;
    // Synthetic saved vector-end pointer. Its last entry has a null buffer
    // and a nonzero length; a two-level preview must preserve both words.
    if (depth == 2 && address == start + 4096 - 96 && count == 24 && words[2] == 0 && words[10] == 102400) second_level++;
}
static void word(unsigned offset, uint64_t value) { memcpy(memory + offset, &value, 8); }

int main(void) {
    s2a_fail_ring ring = {0}; s2a_fail_event out[S2A_FAIL_EVENTS];
    CHECK(s2a_fail_copy(&ring, out) == 0, "empty ring");
    for (unsigned index = 0; index < 70; index++) {
        s2a_fail_event event = {.tick = index, .requested = 1000 + index, .callers = {index + 7}, .caller_count = 1};
        s2a_fail_put(&ring, &event);
    }
    CHECK(ring.total == 70 && ring.count == 64, "bounded event count");
    CHECK(s2a_fail_copy(&ring, out) == 64 && out[0].tick == 6 && out[63].tick == 69, "newest events retain chronological order");
    CHECK(out[63].requested == 1069 && out[63].callers[0] == 76, "event payload preserved");
    word(512, 0); word(520, start + 100);
    word(544, start + 2048);   // saved vector pointer in the synthetic frame
    word(2056, start + 4096);  // vector end
    word(4096 - 80, 0); word(4096 - 16, 102400);
    s2a_diag_stats stats = s2a_diag_frames(start + 512, read_words, emit, NULL);
    CHECK(stats.frames == 1 && emits > 1, "capture frame and pointer nodes");
    CHECK(second_level == 1, "second-level preview retains null buffer and requested length");
    CHECK(stats.bytes <= 64 * 1024 && stats.nodes <= S2A_DIAG_NODES, "bounded capture size");
    emits = 0;
    stats = s2a_diag_frames(start + DATA_BYTES + 128, read_words, emit, NULL);
    CHECK(stats.frames == 0 && stats.failures == 1 && emits == 0, "inaccessible frame rejected");
    word(512, start + 512);
    stats = s2a_diag_frames(start + 512, read_words, emit, NULL);
    CHECK(stats.frames == 1, "cyclic frame terminates");
    CHECK(!s2a_diag_pointer(0) && !s2a_diag_pointer(start + 1) && !s2a_diag_pointer(1ull << 40), "invalid pointer shapes rejected");
    printf("%s t_guest_failure_diag：%d checks, %d failures\n", bad ? "✗" : "✓", checks, bad);
    return bad != 0;
}
