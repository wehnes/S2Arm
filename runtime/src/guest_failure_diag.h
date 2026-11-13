// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
#pragma once
#include <stdint.h>
#include <stddef.h>
#include <string.h>

enum { S2A_FAIL_EVENTS = 64, S2A_DIAG_FRAMES = 20, S2A_DIAG_NODES = 256 };
typedef struct {
    uint64_t tick, thread, pc, lr, fp, address, requested, added, used, pool, result;
    uint64_t callers[6];
    unsigned svc, caller_count;
} s2a_fail_event;
typedef struct { s2a_fail_event events[S2A_FAIL_EVENTS]; unsigned next, count; uint64_t total; } s2a_fail_ring;
// The caller owns synchronization. Successful allocation paths never enter it.
static inline void s2a_fail_put(s2a_fail_ring *ring, const s2a_fail_event *event) {
    ring->events[ring->next] = *event;
    ring->next = (ring->next + 1) % S2A_FAIL_EVENTS;
    if (ring->count < S2A_FAIL_EVENTS) ring->count++;
    ring->total++;
}
static inline unsigned s2a_fail_copy(const s2a_fail_ring *ring, s2a_fail_event *out) {
    unsigned first = (ring->next + S2A_FAIL_EVENTS - ring->count) % S2A_FAIL_EVENTS;
    for (unsigned index = 0; index < ring->count; index++) out[index] = ring->events[(first + index) % S2A_FAIL_EVENTS];
    return ring->count;
}

typedef int (*s2a_diag_read_fn)(void *, uint64_t, uint64_t *, unsigned);
typedef void (*s2a_diag_emit_fn)(void *, unsigned, uint64_t, const uint64_t *, unsigned);
typedef struct { unsigned frames, nodes, failures, limited; uint64_t bytes; } s2a_diag_stats;
typedef struct {
    s2a_diag_read_fn read;
    s2a_diag_emit_fn emit;
    void *ctx;
    uint64_t seen[S2A_DIAG_NODES];
    s2a_diag_stats stats;
} s2a_diag_capture;

static inline int s2a_diag_pointer(uint64_t address) {
    return !(address & 7) && address >= (1ull << 32) && address < (1ull << 39);
}
// Candidate pointer previews, not proof that a word is a live owned object.
// The kernel-backed read callback must reject inaccessible memory safely.
static inline void s2a_diag_node(s2a_diag_capture *capture, uint64_t pointer, unsigned depth) {
    if (!s2a_diag_pointer(pointer)) return;
    for (unsigned index = 0; index < capture->stats.nodes; index++) if (capture->seen[index] == pointer) return;
    if (capture->stats.nodes == S2A_DIAG_NODES) { capture->stats.limited = 1; return; }
    capture->seen[capture->stats.nodes++] = pointer;
    uint64_t words[24], base = pointer - 96;
    unsigned count = 24;
    if (!capture->read(capture->ctx, base, words, count)) {
        base = pointer; count = 8;
        if (!capture->read(capture->ctx, base, words, count)) { capture->stats.failures++; return; }
    }
    capture->stats.bytes += count * sizeof(uint64_t);
    capture->emit(capture->ctx, depth, base, words, count);
    if (depth < 2) {
        for (unsigned index = 0; index < count; index++) {
            uint64_t address = base + index * 8;
            if (address >= pointer && address < pointer + 64) s2a_diag_node(capture, words[index], depth + 1);
        }
    }
}

static inline s2a_diag_stats s2a_diag_frames(uint64_t fp, s2a_diag_read_fn read, s2a_diag_emit_fn emit, void *ctx) {
    s2a_diag_capture capture = {.read = read, .emit = emit, .ctx = ctx};
    uint64_t saved[S2A_DIAG_FRAMES][16], starts[S2A_DIAG_FRAMES], fps[S2A_DIAG_FRAMES];
    unsigned valid[S2A_DIAG_FRAMES] = {0};
    while (capture.stats.frames < S2A_DIAG_FRAMES && s2a_diag_pointer(fp)) {
        uint64_t link[2];
        if (!read(ctx, fp, link, 2)) { capture.stats.failures++; break; }
        unsigned index = capture.stats.frames++;
        fps[index] = fp; starts[index] = fp - 32;
        valid[index] = read(ctx, starts[index], saved[index], 16);
        if (valid[index]) { emit(ctx, 0, starts[index], saved[index], 16); capture.stats.bytes += 128; }
        if (!link[0] || link[0] <= fp) { fp = 0; break; }
        fp = link[0];
    }
    for (unsigned frame = 0; frame < capture.stats.frames; frame++) {
        if (!valid[frame]) continue;
        for (unsigned word = 0; word < 16; word++) {
            if (word == 4 || word == 5) continue;   // frame link and return address are already recorded
            uint64_t pointer = saved[frame][word];
            int is_frame = 0;
            for (unsigned index = 0; index < capture.stats.frames; index++) if (pointer == fps[index]) is_frame = 1;
            if (!is_frame) s2a_diag_node(&capture, pointer, 1);
        }
    }
    if (capture.stats.frames == S2A_DIAG_FRAMES && fp) capture.stats.limited = 1;
    return capture.stats;
}
