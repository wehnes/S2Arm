// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
#include <mach/mach.h>
#include <os/proc.h>
#include <stdint.h>
#include <stdio.h>

static uint64_t available_bytes, footprint_bytes;
static kern_return_t info_result;
static size_t test_available(void) { return available_bytes; }
static kern_return_t test_task_info(task_name_t task, task_flavor_t flavor, task_info_t output, mach_msg_type_number_t *count) {
    (void)task; (void)flavor; (void)count;
    ((task_vm_info_t)output)->phys_footprint = footprint_bytes;
    return info_result;
}
#define os_proc_available_memory test_available
#define task_info test_task_info
#include "../../ios/guest_budget.m"
#undef task_info
#undef os_proc_available_memory

int main(void) {
    const struct { uint64_t available, footprint; kern_return_t result; uint64_t expected; } cases[] = {
        {6ull << 30, 2ull << 30, KERN_SUCCESS, 8ull << 30},
        {0, 0, KERN_SUCCESS, 0},
        {0, 3ull << 30, KERN_SUCCESS, 3ull << 30},
        {8ull << 30, 0, KERN_FAILURE, UINT64_MAX},
        {UINT64_MAX, 1, KERN_SUCCESS, UINT64_MAX},
        {UINT64_MAX - 2, 1, KERN_SUCCESS, UINT64_MAX - 1},
    };
    int failed = 0;
    for (unsigned index = 0; index < 6; index++) {
        available_bytes = cases[index].available; footprint_bytes = cases[index].footprint; info_result = cases[index].result;
        if (s2a_app_pool_process_limit() != cases[index].expected) {
            fprintf(stderr, "iOS budget provider case %u failed\n", index);
            failed++;
        }
    }
    printf("iOS budget provider: 6 cases, %d failed\n", failed);
    return failed != 0;
}
