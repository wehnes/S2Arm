// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 S2Arm contributors
#include <stdint.h>
#include <mach/mach.h>
#include <os/proc.h>

// Internal startup provider for layout.c. No UIKit calls are allowed here:
// the address-window constructor can query it before UIApplication exists.
// Returns a byte allowance, including current footprint; UINT64_MAX means
// unavailable. The caller freezes one sample for the process lifetime.
uint64_t s2a_app_pool_process_limit(void) {
    task_vm_info_data_t info; mach_msg_type_number_t count = TASK_VM_INFO_COUNT;
    uint64_t available = os_proc_available_memory();
    if (task_info(mach_task_self(), TASK_VM_INFO, (task_info_t)&info, &count) != KERN_SUCCESS || available > UINT64_MAX - info.phys_footprint)
        return UINT64_MAX;
    return available + info.phys_footprint;
}
