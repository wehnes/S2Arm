# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 S2Arm contributors
NATIVE_TEST_OWN += guest_failure_diag
.PHONY: native-test-guest_failure_diag
native-test-guest_failure_diag:
	@mkdir -p $(BUILD)/tests
	$(CC) $(CFLAGS) $(NATIVE_INC) -o $(BUILD)/tests/t_guest_failure_diag runtime/tests/t_guest_failure_diag.c
	$(BUILD)/tests/t_guest_failure_diag
TEST_TARGETS += native-test-guest_failure_diag
