# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 S2Arm contributors
NATIVE_TEST_OWN += ios_guest_budget
.PHONY: native-test-ios_guest_budget
native-test-ios_guest_budget:
	@mkdir -p $(BUILD)/tests
	$(CC) $(CFLAGS) $(NATIVE_INC) -DS2A_UNIT_TEST -o $(BUILD)/tests/t_ios_guest_budget runtime/tests/t_ios_guest_budget.m
	$(BUILD)/tests/t_ios_guest_budget
TEST_TARGETS += native-test-ios_guest_budget
