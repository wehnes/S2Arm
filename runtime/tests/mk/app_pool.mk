# Copyright 2026 S2Arm contributors
# SPDX-License-Identifier: Apache-2.0
NATIVE_TEST_OWN += app_pool
.PHONY: native-test-app_pool
native-test-app_pool:
	@mkdir -p $(BUILD)/tests
	$(CC) $(CFLAGS) $(NATIVE_INC) -DS2A_UNIT_TEST -o $(BUILD)/tests/t_app_pool runtime/tests/t_app_pool.c runtime/src/layout.c
	$(BUILD)/tests/t_app_pool
TEST_TARGETS += native-test-app_pool
