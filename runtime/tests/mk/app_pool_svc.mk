# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 S2Arm contributors
NATIVE_TEST_OWN += app_pool_svc
.PHONY: native-test-app_pool_svc
native-test-app_pool_svc: $(TEST_VAGUARD)
	@mkdir -p $(BUILD)/tests
	$(CC) $(CFLAGS) $(NATIVE_INC) -DS2A_UNIT_TEST -o $(BUILD)/tests/t_app_pool_svc runtime/tests/t_app_pool_svc.c runtime/src/svc_mem.c runtime/src/layout.c $(TEST_VAGUARD)
	$(BUILD)/tests/t_app_pool_svc
TEST_TARGETS += native-test-app_pool_svc
