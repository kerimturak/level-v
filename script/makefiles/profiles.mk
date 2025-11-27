# =========================================
# CERES Build Profiles (debug / release / test)
# =========================================

ifeq ($(MODE),debug)
	BUILD_MODE_NAME := Debug
	DEFINE_MACROS += +define+DEBUG
	VLOG_FLAGS_EXTRA := +define+SIM_DEBUG
	OPT_LEVEL := -O0
	BUILD_DESC := "Debug mode enabled (with assertions, waveforms, full tracing)"
endif

ifeq ($(MODE),release)
	BUILD_MODE_NAME := Release
	DEFINE_MACROS += +define+RELEASE
	VLOG_FLAGS_EXTRA := +define+FAST_SIM
	OPT_LEVEL := -O2
	BUILD_DESC := "Release mode enabled (optimized, minimal logs)"
endif

ifeq ($(MODE),test)
	BUILD_MODE_NAME := Test
	DEFINE_MACROS += +define+TEST_ENV
	VLOG_FLAGS_EXTRA := +define+RISCV_TEST
	OPT_LEVEL := -O1
	BUILD_DESC := "Test mode enabled (RISCV arch tests, extended assertions)"
endif

ifndef BUILD_MODE_NAME
	$(error Unknown build mode: $(MODE). Use MODE=debug|release|test)
endif
