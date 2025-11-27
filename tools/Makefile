# Makefile for tools/ — runs .sh scripts and includes coremark rules
# Usage: run targets from repository root or from tools/ with
#   make -f tools/Makefile run-<scriptname>

THIS_MAKEFILE := $(abspath $(lastword $(MAKEFILE_LIST)))
THIS_DIR := $(patsubst %/,%,$(dir $(THIS_MAKEFILE)))
SCRIPTS_DIR := $(THIS_DIR)

SCRIPTS := $(wildcard $(SCRIPTS_DIR)/*.sh)
SCRIPT_BASENAMES := $(patsubst $(SCRIPTS_DIR)/%.sh,%,$(SCRIPTS))

.PHONY: all-scripts run-% list-scripts coremark help

help:
	@echo "Usage: make -f tools/Makefile <target>"
	@echo "Targets:"
	@echo "  list-scripts     - list available .sh scripts in $(SCRIPTS_DIR)"
	@echo "  run-<name>       - run script '<name>.sh' from $(SCRIPTS_DIR)"
	@echo "  all-scripts      - run all scripts sequentially"
	@echo "  coremark         - invoke coremark build rules (if available)"

list-scripts:
	@echo "Scripts in $(SCRIPTS_DIR):"
	@for s in $(SCRIPT_BASENAMES); do echo " - $$s"; done

run-%:
	@script="$(SCRIPTS_DIR)/$*.sh"; \
	if [ -f "$$script" ]; then \
	  if [ -x "$$script" ]; then \
	    echo "Running $$script $$ARGS"; \
	    eval "$$script $$ARGS"; \
	  else \
	    echo "Making $$script executable and running $$ARGS"; \
	    chmod +x "$$script"; \
	    eval "$$script $$ARGS"; \
	  fi; \
	else \
	  echo "Script $$script not found"; exit 2; \
	fi

all-scripts: $(addprefix run-, $(SCRIPT_BASENAMES))

# Try to include the coremark rules from repo script/makefiles
COREMARK_MK := $(abspath $(THIS_DIR)/../script/makefiles/rules_coremark.mk)
ifneq (,$(wildcard $(COREMARK_MK)))
include $(COREMARK_MK)
else
  $(warning Could not find $(COREMARK_MK). Coremark rules not included.)
endif
