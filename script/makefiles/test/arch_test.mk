.PHONY: arch_auto arch_clone arch_setup arch_config arch_run arch_reset arch_help

# ============================================================
# 1️⃣ Ana Akış (Clone → Setup → Config → Run)
# ============================================================
arch_auto: arch_clone arch_setup arch_config arch_run

# ------------------------------------------------------------
# 1. Klonlama
# ------------------------------------------------------------
arch_clone:
	@echo -e "$(YELLOW)[CLONE] Checking riscv-arch-test repo...$(RESET)"
	@mkdir -p $(SUBREPO_DIR)
	@if [ ! -d "$(ARCH_ROOT)/.git" ]; then \
		echo -e "$(YELLOW)[CLONE] Cloning from $(ARCH_REPO_URL)...$(RESET)"; \
		cd $(SUBREPO_DIR) && git clone $(ARCH_REPO_URL); \
		cd $(ARCH_ROOT) && git checkout $(ARCH_BRANCH); \
	else \
		echo -e "$(GREEN)[SKIP] riscv-arch-test already cloned.$(RESET)"; \
	fi

# ------------------------------------------------------------
# 2. RISCOF ve bağımlılıkları kur
# ------------------------------------------------------------
arch_setup:
	@echo -e "$(YELLOW)[SETUP] Installing RISCOF and dependencies...$(RESET)"
	@python3 -m venv ~/.venv/riscof
	@. ~/.venv/riscof/bin/activate && \
		pip install --upgrade pip && \
		pip install git+https://github.com/riscv/riscof.git && \
		pip install riscv-config && \
		pip install riscv-isac==0.12.0 && \
		echo -e "$(GREEN)[OK] riscof installed with local riscv-ctg.$(RESET)"

# ------------------------------------------------------------
# 3. Ceres hedefi için config oluştur
# ------------------------------------------------------------
arch_config:
	@echo -e "$(YELLOW)[CONFIG] Generating ceres target config...$(RESET)"
	@mkdir -p $(ARCH_ROOT)/riscof-plugins/ceres
	@cp script/templates/ceres_plugin.py $(ARCH_ROOT)/riscof-plugins/ceres/ || true
	@echo "[RISCOF]" > $(ARCH_ROOT)/config.ini
	@echo "ReferencePlugin = spike" >> $(ARCH_ROOT)/config.ini
	@echo "ReferencePluginPath = $(ARCH_ROOT)/riscof-plugins/spike" >> $(ARCH_ROOT)/config.ini
	@echo "TargetPlugin = ceres" >> $(ARCH_ROOT)/config.ini
	@echo "TargetPluginPath = $(ARCH_ROOT)/riscof-plugins/ceres" >> $(ARCH_ROOT)/config.ini
	@echo "Suite = $(ARCH_ROOT)/riscv-test-suite" >> $(ARCH_ROOT)/config.ini
	@echo "Env = $(ARCH_ROOT)/riscv-test-suite/env" >> $(ARCH_ROOT)/config.ini
	@echo -e "$(GREEN)[DONE] config.ini generated.$(RESET)"

# ------------------------------------------------------------
# 4. Testleri Çalıştır
# ------------------------------------------------------------
arch_run:
	@echo -e "$(YELLOW)[RUN] Running RISCOF...$(RESET)"
	@. ~/.venv/riscof/bin/activate && \
		cd $(ARCH_ROOT) && \
		riscof run --config config.ini --suite riscv-test-suite/ --env riscv-test-suite/env

# ------------------------------------------------------------
# 5. Repo Temizliği
# ------------------------------------------------------------
arch_reset:
	@echo -e "$(RED)[RESET] Removing riscv-arch-test repo$(RESET)"
	@rm -rf $(ARCH_ROOT)

# ------------------------------------------------------------
# Yardım
# ------------------------------------------------------------
arch_help:
	@echo -e "$(GREEN)Usage Examples:$(RESET)"
	@echo "  make arch_auto       # Clone + Setup + Config + Run"
	@echo "  make arch_config     # Generate ceres plugin & config"
	@echo "  make arch_run        # Run riscof tests"
	@echo "  make arch_reset      # Delete repo"