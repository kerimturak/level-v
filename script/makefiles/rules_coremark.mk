
.PHONY: coremark_auto coremark_clone coremark_build coremark_clean coremark_help

# ============================================================
# 1️⃣ CoreMark Full Pipeline
# ============================================================

coremark_auto: coremark_clone coremark_build
	@echo -e "$(GREEN)[COREMARK] Pipeline complete.$(RESET)"

# ============================================================
# 2️⃣ Submodule Clone / Fallback Clone
# ============================================================

coremark_clone:
	@echo -e "$(YELLOW)[CHECK] CoreMark source availability...$(RESET)"

	@bash -c '\
		PATH_SUB="$(COREMARK_SUBDIR)"; \
		URL="$(COREMARK_REPO_URL)"; \
		\
		# 1) Submodule .gitmodules içinde tanımlı mı? \
		if grep -q "path = $$PATH_SUB" .gitmodules 2>/dev/null; then \
			echo -e "$(YELLOW)[SUBMODULE] Entry found for CoreMark$(RESET)"; \
			\
			# 1A) Klasör yok → init + update \
			if [ ! -d "$$PATH_SUB" ]; then \
				echo -e "$(YELLOW)[INIT] git submodule init$(RESET)"; \
				git submodule init; \
				echo -e "$(YELLOW)[UPDATE] git submodule update --recursive$(RESET)"; \
				git submodule update --recursive; \
				echo -e "$(GREEN)[OK] CoreMark submodule initialized.$(RESET)"; \
				exit 0; \
			fi; \
			\
			# 1B) Klasör var ama boş → update \
			if [ -d "$$PATH_SUB" ] && [ -z "$$(ls -A $$PATH_SUB)" ]; then \
				echo -e "$(YELLOW)[UPDATE] CoreMark folder empty, updating...$(RESET)"; \
				git submodule update --recursive; \
				echo -e "$(GREEN)[OK] CoreMark restored.$(RESET)"; \
				exit 0; \
			fi; \
			\
			# 1C) Klasör dolu → SKIP \
			echo -e "$(GREEN)[SKIP] CoreMark submodule already present.$(RESET)"; \
			exit 0; \
		fi; \
		\
		# 2) Submodule hiç tanımlanmamış → otomatik ekle \
		echo -e "$(YELLOW)[ADD] Registering CoreMark as submodule$(RESET)"; \
		git submodule add "$$URL" "$$PATH_SUB"; \
		echo -e "$(YELLOW)[UPDATE] Initializing CoreMark submodule...$(RESET)"; \
		git submodule update --init --recursive; \
		echo -e "$(GREEN)[OK] CoreMark submodule cloned.$(RESET)"; \
	'

# ============================================================
# 3️⃣ Build
#  (CoreMark klasik Makefile tabanlıdır — baseline build örneği)
# ============================================================

coremark_build:
	@echo -e "$(YELLOW)[BUILD] Building CoreMark...$(RESET)"
	@mkdir -p $(COREMARK_BUILD_DIR)
	@$(MAKE) -C $(COREMARK_SUBDIR) PORT_DIR=linux64 || \
		{ echo -e "$(RED)[ERROR] CoreMark build failed$(RESET)"; exit 1; }
	@echo -e "$(GREEN)[OK] CoreMark build complete.$(RESET)"

# ============================================================
# 4️⃣ Helpers
# ============================================================

coremark_clean:
	@echo -e "$(RED)[CLEAN] Removing CoreMark build output$(RESET)"
	@rm -rf $(COREMARK_BUILD_DIR)

coremark_help:
	@echo -e "$(GREEN)CERES CoreMark Management$(RESET)"
	@echo -e "  coremark_auto   – Clone + Build"
	@echo -e "  coremark_clone  – Clone CoreMark as submodule"
	@echo -e "  coremark_build  – Build CoreMark"
	@echo -e "  coremark_clean  – Clean output"
