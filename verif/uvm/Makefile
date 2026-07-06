# ============================================================================
# Level RISC-V UVM — Derleme/Koşum Makefile'ı
# ----------------------------------------------------------------------------
# Desteklenen simülatörler: Verilator (varsayılan, >=5.048), Questa/ModelSim,
# VCS, Xcelium.
#
# Verilator UVM notları:
#   * UVM kaynağı: Verilator'ın kendi regresyonunda test ettiği düzleştirilmiş
#     IEEE 1800.2-2020 v3.1 (nodpi) paketi — repoya kopyalandı:
#     verif/uvm/verilator/uvm_pkg_all_nodpi.svh (Apache-2.0, Accellera).
#     `include "uvm_macros.svh"` bu akışta verif/uvm/verilator/ altındaki
#     BOŞ shim'e çözülür (makrolar düzleştirilmiş pakette zaten tanımlı).
#   * covergroup'lar Verilator'da yok sayılır (COVERIGN uyarısı) — fonksiyonel
#     coverage raporu gerekiyorsa ticari simülatör kullanın; testler, SVA'lar
#     ve scoreboard kontrolleri tam çalışır.
#   * C++ derlemesi bellek yoğundur: VL_JOBS (vars. 2) ve VL_OPT (vars. -O0)
#     ile dengelenir. RTL tarafında SoC sarmalayıcı/periferikler bu ortamda
#     kullanılmadığı için derleme dışıdır (VL_RTL_EXCLUDE).
#
# Örnekler:
#   make -C verif/uvm run                                   # duman testi
#   make -C verif/uvm run TEST=level_v_irq_stress_test SEED=42
#   make -C verif/uvm run TEST=level_v_backpressure_test VERBOSITY=UVM_HIGH
#   make -C verif/uvm run TEST=level_v_hex_test PLUSARGS="+firmware=prog.hex +tohost_addr=0x80001000"
#   make -C verif/uvm regress N=20                          # 20 rastgele seed
#   make -C verif/uvm run SIM=questa                        # Questa ile
#
# Sık kullanılan plusarg'lar (PLUSARGS içine):
#   +n_instrs=1000        gövde komut sayısını sabitle
#   +tohost_addr=0x...    tohost adresi (hex imajlarında link.ld'ye göre)
#   +lv_trace=commit.log  commit trace dosyası
#   +lv_wave=dump.vcd     dalga kaydı
#   +wd_limit=100000      watchdog çevrim limiti
#   +iomem_assert_off     arayüz SVA'larını kapat
# ============================================================================

# ---- Kullanıcı ayarları ----------------------------------------------------
SIM        ?= verilator
TEST       ?= level_v_random_test
SEED       ?= 1
VERBOSITY  ?= UVM_MEDIUM
PLUSARGS   ?=
GUI        ?= 0
N          ?= 10        # regress hedefi için koşum sayısı

# ---- Yol tanımları ----------------------------------------------------------
ROOT_DIR   := $(abspath ../..)
UVM_DIR    := $(ROOT_DIR)/verif/uvm
WORK_DIR   := $(UVM_DIR)/work
LOG_DIR    := $(UVM_DIR)/logs

RTL_FLIST  := $(ROOT_DIR)/rtl/flist.f
DV_FLIST   := $(UVM_DIR)/level_v_dv.f

# flist'lerdeki repo-köküne-göre yolları mutlak yollara çevir (# ve boş atla)
RTL_SRCS   := $(addprefix $(ROOT_DIR)/,$(shell awk '!/^[[:space:]]*#/ && NF {print $$1}' $(RTL_FLIST)))
DV_SRCS    := $(addprefix $(ROOT_DIR)/,$(shell awk '!/^[[:space:]]*#/ && NF {print $$1}' $(DV_FLIST)))

# RTL parametre profili: level_param.sv, ana makefile'ın ürettiği
# build/gen/level_param_profile.svh dosyasını include eder. Dosya yoksa
# aşağıdaki kural aynı python üreticiyle (varsayılan profil: medium) üretir.
# Profil değiştirmek için: make ... RTL_PROFILE=minimal_soc
RTL_PROFILE  ?= medium
RTL_GEN_DIR  := $(ROOT_DIR)/build/gen
PROFILE_SVH  := $(RTL_GEN_DIR)/level_param_profile.svh
GEN_PROFILE_PY := $(ROOT_DIR)/script/python/gen_level_param_profile.py

INCDIRS    := +incdir+$(ROOT_DIR)/rtl/include \
              +incdir+$(RTL_GEN_DIR) \
              +incdir+$(UVM_DIR)/env \
              +incdir+$(UVM_DIR)/tests

RUN_PLUSARGS := +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(VERBOSITY) $(PLUSARGS)

# ---- Questa/ModelSim ---------------------------------------------------------
# UVM kaynağı: önce QUESTA_HOME içindeki paketlenmiş kopya; UVM_HOME ile
# ezilebilir. UVM_NO_DPI: DPI kütüphanesi derleme derdi olmadan taşınabilir
# koşum (regex/cmdline DPI hızlandırmaları kapanır — işlevsel fark yok).
QUESTA_HOME ?= $(dir $(shell which vsim 2>/dev/null))..
UVM_HOME    ?= $(QUESTA_HOME)/verilog_src/uvm-1.2
UVM_DEFINES := +define+UVM_NO_DPI+UVM_REGEX_NO_DPI+UVM_CMDLINE_NO_DPI
VLOG_SUPPRESS ?= -suppress vlog-2583 -suppress vlog-2275
VSIM_ARGS   ?= -voptargs=+acc

# ---- VCS ---------------------------------------------------------------------
VCS_OPTS  := -full64 -sverilog -timescale=1ns/1ps -ntb_opts uvm-1.2 \
             -CFLAGS -DVCS +lint=TFIPC-L -l $(LOG_DIR)/vcs_compile.log

# ---- Xcelium -------------------------------------------------------------------
XRUN_OPTS := -64bit -uvm -sv -timescale 1ns/1ps -access +rwc

# ---- Verilator ---------------------------------------------------------------
# Düzleştirilmiş UVM paketi (repo içi kopya; VL_UVM_PKG ile ezilebilir).
VL_UVM_PKG ?= $(UVM_DIR)/verilator/uvm_pkg_all_nodpi.svh
# C++ derleme paralelliği ve optimizasyonu (bellek/süre dengesi).
VL_JOBS    ?= 2
VL_OPT     ?= -O0
# UVM'in yeniden derlenmesini önleyen iki katman:
#  1) Verilator, içeriği değişmeyen üretilmiş .cpp dosyalarını yeniden
#     YAZMAZ (skip-identical) -> make yalnızca değişen objeleri derler.
#     TB sınıflarında yapılan bir değişiklik UVM çekirdek objelerine dokunmaz.
#  2) ccache varsa OBJCACHE olarak kullanılır -> tam yeniden üretimlerde bile
#     derleme önbellekten döner (ilk derleme hariç saniyeler mertebesi).
VL_OBJCACHE ?= $(shell command -v ccache >/dev/null 2>&1 && echo ccache)
# Çıktı dizini ve üretilen benzetim ikilisi.
VL_MDIR    := $(ROOT_DIR)/build/uvm_verilator
VL_BIN     := $(VL_MDIR)/Vlevel_v_tb_top
# Bu ortamda DUT çekirdek olduğu için SoC sarmalayıcı/periferik/tracer RTL'i
# derleme dışı bırakılır (iomem arkasında UVM bellek agent'ı var).
VL_RTL_EXCLUDE := ^rtl/(wrapper|periph|tracer)/
VL_RTL_SRCS := $(addprefix $(ROOT_DIR)/,$(shell awk '!/^[[:space:]]*[\#]/ && NF {print $$1}' $(RTL_FLIST) | grep -v -E '$(VL_RTL_EXCLUDE)'))
# Paketin include ettiği tüm sınıf dosyaları da bağımlılıktır — yoksa .svh
# değişiklikleri yeniden derleme tetiklemez.
DV_HDRS   := $(shell find $(UVM_DIR)/env $(UVM_DIR)/tests -name '*.svh' 2>/dev/null)
RTL_HDRS  := $(shell find $(ROOT_DIR)/rtl/include -name '*.svh' 2>/dev/null)
# Uyarı bastırmaları: RTL -Wall temiz değil (lint/style) + covergroup yok sayma.
VL_WNO     := -Wno-lint -Wno-style -Wno-UNOPTFLAT -Wno-MULTIDRIVEN \
              -Wno-TIMESCALEMOD -Wno-COVERIGN

.PHONY: all compile run regress clean help

all: run

$(LOG_DIR):
	@mkdir -p $(LOG_DIR)

# Parametre profili yoksa üret (varsa dokunma — ana makefile'ın seçtiği
# profili ezmemek için; bilinçli değiştirme RTL_PROFILE ile yapılır).
$(PROFILE_SVH):
	@mkdir -p $(RTL_GEN_DIR)
	python3 $(GEN_PROFILE_PY) $(RTL_PROFILE) --out $@

check-tools:
ifeq ($(SIM),questa)
	@command -v vlog >/dev/null 2>&1 || { \
		echo "Hata: SIM=questa secili, ama 'vlog' PATH icinde bulunamadi."; \
		echo "Questa/ModelSim kurulumunu source edin ya da SIM=vcs / SIM=xrun kullanin."; \
		exit 127; \
	}
	@command -v vsim >/dev/null 2>&1 || { \
		echo "Hata: SIM=questa secili, ama 'vsim' PATH icinde bulunamadi."; \
		echo "Questa/ModelSim kurulumunu source edin ya da SIM=vcs / SIM=xrun kullanin."; \
		exit 127; \
	}
else ifeq ($(SIM),vcs)
	@command -v vcs >/dev/null 2>&1 || { \
		echo "Hata: SIM=vcs secili, ama 'vcs' PATH icinde bulunamadi."; \
		exit 127; \
	}
else ifeq ($(SIM),xrun)
	@command -v xrun >/dev/null 2>&1 || { \
		echo "Hata: SIM=xrun secili, ama 'xrun' PATH icinde bulunamadi."; \
		exit 127; \
	}
else ifeq ($(SIM),verilator)
	@command -v verilator >/dev/null 2>&1 || { \
		echo "Hata: 'verilator' PATH icinde bulunamadi."; \
		exit 127; \
	}
	@ver=$$(verilator --version | awk '{print $$2}'); \
	min=5.048; \
	lo=$$(printf '%s\n%s\n' "$$min" "$$ver" | sort -V | head -1); \
	if [ "$$lo" != "$$min" ]; then \
		echo "Hata: Verilator $$ver bulundu; UVM icin >= $$min gerekli."; \
		echo "Guncelleme: https://verilator.org/guide/latest/install.html"; \
		exit 1; \
	fi
	@test -f "$(VL_UVM_PKG)" || { \
		echo "Hata: Duzlestirilmis UVM paketi yok: $(VL_UVM_PKG)"; \
		exit 1; \
	}
	@command -v $${VERILATOR_SOLVER:-z3} >/dev/null 2>&1 || { \
		echo "Hata: SMT cozucu yok. Verilator'un constrained-random cozumu"; \
		echo "harici cozucu ister (varsayilan: z3). Kurulum:"; \
		echo "  sudo apt install z3        # ya da"; \
		echo "  pip install --user z3-solver   (~/.local/bin PATH'te olmali)"; \
		echo "Farkli cozucu icin: export VERILATOR_SOLVER=cvc5"; \
		exit 1; \
	}
else
	$(error Bilinmeyen SIM=$(SIM); verilator/questa/vcs/xrun kullanin)
endif

# ============================================================================
# Derleme
# ============================================================================
# Verilator: gerçek iş, kaynak bağımlılıklarıyla $(VL_BIN) hedefinde.
# (Kaynaklar değişmediyse ne verilation ne C++ derlemesi tekrarlanır.)
ifeq ($(SIM),verilator)
compile: $(VL_BIN)
endif

$(VL_BIN): $(VL_RTL_SRCS) $(DV_SRCS) $(DV_HDRS) $(RTL_HDRS) $(VL_UVM_PKG) $(UVM_DIR)/verilator/uvm_macros.svh $(PROFILE_SVH) | $(LOG_DIR)
	cd $(ROOT_DIR) && OBJCACHE=$(VL_OBJCACHE) verilator --binary --timing -j $(VL_JOBS) \
		--top-module level_v_tb_top \
		--Mdir $(VL_MDIR) \
		$(VL_WNO) \
		--build-jobs $(VL_JOBS) \
		-CFLAGS "$(VL_OPT)" \
		$(VL_UVM_PKG) \
		+incdir+$(UVM_DIR)/verilator $(INCDIRS) \
		$(VL_RTL_SRCS) $(DV_SRCS) \
		2>&1 | tee $(LOG_DIR)/verilator_compile.log | grep -E "%Error|%Warning" || true
	@test -x $(VL_BIN) || { \
		echo "Hata: Verilator derlemesi basarisiz — $(LOG_DIR)/verilator_compile.log"; \
		exit 1; \
	}

compile: check-tools $(PROFILE_SVH) | $(LOG_DIR)
ifeq ($(SIM),questa)
	cd $(UVM_DIR) && vlib work >/dev/null 2>&1 || true
	cd $(UVM_DIR) && vlog -sv -timescale "1ns/1ps" $(UVM_DEFINES) \
		+incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv \
		-l $(LOG_DIR)/compile_uvm.log
	cd $(UVM_DIR) && vlog -sv -timescale "1ns/1ps" $(VLOG_SUPPRESS) \
		$(UVM_DEFINES) +incdir+$(UVM_HOME)/src \
		$(INCDIRS) $(RTL_SRCS) $(DV_SRCS) \
		-l $(LOG_DIR)/compile.log
else ifeq ($(SIM),vcs)
	cd $(UVM_DIR) && vcs $(VCS_OPTS) $(INCDIRS) $(RTL_SRCS) $(DV_SRCS) \
		-top level_v_tb_top -o $(UVM_DIR)/simv
else ifeq ($(SIM),xrun)
	@true  # xrun tek adımda derleyip koşar (run hedefine bak)
else ifeq ($(SIM),verilator)
	@true
else
	$(error Bilinmeyen SIM=$(SIM); verilator/questa/vcs/xrun kullanin)
endif

# ============================================================================
# Koşum
# ============================================================================
run: compile | $(LOG_DIR)
ifeq ($(SIM),questa)
ifeq ($(GUI),1)
	cd $(UVM_DIR) && vsim $(VSIM_ARGS) -sv_seed $(SEED) \
		work.level_v_tb_top $(RUN_PLUSARGS) -l $(LOG_DIR)/$(TEST)_$(SEED).log
else
	cd $(UVM_DIR) && vsim -c $(VSIM_ARGS) -sv_seed $(SEED) \
		work.level_v_tb_top $(RUN_PLUSARGS) -do "run -all; quit -f" \
		-l $(LOG_DIR)/$(TEST)_$(SEED).log
endif
else ifeq ($(SIM),vcs)
	cd $(UVM_DIR) && ./simv +ntb_random_seed=$(SEED) $(RUN_PLUSARGS) \
		-l $(LOG_DIR)/$(TEST)_$(SEED).log
else ifeq ($(SIM),xrun)
	cd $(UVM_DIR) && xrun $(XRUN_OPTS) $(INCDIRS) $(RTL_SRCS) $(DV_SRCS) \
		-top level_v_tb_top -svseed $(SEED) $(RUN_PLUSARGS) \
		-l $(LOG_DIR)/$(TEST)_$(SEED).log
else ifeq ($(SIM),verilator)
	$(VL_BIN) +verilator+seed+$(SEED) +UVM_NO_RELNOTES $(RUN_PLUSARGS) \
		2>&1 | tee $(LOG_DIR)/$(TEST)_$(SEED).log
endif

# ============================================================================
# Mini regresyon: N farklı seed ile ayni testi koş, sonuçları derle.
# ============================================================================
regress: compile | $(LOG_DIR)
	@pass=0; fail=0; \
	for s in $$(seq 1 $(N)); do \
		echo "=== seed $$s ==="; \
		if $(MAKE) --no-print-directory run SEED=$$s TEST=$(TEST) SIM=$(SIM) \
			PLUSARGS="$(PLUSARGS)" >/dev/null 2>&1 && \
		   grep -q "TEST PASS" $(LOG_DIR)/$(TEST)_$$s.log; then \
			echo "  PASS"; pass=$$((pass+1)); \
		else \
			echo "  FAIL -> $(LOG_DIR)/$(TEST)_$$s.log"; fail=$$((fail+1)); \
		fi; \
	done; \
	echo "Regresyon: $$pass PASS / $$fail FAIL"

clean:
	rm -rf $(WORK_DIR) $(UVM_DIR)/work $(LOG_DIR) $(UVM_DIR)/simv* \
	       $(UVM_DIR)/csrc $(UVM_DIR)/*.wlf $(UVM_DIR)/transcript \
	       $(UVM_DIR)/xcelium.d $(UVM_DIR)/xrun.* $(UVM_DIR)/modelsim.ini \
	       $(VL_MDIR)

help:
	@sed -n '2,30p' Makefile
