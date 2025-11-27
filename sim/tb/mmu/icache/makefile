TEST_MODULE = cache
TOP         = tb_i$(TEST_MODULE)
SRCS        =  ../../../pkg/*.sv ../../../ram/sp_bram.sv ../../../core/mmu/$(TEST_MODULE).sv $(TOP).sv
VLIB        = vlib
VLOG        = vlog
VSIM        = vsim
SIM_OPTS    =  -do "do $(TOP).do; run -all;"

all: compile sim

vlib:
	$(VLIB) work

compile: vlib
	$(VLOG) -svinputport=relaxed $(SRCS)

sim: compile
	$(VSIM) $(SIM_OPTS) $(TOP)

clean:
	-rm -rf work transcript vsim.wlf

.PHONY: all compile sim clean
