# Checks for the Verilog that `lake exe adder_netlist` prints.
#
#   make netlist   regenerate sklansky_adder_$(WIDTH).v and its checker
#   make lint      Verilator lint, with every warning on
#   make equiv     a Yosys SAT proof that the adder equals + for every input
#
# OSS_YOSYS is the open-source Yosys. Override it for your own install.

WIDTH     ?= 32
VERILATOR ?= verilator
OSS_YOSYS ?= yosys
ADDER     := sklansky_adder_$(WIDTH)

.PHONY: netlist lint equiv

netlist:
	cd ../.. && lake exe adder_netlist $(WIDTH)

$(ADDER).v $(ADDER)_check.v:
	cd ../.. && lake exe adder_netlist $(WIDTH)

lint: $(ADDER).v $(ADDER)_check.v
	$(VERILATOR) --lint-only -Wall --top-module $(ADDER)_check $(ADDER)_check.v $(ADDER).v

equiv: $(ADDER).v $(ADDER)_check.v
	$(OSS_YOSYS) -q -p "read_verilog $(ADDER).v $(ADDER)_check.v; \
	  prep -top $(ADDER)_check; flatten; sat -verify -prove ok 1"
	@echo "$(ADDER) equals + for every input"
