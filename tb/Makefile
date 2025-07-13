#==============================================================================
# Makefile: Hilbert Transformer Test Suite
#==============================================================================
# Description: Comprehensive test automation for Hilbert Transformer IP
#              Supports SystemVerilog and cocotb testbenches
#              Includes coverage analysis and waveform generation
#
# Features:
# - SystemVerilog testbench execution
# - cocotb testbench execution
# - Multiple simulator support
# - Coverage analysis and reporting
# - Waveform generation
# - Automated regression testing
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

#==============================================================================
# Configuration
#==============================================================================
TOPLEVEL = hilbert_transformer
TOPLEVEL_LANG = verilog
MODULE = test_hilbert_transformer

# Simulator configuration
SIM ?= verilator
VERILOG_SOURCES = ../rtl/hilbert_transformer.sv
VERILOG_SOURCES += ../rtl/hilbert_coefficient_rom.sv
VERILOG_SOURCES += ../rtl/hilbert_delay_line.sv
VERILOG_SOURCES += ../rtl/hilbert_multiplier_array.sv
VERILOG_SOURCES += ../rtl/hilbert_adder_tree.sv

# Test configuration
TEST_NAME ?= all
COVERAGE ?= 1
WAVES ?= 1
GUI ?= 0

# Directories
RTL_DIR = ../rtl
TB_DIR = .
COCOTB_DIR = cocotb
SV_TB_DIR = sv_tb
RESULTS_DIR = results
WAVES_DIR = waves
COVERAGE_DIR = coverage

#==============================================================================
# Simulator-specific Configuration
#==============================================================================

ifeq ($(SIM),verilator)
    COMPILE_ARGS += -Wall -Wno-fatal
    COMPILE_ARGS += -DVERILATOR
    COMPILE_ARGS += --trace
    COMPILE_ARGS += --coverage
    EXTRA_ARGS += --trace-structs
    EXTRA_ARGS += --trace-depth 10
    VERILATOR_FLAGS += -CFLAGS "-std=c++11"
    VERILATOR_FLAGS += -CFLAGS "-g"
    VERILATOR_FLAGS += -CFLAGS "-O2"
endif

ifeq ($(SIM),icarus)
    COMPILE_ARGS += -g2012
    COMPILE_ARGS += -Wall
    EXTRA_ARGS += -I$(RTL_DIR)
endif

ifeq ($(SIM),vcs)
    COMPILE_ARGS += -full64
    COMPILE_ARGS += -sverilog
    COMPILE_ARGS += +v2k
    COMPILE_ARGS += -debug_all
    EXTRA_ARGS += -cm line+cond+fsm+branch+tgl
    EXTRA_ARGS += -cm_dir $(COVERAGE_DIR)
endif

ifeq ($(SIM),xcelium)
    COMPILE_ARGS += -64bit
    COMPILE_ARGS += -sv
    COMPILE_ARGS += -debug_all
    EXTRA_ARGS += -coverage all
    EXTRA_ARGS += -covdut $(TOPLEVEL)
endif

#==============================================================================
# Environment Setup
#==============================================================================

# Create necessary directories
$(shell mkdir -p $(RESULTS_DIR) $(WAVES_DIR) $(COVERAGE_DIR))

# Set environment variables
export COCOTB_REDUCED_LOG_FMT=1
export PYTHONPATH := $(COCOTB_DIR):$(PYTHONPATH)

#==============================================================================
# Main Targets
#==============================================================================

.PHONY: all clean test test-sv test-cocotb test-all coverage waves help

# Default target
all: test

# Run all tests
test: test-sv test-cocotb

# Run SystemVerilog tests
test-sv: $(RESULTS_DIR)/sv_test_results.txt

# Run cocotb tests
test-cocotb: $(RESULTS_DIR)/cocotb_test_results.txt

# Run all tests with coverage
test-all: test coverage waves

#==============================================================================
# SystemVerilog Test Execution
#==============================================================================

$(RESULTS_DIR)/sv_test_results.txt: $(SV_TB_DIR)/tb_hilbert_transformer.sv $(VERILOG_SOURCES)
	@echo "Running SystemVerilog tests with $(SIM)..."
	@mkdir -p $(RESULTS_DIR)
	@mkdir -p $(WAVES_DIR)
	
ifeq ($(SIM),verilator)
	verilator --cc --exe --build $(VERILATOR_FLAGS) \
		$(COMPILE_ARGS) \
		$(VERILOG_SOURCES) \
		$(SV_TB_DIR)/tb_hilbert_transformer.sv \
		-o $(TOPLEVEL) \
		$(EXTRA_ARGS)
	./obj_dir/$(TOPLEVEL) > $@ 2>&1
endif

ifeq ($(SIM),icarus)
	iverilog $(COMPILE_ARGS) \
		$(VERILOG_SOURCES) \
		$(SV_TB_DIR)/tb_hilbert_transformer.sv \
		-o $(TOPLEVEL)_sim \
		$(EXTRA_ARGS)
	vvp $(TOPLEVEL)_sim > $@ 2>&1
endif

ifeq ($(SIM),vcs)
	vcs $(COMPILE_ARGS) \
		$(VERILOG_SOURCES) \
		$(SV_TB_DIR)/tb_hilbert_transformer.sv \
		-o $(TOPLEVEL)_sim \
		$(EXTRA_ARGS)
	./$(TOPLEVEL)_sim > $@ 2>&1
endif

ifeq ($(SIM),xcelium)
	xrun $(COMPILE_ARGS) \
		$(VERILOG_SOURCES) \
		$(SV_TB_DIR)/tb_hilbert_transformer.sv \
		$(EXTRA_ARGS) \
		> $@ 2>&1
endif

	@echo "SystemVerilog tests completed. Results in $@"

#==============================================================================
# cocotb Test Execution
#==============================================================================

$(RESULTS_DIR)/cocotb_test_results.txt: $(COCOTB_DIR)/test_hilbert_transformer.py $(VERILOG_SOURCES)
	@echo "Running cocotb tests with $(SIM)..."
	@mkdir -p $(RESULTS_DIR)
	@mkdir -p $(WAVES_DIR)
	
	COCOTB_RESULTS_FILE=$@ \
	TOPLEVEL=$(TOPLEVEL) \
	TOPLEVEL_LANG=$(TOPLEVEL_LANG) \
	MODULE=$(MODULE) \
	SIM=$(SIM) \
	VERILOG_SOURCES="$(VERILOG_SOURCES)" \
	COMPILE_ARGS="$(COMPILE_ARGS)" \
	EXTRA_ARGS="$(EXTRA_ARGS)" \
	WAVES=$(WAVES) \
	COVERAGE=$(COVERAGE) \
	python -m pytest $(COCOTB_DIR)/test_hilbert_transformer.py -v \
		--tb=short \
		--junitxml=$(RESULTS_DIR)/cocotb_results.xml \
		> $@ 2>&1

	@echo "cocotb tests completed. Results in $@"

#==============================================================================
# Coverage Analysis
#==============================================================================

coverage: $(RESULTS_DIR)/coverage_report.html

$(RESULTS_DIR)/coverage_report.html: test
	@echo "Generating coverage report..."
	@mkdir -p $(COVERAGE_DIR)
	
ifeq ($(SIM),verilator)
	verilator_coverage --rank --annotate $(COVERAGE_DIR) \
		--html $(RESULTS_DIR)/coverage_report.html \
		$(COVERAGE_DIR)/*.dat
endif

ifeq ($(SIM),vcs)
	dve -full64 -cov -dir $(COVERAGE_DIR) &
endif

ifeq ($(SIM),xcelium)
	imc -execcmd "merge $(COVERAGE_DIR)/*.ucm -out $(COVERAGE_DIR)/merged.ucm; \
		report -html -out $(RESULTS_DIR)/coverage_report.html \
		-detail -all -overwrite $(COVERAGE_DIR)/merged.ucm"
endif

	@echo "Coverage report generated: $(RESULTS_DIR)/coverage_report.html"

#==============================================================================
# Waveform Generation
#==============================================================================

waves: $(WAVES_DIR)/waves.vcd

$(WAVES_DIR)/waves.vcd: test
	@echo "Generating waveforms..."
	@mkdir -p $(WAVES_DIR)
	
ifeq ($(SIM),verilator)
	@if [ -f dump.vcd ]; then mv dump.vcd $(WAVES_DIR)/waves.vcd; fi
endif

ifeq ($(SIM),icarus)
	@if [ -f dump.vcd ]; then mv dump.vcd $(WAVES_DIR)/waves.vcd; fi
endif

ifeq ($(SIM),vcs)
	@if [ -f $(TOPLEVEL)_sim.vpd ]; then mv $(TOPLEVEL)_sim.vpd $(WAVES_DIR)/; fi
endif

ifeq ($(SIM),xcelium)
	@if [ -f $(TOPLEVEL).shm ]; then mv $(TOPLEVEL).shm $(WAVES_DIR)/; fi
endif

	@echo "Waveforms generated in $(WAVES_DIR)/"

#==============================================================================
# GUI Simulation
#==============================================================================

gui: WAVES=1
gui: test
	@echo "Starting GUI simulation..."
	
ifeq ($(SIM),verilator)
	gtkwave $(WAVES_DIR)/waves.vcd &
endif

ifeq ($(SIM),icarus)
	gtkwave $(WAVES_DIR)/waves.vcd &
endif

ifeq ($(SIM),vcs)
	dve -full64 -vpd $(WAVES_DIR)/$(TOPLEVEL)_sim.vpd &
endif

ifeq ($(SIM),xcelium)
	simvision $(WAVES_DIR)/$(TOPLEVEL).shm &
endif

#==============================================================================
# Linting and Code Quality
#==============================================================================

lint:
	@echo "Running linting checks..."
	verilator --lint-only $(VERILOG_SOURCES) $(SV_TB_DIR)/tb_hilbert_transformer.sv

synthesis:
	@echo "Running synthesis check..."
	yosys -p "read_verilog $(VERILOG_SOURCES); synth -top $(TOPLEVEL); stat"

#==============================================================================
# Documentation
#==============================================================================

docs:
	@echo "Generating documentation..."
	@mkdir -p docs
	verilator --lint-only --xml-only $(VERILOG_SOURCES) -o docs/module_docs.xml

#==============================================================================
# Cleanup
#==============================================================================

clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(RESULTS_DIR)
	rm -rf $(WAVES_DIR)
	rm -rf $(COVERAGE_DIR)
	rm -rf obj_dir
	rm -rf __pycache__
	rm -rf *.pyc
	rm -f $(TOPLEVEL)_sim
	rm -f dump.vcd
	rm -f *.vpd
	rm -f *.shm
	rm -f *.ucm
	rm -f *.dat
	rm -f *.xml
	rm -f *.log

distclean: clean
	@echo "Deep cleaning..."
	rm -rf .pytest_cache
	rm -rf .cocotb
	rm -rf sim_build

#==============================================================================
# Help
#==============================================================================

help:
	@echo "Hilbert Transformer Test Suite"
	@echo "=============================="
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Run all tests (default)"
	@echo "  test         - Run all tests"
	@echo "  test-sv      - Run SystemVerilog tests only"
	@echo "  test-cocotb  - Run cocotb tests only"
	@echo "  test-all     - Run all tests with coverage and waves"
	@echo "  coverage     - Generate coverage report"
	@echo "  waves        - Generate waveform files"
	@echo "  gui          - Start GUI simulation"
	@echo "  lint         - Run linting checks"
	@echo "  synthesis    - Run synthesis check"
	@echo "  docs         - Generate documentation"
	@echo "  clean        - Clean build artifacts"
	@echo "  distclean    - Deep clean"
	@echo "  help         - Show this help"
	@echo ""
	@echo "Environment variables:"
	@echo "  SIM          - Simulator (verilator, icarus, vcs, xcelium)"
	@echo "  COVERAGE     - Enable coverage (1/0)"
	@echo "  WAVES        - Enable waveform generation (1/0)"
	@echo "  GUI          - Enable GUI mode (1/0)"
	@echo ""
	@echo "Examples:"
	@echo "  make SIM=verilator test"
	@echo "  make SIM=vcs test-all"
	@echo "  make SIM=icarus gui"

#==============================================================================
# Include cocotb Makefile
#==============================================================================

include $(shell cocotb-config --makefiles)/Makefile.sim

