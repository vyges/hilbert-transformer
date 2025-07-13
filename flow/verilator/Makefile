#==============================================================================
# Makefile: Verilator Flow for Hilbert Transformer IP
#==============================================================================
# Description: Comprehensive Verilator flow for simulation, synthesis, and analysis
#              Supports SystemVerilog testbenches, coverage analysis, and waveform generation
#
# Features:
# - SystemVerilog simulation with multiple testbenches
# - Coverage analysis and reporting
# - Waveform generation and viewing
# - Linting and code quality checks
# - Performance analysis and optimization
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
SIM = verilator

# RTL source files
RTL_SOURCES = ../../rtl/hilbert_transformer.sv
RTL_SOURCES += ../../rtl/hilbert_coefficient_rom.sv
RTL_SOURCES += ../../rtl/hilbert_delay_line.sv
RTL_SOURCES += ../../rtl/hilbert_multiplier_array.sv
RTL_SOURCES += ../../rtl/hilbert_adder_tree.sv

# Testbench files
TB_SOURCES = ../../tb/sv_tb/tb_hilbert_transformer.sv

# Directories
BUILD_DIR = build
RESULTS_DIR = results
WAVES_DIR = waves
COVERAGE_DIR = coverage
REPORTS_DIR = reports

# Verilator configuration
VERILATOR_VERSION = 4.0+
VERILATOR_FLAGS = --cc --exe --build
VERILATOR_FLAGS += --trace
VERILATOR_FLAGS += --coverage
VERILATOR_FLAGS += --trace-structs
VERILATOR_FLAGS += --trace-depth 10
VERILATOR_FLAGS += -Wall -Wno-fatal
VERILATOR_FLAGS += -DVERILATOR
VERILATOR_FLAGS += -CFLAGS "-std=c++11"
VERILATOR_FLAGS += -CFLAGS "-g"
VERILATOR_FLAGS += -CFLAGS "-O2"
VERILATOR_FLAGS += -CFLAGS "-I$(BUILD_DIR)"

# Test configuration
TEST_NAME ?= all
COVERAGE ?= 1
WAVES ?= 1
GUI ?= 0
THREADS ?= 4

#==============================================================================
# Environment Setup
#==============================================================================

# Create necessary directories
$(shell mkdir -p $(BUILD_DIR) $(RESULTS_DIR) $(WAVES_DIR) $(COVERAGE_DIR) $(REPORTS_DIR))

# Set environment variables
export VERILATOR_ROOT ?= /usr/local/share/verilator
export PATH := $(VERILATOR_ROOT)/bin:$(PATH)

#==============================================================================
# Main Targets
#==============================================================================

.PHONY: all clean sim sim-sv sim-cocotb coverage waves lint synthesis help

# Default target
all: sim

# Run all simulations
sim: sim-sv sim-cocotb

# Run SystemVerilog simulation
sim-sv: $(RESULTS_DIR)/sv_simulation_results.txt

# Run cocotb simulation
sim-cocotb: $(RESULTS_DIR)/cocotb_simulation_results.txt

# Run with coverage and waves
sim-all: sim coverage waves

#==============================================================================
# SystemVerilog Simulation
#==============================================================================

$(RESULTS_DIR)/sv_simulation_results.txt: $(TB_SOURCES) $(RTL_SOURCES)
	@echo "Running SystemVerilog simulation with Verilator..."
	@mkdir -p $(RESULTS_DIR) $(WAVES_DIR)
	
	# Compile and build simulation
	verilator $(VERILATOR_FLAGS) \
		$(RTL_SOURCES) \
		$(TB_SOURCES) \
		-o $(TOPLEVEL) \
		--Mdir $(BUILD_DIR)/obj_dir
	
	# Run simulation
	$(BUILD_DIR)/obj_dir/V$(TOPLEVEL) > $@ 2>&1
	
	# Move waveform file if generated
	@if [ -f $(BUILD_DIR)/obj_dir/dump.vcd ]; then \
		mv $(BUILD_DIR)/obj_dir/dump.vcd $(WAVES_DIR)/sv_simulation.vcd; \
	fi
	
	@echo "SystemVerilog simulation completed. Results in $@"

#==============================================================================
# cocotb Simulation
#==============================================================================

$(RESULTS_DIR)/cocotb_simulation_results.txt: ../../tb/cocotb/test_hilbert_transformer.py $(RTL_SOURCES)
	@echo "Running cocotb simulation with Verilator..."
	@mkdir -p $(RESULTS_DIR) $(WAVES_DIR)
	
	COCOTB_RESULTS_FILE=$@ \
	TOPLEVEL=$(TOPLEVEL) \
	TOPLEVEL_LANG=$(TOPLEVEL_LANG) \
	MODULE=test_hilbert_transformer \
	SIM=$(SIM) \
	VERILOG_SOURCES="$(RTL_SOURCES)" \
	COMPILE_ARGS="$(VERILATOR_FLAGS)" \
	WAVES=$(WAVES) \
	COVERAGE=$(COVERAGE) \
	python -m pytest ../../tb/cocotb/test_hilbert_transformer.py -v \
		--tb=short \
		--junitxml=$(RESULTS_DIR)/cocotb_results.xml \
		> $@ 2>&1
	
	@echo "cocotb simulation completed. Results in $@"

#==============================================================================
# Coverage Analysis
#==============================================================================

coverage: $(REPORTS_DIR)/coverage_report.html

$(REPORTS_DIR)/coverage_report.html: sim
	@echo "Generating coverage report..."
	@mkdir -p $(COVERAGE_DIR) $(REPORTS_DIR)
	
	# Generate coverage report
	verilator_coverage --rank --annotate $(COVERAGE_DIR) \
		--html $(REPORTS_DIR)/coverage_report.html \
		$(COVERAGE_DIR)/*.dat
	
	# Generate coverage summary
	verilator_coverage --rank --annotate $(COVERAGE_DIR) \
		--write $(REPORTS_DIR)/coverage_summary.txt \
		$(COVERAGE_DIR)/*.dat
	
	@echo "Coverage report generated: $(REPORTS_DIR)/coverage_report.html"

#==============================================================================
# Waveform Generation
#==============================================================================

waves: $(WAVES_DIR)/simulation_waves.vcd

$(WAVES_DIR)/simulation_waves.vcd: sim
	@echo "Generating waveforms..."
	@mkdir -p $(WAVES_DIR)
	
	# Combine waveform files if multiple exist
	@if [ -f $(WAVES_DIR)/sv_simulation.vcd ]; then \
		cp $(WAVES_DIR)/sv_simulation.vcd $(WAVES_DIR)/simulation_waves.vcd; \
	fi
	
	@echo "Waveforms generated in $(WAVES_DIR)/"

#==============================================================================
# GUI Simulation
#==============================================================================

gui: WAVES=1
gui: sim
	@echo "Starting GUI simulation..."
	
	@if [ -f $(WAVES_DIR)/simulation_waves.vcd ]; then \
		gtkwave $(WAVES_DIR)/simulation_waves.vcd & \
	else \
		echo "No waveform file found. Run 'make waves' first."; \
	fi

#==============================================================================
# Linting and Code Quality
#==============================================================================

lint:
	@echo "Running linting checks..."
	verilator --lint-only $(VERILATOR_FLAGS) \
		$(RTL_SOURCES) $(TB_SOURCES) \
		--lint-output $(REPORTS_DIR)/lint_report.txt

lint-html: lint
	@echo "Generating HTML lint report..."
	verilator --lint-only $(VERILATOR_FLAGS) \
		$(RTL_SOURCES) $(TB_SOURCES) \
		--lint-output $(REPORTS_DIR)/lint_report.html \
		--lint-html

#==============================================================================
# Synthesis Analysis
#==============================================================================

synthesis:
	@echo "Running synthesis analysis..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate synthesis report
	verilator --lint-only --xml-only $(RTL_SOURCES) \
		-o $(REPORTS_DIR)/synthesis_report.xml
	
	# Generate statistics
	verilator --lint-only --stats $(RTL_SOURCES) \
		-o $(REPORTS_DIR)/synthesis_stats.txt

#==============================================================================
# Performance Analysis
#==============================================================================

performance: sim
	@echo "Running performance analysis..."
	@mkdir -p $(REPORTS_DIR)
	
	# Extract performance metrics from simulation results
	@if [ -f $(RESULTS_DIR)/sv_simulation_results.txt ]; then \
		grep -E "(throughput|latency|frequency)" $(RESULTS_DIR)/sv_simulation_results.txt > $(REPORTS_DIR)/performance_metrics.txt; \
	fi
	
	@if [ -f $(RESULTS_DIR)/cocotb_simulation_results.txt ]; then \
		grep -E "(throughput|latency|frequency)" $(RESULTS_DIR)/cocotb_simulation_results.txt >> $(REPORTS_DIR)/performance_metrics.txt; \
	fi
	
	@echo "Performance analysis completed: $(REPORTS_DIR)/performance_metrics.txt"

#==============================================================================
# Regression Testing
#==============================================================================

regression: clean sim-all performance
	@echo "Running regression test suite..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate regression report
	@echo "Regression Test Results" > $(REPORTS_DIR)/regression_report.txt
	@echo "=======================" >> $(REPORTS_DIR)/regression_report.txt
	@echo "Date: $(shell date)" >> $(REPORTS_DIR)/regression_report.txt
	@echo "" >> $(REPORTS_DIR)/regression_report.txt
	
	# Check simulation results
	@if [ -f $(RESULTS_DIR)/sv_simulation_results.txt ]; then \
		echo "SystemVerilog Tests:" >> $(REPORTS_DIR)/regression_report.txt; \
		grep -E "(PASSED|FAILED|ERROR)" $(RESULTS_DIR)/sv_simulation_results.txt >> $(REPORTS_DIR)/regression_report.txt; \
		echo "" >> $(REPORTS_DIR)/regression_report.txt; \
	fi
	
	@if [ -f $(RESULTS_DIR)/cocotb_simulation_results.txt ]; then \
		echo "cocotb Tests:" >> $(REPORTS_DIR)/regression_report.txt; \
		grep -E "(PASSED|FAILED|ERROR)" $(RESULTS_DIR)/cocotb_simulation_results.txt >> $(REPORTS_DIR)/regression_report.txt; \
		echo "" >> $(REPORTS_DIR)/regression_report.txt; \
	fi
	
	# Check coverage
	@if [ -f $(REPORTS_DIR)/coverage_summary.txt ]; then \
		echo "Coverage Summary:" >> $(REPORTS_DIR)/regression_report.txt; \
		cat $(REPORTS_DIR)/coverage_summary.txt >> $(REPORTS_DIR)/regression_report.txt; \
	fi
	
	@echo "Regression testing completed: $(REPORTS_DIR)/regression_report.txt"

#==============================================================================
# Documentation
#==============================================================================

docs:
	@echo "Generating documentation..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate module documentation
	verilator --lint-only --xml-only $(RTL_SOURCES) \
		-o $(REPORTS_DIR)/module_docs.xml
	
	# Generate test documentation
	@echo "Test Documentation" > $(REPORTS_DIR)/test_docs.txt
	@echo "=================" >> $(REPORTS_DIR)/test_docs.txt
	@echo "" >> $(REPORTS_DIR)/test_docs.txt
	@echo "SystemVerilog Tests:" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Functional tests with sine wave verification" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Performance tests with throughput measurement" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Corner case tests with edge conditions" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Error tests with protocol violations" >> $(REPORTS_DIR)/test_docs.txt
	@echo "" >> $(REPORTS_DIR)/test_docs.txt
	@echo "cocotb Tests:" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Python-based test scenarios" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Coverage analysis and reporting" >> $(REPORTS_DIR)/test_docs.txt
	@echo "- Waveform generation for debugging" >> $(REPORTS_DIR)/test_docs.txt

#==============================================================================
# Cleanup
#==============================================================================

clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(BUILD_DIR)
	rm -rf $(RESULTS_DIR)
	rm -rf $(WAVES_DIR)
	rm -rf $(COVERAGE_DIR)
	rm -rf $(REPORTS_DIR)
	rm -rf obj_dir
	rm -rf __pycache__
	rm -rf *.pyc
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
	@echo "Verilator Flow for Hilbert Transformer IP"
	@echo "========================================="
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Run all simulations (default)"
	@echo "  sim          - Run all simulations"
	@echo "  sim-sv       - Run SystemVerilog simulation only"
	@echo "  sim-cocotb   - Run cocotb simulation only"
	@echo "  sim-all      - Run all simulations with coverage and waves"
	@echo "  coverage     - Generate coverage report"
	@echo "  waves        - Generate waveform files"
	@echo "  gui          - Start GUI simulation"
	@echo "  lint         - Run linting checks"
	@echo "  lint-html    - Generate HTML lint report"
	@echo "  synthesis    - Run synthesis analysis"
	@echo "  performance  - Run performance analysis"
	@echo "  regression   - Run complete regression test suite"
	@echo "  docs         - Generate documentation"
	@echo "  clean        - Clean build artifacts"
	@echo "  distclean    - Deep clean"
	@echo "  help         - Show this help"
	@echo ""
	@echo "Environment variables:"
	@echo "  TEST_NAME    - Specific test to run"
	@echo "  COVERAGE     - Enable coverage (1/0)"
	@echo "  WAVES        - Enable waveform generation (1/0)"
	@echo "  GUI          - Enable GUI mode (1/0)"
	@echo "  THREADS      - Number of threads for parallel execution"
	@echo ""
	@echo "Examples:"
	@echo "  make sim-sv"
	@echo "  make sim-all"
	@echo "  make regression"
	@echo "  make gui"

#==============================================================================
# Include cocotb Makefile
#==============================================================================

include $(shell cocotb-config --makefiles)/Makefile.sim 