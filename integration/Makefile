#=============================================================================
# Integration Makefile
#=============================================================================
# Description: Makefile for Hilbert Transformer IP integration components
#              Supports building, testing, and validation of integration examples
#
# Features:
# - SoC integration testing
# - FPGA integration building
# - ASIC integration validation
# - Interface adapter testing
# - Performance benchmarking
# - Coverage analysis
#
# Author: Vyges Team
# License: Apache-2.0
#=============================================================================

#=============================================================================
# Configuration
#=============================================================================
PROJECT_NAME := hilbert-transformer
VERSION := 1.0.0

# Directories
INTEGRATION_DIR := .
SOC_DIR := $(INTEGRATION_DIR)/soc
FPGA_DIR := $(INTEGRATION_DIR)/fpga
ASIC_DIR := $(INTEGRATION_DIR)/asic
INTERFACES_DIR := $(INTEGRATION_DIR)/interfaces
VERIFICATION_DIR := $(INTEGRATION_DIR)/verification
EXAMPLES_DIR := $(INTEGRATION_DIR)/examples

# Build directories
BUILD_DIR := $(INTEGRATION_DIR)/build
REPORTS_DIR := $(BUILD_DIR)/reports
LOGS_DIR := $(BUILD_DIR)/logs
WAVEFORMS_DIR := $(BUILD_DIR)/waveforms

# Tools
IVERILOG := iverilog
VVP := vvp
VERILATOR := verilator
MODELSIM := vsim
VIVADO := vivado
QUARTUS := quartus_map
OPENLANE := openlane

# Parameters
DATA_WIDTH := 16
FILTER_ORDER := 64
PIPELINE_STAGES := 8
COEFF_WIDTH := 18
ACCUM_WIDTH := 32

#=============================================================================
# Default Target
#=============================================================================
.PHONY: all
all: build test

#=============================================================================
# Directory Creation
#=============================================================================
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)
	mkdir -p $(REPORTS_DIR)
	mkdir -p $(LOGS_DIR)
	mkdir -p $(WAVEFORMS_DIR)

#=============================================================================
# Build Targets
#=============================================================================
.PHONY: build
build: $(BUILD_DIR) build-soc build-fpga build-asic build-interfaces

.PHONY: build-soc
build-soc: $(BUILD_DIR)
	@echo "Building SoC integration components..."
	$(IVERILOG) -o $(BUILD_DIR)/soc_integration.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(SOC_DIR)/*.sv \
		../rtl/*.sv \
		2>&1 | tee $(LOGS_DIR)/soc_build.log

.PHONY: build-fpga
build-fpga: $(BUILD_DIR)
	@echo "Building FPGA integration components..."
	$(IVERILOG) -o $(BUILD_DIR)/fpga_integration.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(FPGA_DIR)/xilinx/*.sv \
		$(SOC_DIR)/*.sv \
		../rtl/*.sv \
		2>&1 | tee $(LOGS_DIR)/fpga_build.log

.PHONY: build-asic
build-asic: $(BUILD_DIR)
	@echo "Building ASIC integration components..."
	$(IVERILOG) -o $(BUILD_DIR)/asic_integration.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(ASIC_DIR)/*.sv \
		$(SOC_DIR)/*.sv \
		../rtl/*.sv \
		2>&1 | tee $(LOGS_DIR)/asic_build.log

.PHONY: build-interfaces
build-interfaces: $(BUILD_DIR)
	@echo "Building interface adapters..."
	$(IVERILOG) -o $(BUILD_DIR)/interfaces.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		$(INTERFACES_DIR)/*.sv \
		$(SOC_DIR)/*.sv \
		../rtl/*.sv \
		2>&1 | tee $(LOGS_DIR)/interfaces_build.log

#=============================================================================
# Test Targets
#=============================================================================
.PHONY: test
test: test-soc test-fpga test-asic test-interfaces test-integration

.PHONY: test-soc
test-soc: build-soc
	@echo "Testing SoC integration..."
	$(VVP) $(BUILD_DIR)/soc_integration.vvp \
		+test=soc_basic \
		+vcd=$(WAVEFORMS_DIR)/soc_test.vcd \
		2>&1 | tee $(LOGS_DIR)/soc_test.log
	@echo "SoC test completed. Check $(LOGS_DIR)/soc_test.log for results."

.PHONY: test-fpga
test-fpga: build-fpga
	@echo "Testing FPGA integration..."
	$(VVP) $(BUILD_DIR)/fpga_integration.vvp \
		+test=fpga_basic \
		+vcd=$(WAVEFORMS_DIR)/fpga_test.vcd \
		2>&1 | tee $(LOGS_DIR)/fpga_test.log
	@echo "FPGA test completed. Check $(LOGS_DIR)/fpga_test.log for results."

.PHONY: test-asic
test-asic: build-asic
	@echo "Testing ASIC integration..."
	$(VVP) $(BUILD_DIR)/asic_integration.vvp \
		+test=asic_basic \
		+vcd=$(WAVEFORMS_DIR)/asic_test.vcd \
		2>&1 | tee $(LOGS_DIR)/asic_test.log
	@echo "ASIC test completed. Check $(LOGS_DIR)/asic_test.log for results."

.PHONY: test-interfaces
test-interfaces: build-interfaces
	@echo "Testing interface adapters..."
	$(VVP) $(BUILD_DIR)/interfaces.vvp \
		+test=interface_basic \
		+vcd=$(WAVEFORMS_DIR)/interface_test.vcd \
		2>&1 | tee $(LOGS_DIR)/interface_test.log
	@echo "Interface test completed. Check $(LOGS_DIR)/interface_test.log for results."

.PHONY: test-integration
test-integration: $(BUILD_DIR)
	@echo "Running integration testbench..."
	$(IVERILOG) -o $(BUILD_DIR)/integration_test.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(VERIFICATION_DIR)/integration_testbench.sv \
		$(SOC_DIR)/example_soc.sv \
		$(SOC_DIR)/axi_stream_adapter.sv \
		../rtl/*.sv \
		2>&1 | tee $(LOGS_DIR)/integration_build.log
	$(VVP) $(BUILD_DIR)/integration_test.vvp \
		+vcd=$(WAVEFORMS_DIR)/integration_test.vcd \
		2>&1 | tee $(LOGS_DIR)/integration_test.log
	@echo "Integration test completed. Check $(LOGS_DIR)/integration_test.log for results."

#=============================================================================
# Simulation Targets
#=============================================================================
.PHONY: sim
sim: sim-soc sim-fpga sim-asic

.PHONY: sim-soc
sim-soc: build-soc
	@echo "Running SoC simulation..."
	$(VVP) $(BUILD_DIR)/soc_integration.vvp \
		+vcd=$(WAVEFORMS_DIR)/soc_sim.vcd \
		+waveform=$(WAVEFORMS_DIR)/soc_sim.gtkw

.PHONY: sim-fpga
sim-fpga: build-fpga
	@echo "Running FPGA simulation..."
	$(VVP) $(BUILD_DIR)/fpga_integration.vvp \
		+vcd=$(WAVEFORMS_DIR)/fpga_sim.vcd \
		+waveform=$(WAVEFORMS_DIR)/fpga_sim.gtkw

.PHONY: sim-asic
sim-asic: build-asic
	@echo "Running ASIC simulation..."
	$(VVP) $(BUILD_DIR)/asic_integration.vvp \
		+vcd=$(WAVEFORMS_DIR)/asic_sim.vcd \
		+waveform=$(WAVEFORMS_DIR)/asic_sim.gtkw

#=============================================================================
# Verilator Targets
#=============================================================================
.PHONY: verilator
verilator: $(BUILD_DIR)
	@echo "Running Verilator simulation..."
	$(VERILATOR) --cc \
		--exe \
		--build \
		--trace \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(VERIFICATION_DIR)/integration_testbench.sv \
		$(SOC_DIR)/example_soc.sv \
		$(SOC_DIR)/axi_stream_adapter.sv \
		../rtl/*.sv \
		--exe $(VERIFICATION_DIR)/verilator_main.cpp \
		-o $(BUILD_DIR)/verilator_sim \
		2>&1 | tee $(LOGS_DIR)/verilator_build.log
	$(BUILD_DIR)/verilator_sim \
		2>&1 | tee $(LOGS_DIR)/verilator_sim.log

#=============================================================================
# Coverage Targets
#=============================================================================
.PHONY: coverage
coverage: coverage-soc coverage-fpga coverage-asic coverage-integration

.PHONY: coverage-soc
coverage-soc: build-soc
	@echo "Running SoC coverage analysis..."
	$(VVP) $(BUILD_DIR)/soc_integration.vvp \
		+coverage \
		+coverage_file=$(REPORTS_DIR)/soc_coverage.ucdb \
		2>&1 | tee $(LOGS_DIR)/soc_coverage.log

.PHONY: coverage-fpga
coverage-fpga: build-fpga
	@echo "Running FPGA coverage analysis..."
	$(VVP) $(BUILD_DIR)/fpga_integration.vvp \
		+coverage \
		+coverage_file=$(REPORTS_DIR)/fpga_coverage.ucdb \
		2>&1 | tee $(LOGS_DIR)/fpga_coverage.log

.PHONY: coverage-asic
coverage-asic: build-asic
	@echo "Running ASIC coverage analysis..."
	$(VVP) $(BUILD_DIR)/asic_integration.vvp \
		+coverage \
		+coverage_file=$(REPORTS_DIR)/asic_coverage.ucdb \
		2>&1 | tee $(LOGS_DIR)/asic_coverage.log

.PHONY: coverage-integration
coverage-integration: $(BUILD_DIR)
	@echo "Running integration coverage analysis..."
	$(IVERILOG) -o $(BUILD_DIR)/integration_coverage.vvp \
		-DDATA_WIDTH=$(DATA_WIDTH) \
		-DFILTER_ORDER=$(FILTER_ORDER) \
		-DPIPELINE_STAGES=$(PIPELINE_STAGES) \
		-DCOEFF_WIDTH=$(COEFF_WIDTH) \
		-DACCUM_WIDTH=$(ACCUM_WIDTH) \
		$(VERIFICATION_DIR)/integration_testbench.sv \
		$(SOC_DIR)/example_soc.sv \
		$(SOC_DIR)/axi_stream_adapter.sv \
		../rtl/*.sv \
		+coverage \
		2>&1 | tee $(LOGS_DIR)/integration_coverage_build.log
	$(VVP) $(BUILD_DIR)/integration_coverage.vvp \
		+coverage \
		+coverage_file=$(REPORTS_DIR)/integration_coverage.ucdb \
		2>&1 | tee $(LOGS_DIR)/integration_coverage.log

#=============================================================================
# Performance Targets
#=============================================================================
.PHONY: performance
performance: performance-soc performance-fpga performance-asic

.PHONY: performance-soc
performance-soc: build-soc
	@echo "Running SoC performance analysis..."
	$(VVP) $(BUILD_DIR)/soc_integration.vvp \
		+performance \
		+performance_file=$(REPORTS_DIR)/soc_performance.txt \
		2>&1 | tee $(LOGS_DIR)/soc_performance.log

.PHONY: performance-fpga
performance-fpga: build-fpga
	@echo "Running FPGA performance analysis..."
	$(VVP) $(BUILD_DIR)/fpga_integration.vvp \
		+performance \
		+performance_file=$(REPORTS_DIR)/fpga_performance.txt \
		2>&1 | tee $(LOGS_DIR)/fpga_performance.log

.PHONY: performance-asic
performance-asic: build-asic
	@echo "Running ASIC performance analysis..."
	$(VVP) $(BUILD_DIR)/asic_integration.vvp \
		+performance \
		+performance_file=$(REPORTS_DIR)/asic_performance.txt \
		2>&1 | tee $(LOGS_DIR)/asic_performance.log

#=============================================================================
# FPGA Synthesis Targets
#=============================================================================
.PHONY: fpga-synth
fpga-synth: $(BUILD_DIR)
	@echo "Running FPGA synthesis..."
	$(VIVADO) -mode batch -source $(FPGA_DIR)/xilinx/synthesis.tcl \
		-tclargs $(BUILD_DIR) $(FPGA_DIR)/xilinx \
		2>&1 | tee $(LOGS_DIR)/fpga_synthesis.log

.PHONY: fpga-impl
fpga-impl: fpga-synth
	@echo "Running FPGA implementation..."
	$(VIVADO) -mode batch -source $(FPGA_DIR)/xilinx/implementation.tcl \
		-tclargs $(BUILD_DIR) $(FPGA_DIR)/xilinx \
		2>&1 | tee $(LOGS_DIR)/fpga_implementation.log

#=============================================================================
# ASIC Synthesis Targets
#=============================================================================
.PHONY: asic-synth
asic-synth: $(BUILD_DIR)
	@echo "Running ASIC synthesis..."
	$(OPENLANE) -design $(ASIC_DIR)/openlane/config.tcl \
		-run_synthesis \
		2>&1 | tee $(LOGS_DIR)/asic_synthesis.log

.PHONY: asic-impl
asic-impl: asic-synth
	@echo "Running ASIC implementation..."
	$(OPENLANE) -design $(ASIC_DIR)/openlane/config.tcl \
		-run_placement \
		-run_cts \
		-run_routing \
		2>&1 | tee $(LOGS_DIR)/asic_implementation.log

#=============================================================================
# Documentation Targets
#=============================================================================
.PHONY: docs
docs: $(BUILD_DIR)
	@echo "Generating integration documentation..."
	pandoc $(INTEGRATION_DIR)/README.md \
		-o $(REPORTS_DIR)/integration_documentation.pdf \
		--pdf-engine=xelatex \
		2>&1 | tee $(LOGS_DIR)/docs_generation.log

.PHONY: reports
reports: $(BUILD_DIR)
	@echo "Generating integration reports..."
	@echo "Integration Test Report" > $(REPORTS_DIR)/integration_report.txt
	@echo "======================" >> $(REPORTS_DIR)/integration_report.txt
	@echo "Generated: $(shell date)" >> $(REPORTS_DIR)/integration_report.txt
	@echo "" >> $(REPORTS_DIR)/integration_report.txt
	@echo "Test Results:" >> $(REPORTS_DIR)/integration_report.txt
	@if [ -f $(LOGS_DIR)/soc_test.log ]; then \
		echo "SoC Integration: $(shell grep -c "PASS\|FAIL" $(LOGS_DIR)/soc_test.log || echo "Not run")" >> $(REPORTS_DIR)/integration_report.txt; \
	fi
	@if [ -f $(LOGS_DIR)/fpga_test.log ]; then \
		echo "FPGA Integration: $(shell grep -c "PASS\|FAIL" $(LOGS_DIR)/fpga_test.log || echo "Not run")" >> $(REPORTS_DIR)/integration_report.txt; \
	fi
	@if [ -f $(LOGS_DIR)/asic_test.log ]; then \
		echo "ASIC Integration: $(shell grep -c "PASS\|FAIL" $(LOGS_DIR)/asic_test.log || echo "Not run")" >> $(REPORTS_DIR)/integration_report.txt; \
	fi
	@if [ -f $(LOGS_DIR)/integration_test.log ]; then \
		echo "Integration Testbench: $(shell grep -c "PASS\|FAIL" $(LOGS_DIR)/integration_test.log || echo "Not run")" >> $(REPORTS_DIR)/integration_report.txt; \
	fi

#=============================================================================
# Clean Targets
#=============================================================================
.PHONY: clean
clean:
	@echo "Cleaning integration build files..."
	rm -rf $(BUILD_DIR)
	rm -f *.vcd *.gtkw *.log

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning log files..."
	rm -f $(LOGS_DIR)/*.log

.PHONY: clean-waveforms
clean-waveforms:
	@echo "Cleaning waveform files..."
	rm -f $(WAVEFORMS_DIR)/*.vcd $(WAVEFORMS_DIR)/*.gtkw

.PHONY: clean-reports
clean-reports:
	@echo "Cleaning report files..."
	rm -f $(REPORTS_DIR)/*.txt $(REPORTS_DIR)/*.pdf $(REPORTS_DIR)/*.ucdb

#=============================================================================
# Help Target
#=============================================================================
.PHONY: help
help:
	@echo "Hilbert Transformer IP - Integration Makefile"
	@echo "============================================="
	@echo ""
	@echo "Available targets:"
	@echo "  all              - Build and test all integration components"
	@echo "  build            - Build all integration components"
	@echo "  test             - Run all integration tests"
	@echo "  sim              - Run all simulations"
	@echo "  coverage         - Run coverage analysis"
	@echo "  performance      - Run performance analysis"
	@echo "  fpga-synth       - Run FPGA synthesis"
	@echo "  fpga-impl        - Run FPGA implementation"
	@echo "  asic-synth       - Run ASIC synthesis"
	@echo "  asic-impl        - Run ASIC implementation"
	@echo "  docs             - Generate documentation"
	@echo "  reports          - Generate test reports"
	@echo "  clean            - Clean all build files"
	@echo "  help             - Show this help message"
	@echo ""
	@echo "Individual component targets:"
	@echo "  build-soc        - Build SoC integration"
	@echo "  build-fpga       - Build FPGA integration"
	@echo "  build-asic       - Build ASIC integration"
	@echo "  test-soc         - Test SoC integration"
	@echo "  test-fpga        - Test FPGA integration"
	@echo "  test-asic        - Test ASIC integration"
	@echo "  sim-soc          - Simulate SoC integration"
	@echo "  sim-fpga         - Simulate FPGA integration"
	@echo "  sim-asic         - Simulate ASIC integration"
	@echo ""
	@echo "Configuration:"
	@echo "  DATA_WIDTH       = $(DATA_WIDTH)"
	@echo "  FILTER_ORDER     = $(FILTER_ORDER)"
	@echo "  PIPELINE_STAGES  = $(PIPELINE_STAGES)"
	@echo "  COEFF_WIDTH      = $(COEFF_WIDTH)"
	@echo "  ACCUM_WIDTH      = $(ACCUM_WIDTH)"

#=============================================================================
# Validation Targets
#=============================================================================
.PHONY: validate
validate: validate-syntax validate-protocol validate-timing

.PHONY: validate-syntax
validate-syntax: $(BUILD_DIR)
	@echo "Validating syntax..."
	@for file in $(SOC_DIR)/*.sv $(FPGA_DIR)/xilinx/*.sv $(ASIC_DIR)/*.sv $(INTERFACES_DIR)/*.sv $(VERIFICATION_DIR)/*.sv; do \
		if [ -f $$file ]; then \
			echo "Checking $$file..."; \
			$(IVERILOG) -t null $$file 2>&1 | tee -a $(LOGS_DIR)/syntax_validation.log; \
		fi; \
	done

.PHONY: validate-protocol
validate-protocol: build-interfaces
	@echo "Validating protocol compliance..."
	$(VVP) $(BUILD_DIR)/interfaces.vvp \
		+protocol_check \
		2>&1 | tee $(LOGS_DIR)/protocol_validation.log

.PHONY: validate-timing
validate-timing: build-soc
	@echo "Validating timing constraints..."
	$(VVP) $(BUILD_DIR)/soc_integration.vvp \
		+timing_check \
		2>&1 | tee $(LOGS_DIR)/timing_validation.log

#=============================================================================
# Regression Testing
#=============================================================================
.PHONY: regression
regression: $(BUILD_DIR)
	@echo "Running regression tests..."
	@echo "Regression Test Suite - $(shell date)" > $(REPORTS_DIR)/regression_report.txt
	@echo "=====================================" >> $(REPORTS_DIR)/regression_report.txt
	@echo "" >> $(REPORTS_DIR)/regression_report.txt
	
	@echo "Running SoC regression..." >> $(REPORTS_DIR)/regression_report.txt
	@$(MAKE) test-soc >> $(REPORTS_DIR)/regression_report.txt 2>&1 || echo "SoC regression FAILED" >> $(REPORTS_DIR)/regression_report.txt
	
	@echo "Running FPGA regression..." >> $(REPORTS_DIR)/regression_report.txt
	@$(MAKE) test-fpga >> $(REPORTS_DIR)/regression_report.txt 2>&1 || echo "FPGA regression FAILED" >> $(REPORTS_DIR)/regression_report.txt
	
	@echo "Running ASIC regression..." >> $(REPORTS_DIR)/regression_report.txt
	@$(MAKE) test-asic >> $(REPORTS_DIR)/regression_report.txt 2>&1 || echo "ASIC regression FAILED" >> $(REPORTS_DIR)/regression_report.txt
	
	@echo "Running integration regression..." >> $(REPORTS_DIR)/regression_report.txt
	@$(MAKE) test-integration >> $(REPORTS_DIR)/regression_report.txt 2>&1 || echo "Integration regression FAILED" >> $(REPORTS_DIR)/regression_report.txt
	
	@echo "Regression testing completed. Check $(REPORTS_DIR)/regression_report.txt for results."

#=============================================================================
# Continuous Integration
#=============================================================================
.PHONY: ci
ci: clean build test coverage validate regression reports
	@echo "Continuous Integration completed."
	@echo "Check $(REPORTS_DIR)/ for detailed reports."

#=============================================================================
# Release Targets
#=============================================================================
.PHONY: release
release: ci docs
	@echo "Creating integration release..."
	@mkdir -p $(BUILD_DIR)/release
	@cp -r $(SOC_DIR) $(BUILD_DIR)/release/
	@cp -r $(FPGA_DIR) $(BUILD_DIR)/release/
	@cp -r $(ASIC_DIR) $(BUILD_DIR)/release/
	@cp -r $(INTERFACES_DIR) $(BUILD_DIR)/release/
	@cp -r $(VERIFICATION_DIR) $(BUILD_DIR)/release/
	@cp -r $(EXAMPLES_DIR) $(BUILD_DIR)/release/
	@cp $(INTEGRATION_DIR)/README.md $(BUILD_DIR)/release/
	@cp $(REPORTS_DIR)/*.pdf $(BUILD_DIR)/release/
	@cp $(REPORTS_DIR)/*.txt $(BUILD_DIR)/release/
	@tar -czf $(BUILD_DIR)/$(PROJECT_NAME)-integration-$(VERSION).tar.gz -C $(BUILD_DIR) release/
	@echo "Release created: $(BUILD_DIR)/$(PROJECT_NAME)-integration-$(VERSION).tar.gz" 