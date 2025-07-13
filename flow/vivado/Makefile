#==============================================================================
# Makefile: Vivado Flow for Hilbert Transformer IP
#==============================================================================
# Description: Comprehensive Vivado flow for FPGA synthesis, implementation,
#              and bitstream generation with simulation and analysis capabilities
#
# Features:
# - RTL synthesis and optimization
# - Implementation with placement and routing
# - Bitstream generation for FPGA programming
# - Simulation with SystemVerilog and cocotb
# - Timing analysis and constraint validation
# - Resource utilization analysis
# - Power analysis and optimization
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

#==============================================================================
# Configuration
#==============================================================================
PROJECT_NAME = hilbert_transformer
TOPLEVEL = hilbert_transformer
PART = xc7a35ticsg324-1L
BOARD = arty-a7-35
VIVADO_VERSION = 2023.1

# RTL source files
RTL_SOURCES = ../../rtl/hilbert_transformer.sv
RTL_SOURCES += ../../rtl/hilbert_coefficient_rom.sv
RTL_SOURCES += ../../rtl/hilbert_delay_line.sv
RTL_SOURCES += ../../rtl/hilbert_multiplier_array.sv
RTL_SOURCES += ../../rtl/hilbert_adder_tree.sv

# Testbench files
TB_SOURCES = ../../tb/sv_tb/tb_hilbert_transformer.sv

# Constraint files
CONSTRAINTS = constraints/hilbert_transformer.xdc
CONSTRAINTS += constraints/timing.xdc

# Directories
BUILD_DIR = build
RESULTS_DIR = results
WAVES_DIR = waves
REPORTS_DIR = reports
CONSTRAINTS_DIR = constraints
IP_DIR = ip

# Vivado configuration
VIVADO_FLAGS = -mode batch
VIVADO_FLAGS += -source
VIVADO_FLAGS += -notrace

# Synthesis configuration
SYNTH_STRATEGY = Flow_Quick
SYNTH_RUN = synth_1

# Implementation configuration
IMPL_STRATEGY = Performance_Explore
IMPL_RUN = impl_1

# Simulation configuration
SIM_RUN = sim_1
SIM_TIME = 1000ns

#==============================================================================
# Environment Setup
#==============================================================================

# Create necessary directories
$(shell mkdir -p $(BUILD_DIR) $(RESULTS_DIR) $(WAVES_DIR) $(REPORTS_DIR) $(CONSTRAINTS_DIR) $(IP_DIR))

# Set environment variables
export VIVADO_PATH ?= /opt/Xilinx/Vivado/$(VIVADO_VERSION)
export PATH := $(VIVADO_PATH)/bin:$(PATH)

#==============================================================================
# Main Targets
#==============================================================================

.PHONY: all clean project synth impl bitstream sim sim-sv sim-cocotb timing power help

# Default target
all: bitstream

# Complete flow
flow: project synth impl bitstream

# Project creation
project: $(BUILD_DIR)/$(PROJECT_NAME).xpr

# Synthesis
synth: $(RESULTS_DIR)/synth_complete.rpt

# Implementation
impl: $(RESULTS_DIR)/impl_complete.rpt

# Bitstream generation
bitstream: $(RESULTS_DIR)/$(PROJECT_NAME).bit

# Simulation
sim: sim-sv sim-cocotb

#==============================================================================
# Project Creation
#==============================================================================

$(BUILD_DIR)/$(PROJECT_NAME).xpr: $(RTL_SOURCES) $(CONSTRAINTS)
	@echo "Creating Vivado project..."
	@mkdir -p $(BUILD_DIR)
	
	# Create project
	vivado $(VIVADO_FLAGS) scripts/create_project.tcl \
		-tclargs $(PROJECT_NAME) $(PART) $(BUILD_DIR)
	
	# Add source files
	vivado $(VIVADO_FLAGS) scripts/add_sources.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr "$(RTL_SOURCES)" "$(CONSTRAINTS)"
	
	@echo "Project created: $(BUILD_DIR)/$(PROJECT_NAME).xpr"

#==============================================================================
# Synthesis
#==============================================================================

$(RESULTS_DIR)/synth_complete.rpt: $(BUILD_DIR)/$(PROJECT_NAME).xpr
	@echo "Running synthesis..."
	@mkdir -p $(RESULTS_DIR)
	
	# Run synthesis
	vivado $(VIVADO_FLAGS) scripts/run_synthesis.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(SYNTH_RUN) $(SYNTH_STRATEGY) $(RESULTS_DIR)
	
	@echo "Synthesis completed: $(RESULTS_DIR)/synth_complete.rpt"

#==============================================================================
# Implementation
#==============================================================================

$(RESULTS_DIR)/impl_complete.rpt: $(RESULTS_DIR)/synth_complete.rpt
	@echo "Running implementation..."
	@mkdir -p $(RESULTS_DIR)
	
	# Run implementation
	vivado $(VIVADO_FLAGS) scripts/run_implementation.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(IMPL_RUN) $(IMPL_STRATEGY) $(RESULTS_DIR)
	
	@echo "Implementation completed: $(RESULTS_DIR)/impl_complete.rpt"

#==============================================================================
# Bitstream Generation
#==============================================================================

$(RESULTS_DIR)/$(PROJECT_NAME).bit: $(RESULTS_DIR)/impl_complete.rpt
	@echo "Generating bitstream..."
	@mkdir -p $(RESULTS_DIR)
	
	# Generate bitstream
	vivado $(VIVADO_FLAGS) scripts/generate_bitstream.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(IMPL_RUN) $(RESULTS_DIR)
	
	@echo "Bitstream generated: $(RESULTS_DIR)/$(PROJECT_NAME).bit"

#==============================================================================
# SystemVerilog Simulation
#==============================================================================

sim-sv: $(RESULTS_DIR)/sv_simulation_results.txt

$(RESULTS_DIR)/sv_simulation_results.txt: $(BUILD_DIR)/$(PROJECT_NAME).xpr $(TB_SOURCES)
	@echo "Running SystemVerilog simulation..."
	@mkdir -p $(RESULTS_DIR) $(WAVES_DIR)
	
	# Run simulation
	vivado $(VIVADO_FLAGS) scripts/run_simulation.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(SIM_RUN) $(SIM_TIME) $(RESULTS_DIR) $(WAVES_DIR)
	
	@echo "SystemVerilog simulation completed: $(RESULTS_DIR)/sv_simulation_results.txt"

#==============================================================================
# cocotb Simulation
#==============================================================================

sim-cocotb: $(RESULTS_DIR)/cocotb_simulation_results.txt

$(RESULTS_DIR)/cocotb_simulation_results.txt: ../../tb/cocotb/test_hilbert_transformer.py $(BUILD_DIR)/$(PROJECT_NAME).xpr
	@echo "Running cocotb simulation..."
	@mkdir -p $(RESULTS_DIR) $(WAVES_DIR)
	
	COCOTB_RESULTS_FILE=$@ \
	TOPLEVEL=$(TOPLEVEL) \
	TOPLEVEL_LANG=verilog \
	MODULE=test_hilbert_transformer \
	SIM=xsim \
	VERILOG_SOURCES="$(RTL_SOURCES)" \
	WAVES=1 \
	COVERAGE=1 \
	python -m pytest ../../tb/cocotb/test_hilbert_transformer.py -v \
		--tb=short \
		--junitxml=$(RESULTS_DIR)/cocotb_results.xml \
		> $@ 2>&1
	
	@echo "cocotb simulation completed: $(RESULTS_DIR)/cocotb_simulation_results.txt"

#==============================================================================
# Timing Analysis
#==============================================================================

timing: $(REPORTS_DIR)/timing_summary.rpt

$(REPORTS_DIR)/timing_summary.rpt: $(RESULTS_DIR)/impl_complete.rpt
	@echo "Running timing analysis..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate timing report
	vivado $(VIVADO_FLAGS) scripts/generate_timing_report.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(IMPL_RUN) $(REPORTS_DIR)
	
	@echo "Timing analysis completed: $(REPORTS_DIR)/timing_summary.rpt"

#==============================================================================
# Power Analysis
#==============================================================================

power: $(REPORTS_DIR)/power_summary.rpt

$(REPORTS_DIR)/power_summary.rpt: $(RESULTS_DIR)/impl_complete.rpt
	@echo "Running power analysis..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate power report
	vivado $(VIVADO_FLAGS) scripts/generate_power_report.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(IMPL_RUN) $(REPORTS_DIR)
	
	@echo "Power analysis completed: $(REPORTS_DIR)/power_summary.rpt"

#==============================================================================
# Resource Analysis
#==============================================================================

resources: $(REPORTS_DIR)/resource_summary.rpt

$(REPORTS_DIR)/resource_summary.rpt: $(RESULTS_DIR)/synth_complete.rpt
	@echo "Generating resource report..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate resource report
	vivado $(VIVADO_FLAGS) scripts/generate_resource_report.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(SYNTH_RUN) $(REPORTS_DIR)
	
	@echo "Resource analysis completed: $(REPORTS_DIR)/resource_summary.rpt"

#==============================================================================
# GUI
#==============================================================================

gui:
	@echo "Starting Vivado GUI..."
	vivado $(BUILD_DIR)/$(PROJECT_NAME).xpr &

gui-synth:
	@echo "Starting Vivado GUI with synthesis results..."
	vivado $(BUILD_DIR)/$(PROJECT_NAME).xpr -source scripts/open_synthesis.tcl &

gui-impl:
	@echo "Starting Vivado GUI with implementation results..."
	vivado $(BUILD_DIR)/$(PROJECT_NAME).xpr -source scripts/open_implementation.tcl &

#==============================================================================
# Programming
#==============================================================================

program: $(RESULTS_DIR)/$(PROJECT_NAME).bit
	@echo "Programming FPGA..."
	
	# Program FPGA
	vivado $(VIVADO_FLAGS) scripts/program_fpga.tcl \
		-tclargs $(RESULTS_DIR)/$(PROJECT_NAME).bit $(BOARD)
	
	@echo "FPGA programming completed"

#==============================================================================
# IP Core Generation
#==============================================================================

ip-core: $(IP_DIR)/$(PROJECT_NAME).xci

$(IP_DIR)/$(PROJECT_NAME).xci: $(RTL_SOURCES)
	@echo "Generating IP core..."
	@mkdir -p $(IP_DIR)
	
	# Generate IP core
	vivado $(VIVADO_FLAGS) scripts/generate_ip_core.tcl \
		-tclargs $(PROJECT_NAME) $(IP_DIR) "$(RTL_SOURCES)"
	
	@echo "IP core generated: $(IP_DIR)/$(PROJECT_NAME).xci"

#==============================================================================
# Documentation
#==============================================================================

docs: $(REPORTS_DIR)/design_documentation.txt

$(REPORTS_DIR)/design_documentation.txt: $(RESULTS_DIR)/synth_complete.rpt
	@echo "Generating design documentation..."
	@mkdir -p $(REPORTS_DIR)
	
	# Generate documentation
	vivado $(VIVADO_FLAGS) scripts/generate_documentation.tcl \
		-tclargs $(BUILD_DIR)/$(PROJECT_NAME).xpr $(REPORTS_DIR)
	
	@echo "Documentation generated: $(REPORTS_DIR)/design_documentation.txt"

#==============================================================================
# Cleanup
#==============================================================================

clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(BUILD_DIR)
	rm -rf $(RESULTS_DIR)
	rm -rf $(WAVES_DIR)
	rm -rf $(REPORTS_DIR)
	rm -rf $(IP_DIR)
	rm -rf *.jou
	rm -rf *.log
	rm -rf *.str
	rm -rf *.wdb
	rm -rf *.wcfg
	rm -rf *.xpr
	rm -rf *.xsa
	rm -rf *.bit
	rm -rf *.mcs
	rm -rf *.prm

distclean: clean
	@echo "Deep cleaning..."
	rm -rf .Xil
	rm -rf .cache
	rm -rf .ip_user_files
	rm -rf .sim
	rm -rf .srcs

#==============================================================================
# Help
#==============================================================================

help:
	@echo "Vivado Flow for Hilbert Transformer IP"
	@echo "======================================"
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Generate bitstream (default)"
	@echo "  flow         - Complete flow: project -> synth -> impl -> bitstream"
	@echo "  project      - Create Vivado project"
	@echo "  synth        - Run synthesis"
	@echo "  impl         - Run implementation"
	@echo "  bitstream    - Generate bitstream"
	@echo "  sim          - Run all simulations"
	@echo "  sim-sv       - Run SystemVerilog simulation"
	@echo "  sim-cocotb   - Run cocotb simulation"
	@echo "  timing       - Generate timing report"
	@echo "  power        - Generate power report"
	@echo "  resources    - Generate resource report"
	@echo "  gui          - Start Vivado GUI"
	@echo "  gui-synth    - Start GUI with synthesis results"
	@echo "  gui-impl     - Start GUI with implementation results"
	@echo "  program      - Program FPGA"
	@echo "  ip-core      - Generate IP core"
	@echo "  docs         - Generate documentation"
	@echo "  clean        - Clean build artifacts"
	@echo "  distclean    - Deep clean"
	@echo "  help         - Show this help"
	@echo ""
	@echo "Environment variables:"
	@echo "  VIVADO_PATH  - Path to Vivado installation"
	@echo "  PART         - FPGA part number"
	@echo "  BOARD        - Target board"
	@echo "  SYNTH_STRATEGY - Synthesis strategy"
	@echo "  IMPL_STRATEGY  - Implementation strategy"
	@echo ""
	@echo "Examples:"
	@echo "  make flow"
	@echo "  make synth"
	@echo "  make gui"
	@echo "  make program"

#==============================================================================
# Include cocotb Makefile
#==============================================================================

include $(shell cocotb-config --makefiles)/Makefile.sim 