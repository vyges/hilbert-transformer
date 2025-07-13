# Hilbert Transformer IP - Design Flows

This directory contains comprehensive design flows for the Hilbert Transformer IP, supporting both simulation and implementation workflows.

## Overview

The Hilbert Transformer IP provides two main design flows:

1. **Verilator Flow** - Fast simulation and verification
2. **Vivado Flow** - FPGA synthesis, implementation, and bitstream generation

Both flows are fully automated and include comprehensive testing, analysis, and reporting capabilities.

## Directory Structure

```
flow/
├── README.md                    # This file
├── verilator/                   # Verilator simulation flow
│   ├── Makefile                # Verilator build system
│   ├── build/                  # Build artifacts (auto-generated)
│   ├── results/                # Simulation results (auto-generated)
│   ├── waves/                  # Waveform files (auto-generated)
│   ├── coverage/               # Coverage reports (auto-generated)
│   └── reports/                # Analysis reports (auto-generated)
└── vivado/                     # Vivado FPGA flow
    ├── Makefile                # Vivado build system
    ├── scripts/                # TCL automation scripts
    │   ├── create_project.tcl  # Project creation
    │   ├── add_sources.tcl     # Source file management
    │   ├── run_synthesis.tcl   # Synthesis automation
    │   ├── run_implementation.tcl # Implementation automation
    │   ├── generate_bitstream.tcl # Bitstream generation
    │   ├── run_simulation.tcl  # Simulation automation
    │   └── generate_timing_report.tcl # Timing analysis
    ├── constraints/            # Design constraints
    │   ├── hilbert_transformer.xdc # Pin assignments and physical constraints
    │   └── timing.xdc         # Timing constraints
    ├── build/                  # Project files (auto-generated)
    ├── results/                # Implementation results (auto-generated)
    ├── waves/                  # Simulation waveforms (auto-generated)
    ├── reports/                # Analysis reports (auto-generated)
    └── ip/                     # IP core files (auto-generated)
```

## Prerequisites

### Verilator Flow
- Verilator 4.0 or later
- Python 3.7+ with cocotb
- GTKWave (optional, for waveform viewing)
- Make

### Vivado Flow
- Xilinx Vivado 2023.1 or later
- Python 3.7+ with cocotb (for simulation)
- Digilent Arty-A7-35 board (for physical testing)
- Make

## Quick Start

### Verilator Flow

```bash
# Navigate to Verilator flow directory
cd flow/verilator

# Run all simulations
make sim

# Run with coverage and waveforms
make sim-all

# Run specific simulation type
make sim-sv      # SystemVerilog only
make sim-cocotb  # cocotb only

# Generate coverage report
make coverage

# View waveforms
make gui

# Run complete regression
make regression

# Clean build artifacts
make clean
```

### Vivado Flow

```bash
# Navigate to Vivado flow directory
cd flow/vivado

# Complete flow: project -> synthesis -> implementation -> bitstream
make flow

# Individual steps
make project     # Create project
make synth       # Run synthesis
make impl        # Run implementation
make bitstream   # Generate bitstream

# Simulation
make sim         # Run all simulations
make sim-sv      # SystemVerilog simulation
make sim-cocotb  # cocotb simulation

# Analysis
make timing      # Generate timing reports
make power       # Generate power reports
make resources   # Generate resource reports

# GUI
make gui         # Open Vivado GUI
make gui-synth   # Open GUI with synthesis results
make gui-impl    # Open GUI with implementation results

# Programming
make program     # Program FPGA

# Clean build artifacts
make clean
```

## Configuration

### Verilator Configuration

Key configuration variables in `flow/verilator/Makefile`:

```makefile
# RTL source files
RTL_SOURCES = ../../rtl/hilbert_transformer.sv
RTL_SOURCES += ../../rtl/hilbert_coefficient_rom.sv
RTL_SOURCES += ../../rtl/hilbert_delay_line.sv
RTL_SOURCES += ../../rtl/hilbert_multiplier_array.sv
RTL_SOURCES += ../../rtl/hilbert_adder_tree.sv

# Testbench files
TB_SOURCES = ../../tb/sv_tb/tb_hilbert_transformer.sv

# Verilator flags
VERILATOR_FLAGS = --cc --exe --build
VERILATOR_FLAGS += --trace
VERILATOR_FLAGS += --coverage
```

### Vivado Configuration

Key configuration variables in `flow/vivado/Makefile`:

```makefile
# Project configuration
PROJECT_NAME = hilbert_transformer
TOPLEVEL = hilbert_transformer
PART = xc7a35ticsg324-1L
BOARD = arty-a7-35

# Synthesis and implementation strategies
SYNTH_STRATEGY = Flow_Quick
IMPL_STRATEGY = Performance_Explore
```

## Features

### Verilator Flow Features

- **Fast Simulation**: High-performance SystemVerilog simulation
- **Coverage Analysis**: Comprehensive functional and code coverage
- **Waveform Generation**: VCD waveform files for debugging
- **Multiple Testbenches**: Support for SystemVerilog and cocotb testbenches
- **Regression Testing**: Automated test suite execution
- **Performance Analysis**: Throughput and latency measurement
- **Linting**: Code quality and style checking
- **Documentation**: Automated documentation generation

### Vivado Flow Features

- **Complete FPGA Flow**: Synthesis, implementation, and bitstream generation
- **Timing Analysis**: Comprehensive timing reports and analysis
- **Resource Analysis**: Detailed resource utilization reports
- **Power Analysis**: Power consumption analysis and optimization
- **Simulation**: Integrated simulation with waveform generation
- **IP Core Generation**: Automated IP core packaging
- **Programming**: FPGA programming automation
- **GUI Integration**: Seamless GUI workflow integration

## Test Categories

Both flows support comprehensive testing:

### Functional Tests
- Basic functionality verification
- AXI-Stream protocol compliance
- Interface verification
- Configuration and status testing

### Performance Tests
- Maximum frequency measurement
- Throughput analysis
- Latency measurement
- Resource utilization

### Corner Case Tests
- FIFO overflow/underflow
- Reset behavior
- Timeout conditions
- Edge case handling

### Error Tests
- Protocol violations
- Error injection
- Fault tolerance
- Error recovery

### Coverage Tests
- Functional coverage
- Code coverage
- Toggle coverage
- FSM coverage

## Reports and Analysis

### Verilator Reports
- `coverage_report.html`: Coverage analysis
- `performance_metrics.txt`: Performance analysis
- `regression_report.txt`: Test results summary
- `lint_report.txt`: Code quality analysis

### Vivado Reports
- `timing_summary.rpt`: Timing analysis
- `utilization_impl.rpt`: Resource utilization
- `power_impl.rpt`: Power analysis
- `drc_impl.rpt`: Design rule checks
- `route_status.rpt`: Routing analysis

## Target Platforms

### Verilator Flow
- **Simulation**: Any platform supporting Verilator
- **Coverage**: Cross-platform coverage analysis
- **Waveforms**: GTKWave compatible

### Vivado Flow
- **FPGA**: Digilent Arty-A7-35 (xc7a35ticsg324-1L)
- **Target Frequency**: 200 MHz
- **Interface**: AXI-Stream with handshake protocol
- **Configuration**: 32-bit configuration interface

## Performance Targets

### Verilator Performance
- **Simulation Speed**: >1000 samples/second
- **Coverage**: >95% line coverage
- **Memory Usage**: <2GB for typical test cases

### Vivado Performance
- **Target Frequency**: 200 MHz
- **Resource Utilization**: <80% of available resources
- **Power Consumption**: <2W typical
- **Latency**: <64 clock cycles

## Troubleshooting

### Common Issues

#### Verilator Flow
1. **Verilator not found**: Set `VERILATOR_ROOT` environment variable
2. **Python import errors**: Install required Python packages
3. **Memory issues**: Reduce simulation time or increase system memory

#### Vivado Flow
1. **Vivado not found**: Set `VIVADO_PATH` environment variable
2. **Timing violations**: Review timing constraints and optimization settings
3. **Resource constraints**: Optimize RTL or use larger FPGA

### Debug Commands

```bash
# Verilator debugging
make sim-sv WAVES=1
make gui

# Vivado debugging
make gui-synth
make gui-impl
make timing
```

## Integration

### SoC Integration
Both flows support easy integration into larger systems:

- **AXI-Stream Interface**: Standard streaming protocol
- **Single Clock Domain**: Simplified timing analysis
- **Synchronous Reset**: Standard reset strategy
- **Configuration Interface**: Runtime parameter configuration

### CI/CD Integration
The flows are designed for automated CI/CD pipelines:

- **Batch Mode**: Non-interactive execution
- **Exit Codes**: Proper error reporting
- **Artifact Generation**: Structured output files
- **Regression Testing**: Automated test execution

## Support

For issues and questions:

1. Check the troubleshooting section above
2. Review the generated reports for detailed analysis
3. Consult the main project documentation
4. Contact the Vyges team for support

## License

This work is licensed under the Apache License, Version 2.0. See the LICENSE file for details. 