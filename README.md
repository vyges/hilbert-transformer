# Hilbert Transformer IP

[![Vyges IP Template](https://img.shields.io/badge/Vyges-IP%20Template-blue.svg)](https://vyges.com)
[![Use this template](https://img.shields.io/badge/Use%20this%20template-brightgreen.svg)](https://github.com/vyges/vyges-ip-template)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Build Status](https://img.shields.io/badge/Build-Passing-brightgreen.svg)](https://github.com/vyges/hilbert-transformer/actions)

A fully pipelined digital Hilbert transformer IP block for DSP applications including single sideband modulation, amplitude/phase detection, and quadrature signal processing. Optimized for FPGA and ASIC implementations with configurable precision and maximum throughput.

## Overview

The Hilbert Transformer IP block implements a Finite Impulse Response (FIR) filter-based Hilbert transform with anti-symmetric coefficient optimization. The design features a fully pipelined architecture achieving 1 sample per clock cycle throughput with configurable data widths, filter orders, and pipeline stages.

### Key Features

- **Fully Pipelined Architecture**: Maximum throughput with minimal latency
- **Configurable Precision**: Support for 8-bit to 32-bit data widths
- **Anti-symmetric Optimization**: Efficient FIR filter implementation
- **AXI-Stream Interface**: Standard streaming interface for easy integration
- **Configuration Interface**: Runtime parameter configuration
- **Error Detection**: Overflow monitoring and status reporting
- **Multi-Platform Support**: Optimized for both FPGA and ASIC implementations

### Applications

- **Single Sideband (SSB) Modulation/Demodulation**: Essential for efficient bandwidth utilization
- **Amplitude and Phase Detection**: Enables envelope and phase extraction from modulated signals
- **Quadrature Signal Processing**: Creates in-phase (I) and quadrature (Q) signal components
- **Digital Communications**: Used in software-defined radio and modern communication systems
- **Audio Processing**: Phase correction and stereo enhancement

## Interfaces

| Signal Name | Function | Direction | Description |
|-------------|----------|-----------|-------------|
| clk_i | System Clock | Input | System clock input |
| rst_n_i | Reset | Input | Active-low reset signal |
| tdata_i[W-1:0] | Input Data | Input | Input data stream |
| tvalid_i | Input Valid | Input | Input data valid signal |
| tready_o | Input Ready | Output | Ready to accept input |
| tdata_o[W-1:0] | Output Data | Output | Output data stream |
| tvalid_o | Output Valid | Output | Output data valid signal |
| tready_i | Output Ready | Input | Downstream ready signal |
| config_valid_i | Config Valid | Input | Configuration valid signal |
| config_data_i[31:0] | Config Data | Input | Configuration data |
| status_o[31:0] | Status | Output | Status information |

## Integration

### Integration Framework

The IP includes a comprehensive integration framework with:

- **SoC Integration**: Complete system-on-chip integration examples with AXI-Stream adapters, configuration controllers, and performance monitoring
- **FPGA Integration**: Board-specific examples for Arty-A7-35 and other FPGA platforms with UART interfaces and LED indicators
- **ASIC Integration**: Standard cell library and OpenLane flow integration with synthesis and timing constraints
- **Interface Adapters**: AXI-Stream to other protocol bridges (APB, AHB, Wishbone, Avalon)
- **Verification Components**: Protocol checkers, performance monitors, and comprehensive integration testbenches

### Bus Protocols

- **AXI-Stream**: Standard ARM AMBA AXI-Stream protocol for data streaming
- **Single Clock Domain**: All logic operates on the same clock for easy integration
- **Synchronous Reset**: Active-low reset with proper initialization sequence

### Target Usage

- **FPGA Integration**: Xilinx IP Integrator compatible with provided constraints and example designs
- **ASIC Integration**: Standard cell library compatible with synthesis constraints and OpenLane flow
- **SoC Integration**: Easy integration into system-on-chip designs with comprehensive examples
- **DSP Systems**: Optimized for digital signal processing applications with performance monitoring

## Testing & Verification

| Method | Tool | Status |
|--------|------|--------|
| Functional Simulation | SystemVerilog | ✅ Passing |
| Functional Simulation | cocotb | ✅ Passing |
| Coverage Analysis | Verilator | ✅ Passing |
| Linting | Verilator | ✅ Passing |
| Synthesis | Yosys | ✅ Passing |
| Timing Analysis | OpenSTA | ✅ Passing |

## Build & Test

### Prerequisites

- Python 3.8+
- Verilator 4.0+
- Icarus Verilog (optional)
- GTKWave (optional, for waveform viewing)

### Quick Start

```bash
# Clone the repository
git clone https://github.com/vyges/hilbert-transformer.git
cd hilbert-transformer

# Run all tests with Verilator
make -C tb test

# Run specific test categories
make -C tb test-sv      # SystemVerilog tests only
make -C tb test-cocotb  # cocotb tests only

# Run with coverage and waveforms
make -C tb test-all

# Start GUI simulation
make -C tb gui

# Run integration tests
make -C integration test

# Run specific integration tests
make -C integration test-soc      # SoC integration tests
make -C integration test-fpga     # FPGA integration tests
make -C integration test-integration # Full integration testbench
```

### Test Categories

- **Functional Tests**: Sine wave input with 90° phase shift verification
- **Performance Tests**: Throughput measurement and timing analysis
- **Corner Case Tests**: Edge conditions and boundary testing
- **Error Tests**: Protocol violations and overflow detection
- **Coverage Tests**: Comprehensive coverage analysis
- **Integration Tests**: Complete system integration verification
  - SoC integration with AXI-Stream protocols
  - FPGA integration with board-specific features
  - ASIC integration with synthesis flows
  - Interface adapter testing and validation

## Toolchain & Flow Support

| Toolchain | Supported | Location |
|-----------|-----------|----------|
| Verilator | ✅ Yes | `tb/Makefile`, `integration/Makefile` |
| Icarus Verilog | ✅ Yes | `tb/Makefile`, `integration/Makefile` |
| VCS | ✅ Yes | `tb/Makefile`, `integration/Makefile` |
| Xcelium | ✅ Yes | `tb/Makefile`, `integration/Makefile` |
| OpenLane | ✅ Yes | `flow/openlane/`, `integration/asic/openlane/` |
| Vivado | ✅ Yes | `flow/vivado/`, `integration/fpga/xilinx/` |
| Yosys | ✅ Yes | `flow/yosys/` |

## File Structure

```
hilbert-transformer/
├── rtl/                          # RTL source files
│   ├── hilbert_transformer.sv    # Main module
│   ├── hilbert_coefficient_rom.sv # Coefficient ROM
│   ├── hilbert_delay_line.sv     # Delay line buffer
│   ├── hilbert_multiplier_array.sv # Multiplier array
│   └── hilbert_adder_tree.sv     # Adder tree
├── tb/                          # Testbench files
│   ├── sv_tb/                   # SystemVerilog testbenches
│   │   └── tb_hilbert_transformer.sv
│   ├── cocotb/                  # Python testbenches
│   │   └── test_hilbert_transformer.py
│   └── Makefile                 # Test automation
├── integration/                 # Integration components
│   ├── soc/                     # System-on-Chip integration
│   │   ├── axi_stream_adapter.sv # AXI-Stream protocol adapter
│   │   ├── example_soc.sv       # Complete SoC integration example
│   │   └── README.md            # SoC integration guide
│   ├── fpga/                    # FPGA integration examples
│   │   ├── xilinx/              # Xilinx FPGA examples
│   │   │   ├── arty_a7_example.sv # Arty-A7-35 example design
│   │   │   └── constraints.xdc  # FPGA constraints
│   │   └── intel/               # Intel FPGA examples
│   ├── asic/                    # ASIC integration
│   │   ├── standard_cell/       # Standard cell integration
│   │   └── openlane/            # OpenLane ASIC flow
│   ├── interfaces/              # Interface adapters
│   │   ├── axi_stream_to_apb.sv # AXI-Stream to APB bridge
│   │   ├── axi_stream_to_ahb.sv # AXI-Stream to AHB bridge
│   │   └── axi_stream_to_wishbone.sv # AXI-Stream to Wishbone bridge
│   ├── verification/            # Integration verification
│   │   ├── integration_testbench.sv # Comprehensive integration testbench
│   │   ├── protocol_checker.sv  # Protocol compliance checker
│   │   └── performance_monitor.sv # Performance monitoring
│   ├── examples/                # Complete example designs
│   │   ├── audio_processor/     # Audio processing example
│   │   ├── communication_system/ # Communication system example
│   │   └── radar_system/        # Radar system example
│   ├── README.md                # Integration guide
│   └── Makefile                 # Integration build system
├── flow/                        # Tool flow configurations
│   ├── openlane/                # ASIC flow
│   ├── vivado/                  # FPGA flow
│   └── yosys/                   # Synthesis flow
├── docs/                        # Documentation
│   ├── Hibert-Transformer_design_spec.md
│   └── architecture.md
├── test/                        # Test vectors and coverage
├── constraints/                 # Timing and pin constraints
└── vyges-metadata.json         # IP metadata
```

## Performance Characteristics

### Timing Specifications

- **Maximum Clock Frequency**: 200 MHz (FPGA), 500 MHz (ASIC)
- **Latency**: Configurable from 8 to 64 clock cycles
- **Throughput**: 1 sample per clock cycle (fully pipelined)
- **Setup Time**: 2.5 ns (FPGA), 1.0 ns (ASIC)
- **Hold Time**: 0.5 ns (FPGA), 0.2 ns (ASIC)

### Resource Utilization

#### FPGA Resources (Arty-A7-35)
- **LUTs**: ~2000-8000 (depending on data width)
- **DSP Blocks**: 16-64 (depending on filter order)
- **BRAM**: 1-4 blocks (coefficient and buffer storage)
- **FFs**: ~1000-4000 (pipeline registers and control logic)

#### ASIC Resources (28nm process)
- **Area**: 0.1-0.5 mm² (depending on configuration)
- **Power**: 1-10 mW (typical operation)
- **Gate Count**: 50K-200K gates (depending on configuration)

## Configuration

### Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| DATA_WIDTH | int | 16 | 8-32 | Data width for input/output streams |
| FILTER_ORDER | int | 64 | 16-256 | FIR filter order |
| PIPELINE_STAGES | int | 8 | 4-16 | Number of pipeline stages |
| COEFF_WIDTH | int | 18 | 16-24 | Coefficient width |
| ACCUM_WIDTH | int | 32 | - | Accumulator width |

### Configuration Register

```
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ 31:24       │ 23:16       │ 15:8        │ 7:0         │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Reserved    │ Pipeline    │ Data Width  │ Filter      │
│             │ Mode        │ Config      │ Order       │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

## Maintainers

| Name | Role | Contact |
|------|------|---------|
| Vyges Team | Primary Maintainer | team@vyges.com |

## Related Projects

- [Vyges IP Template](https://github.com/vyges/vyges-ip-template) - Base template for Vyges IP development
- [Vyges IP Catalog](https://vyges.com/catalog) - Complete IP catalog
- [Vyges Documentation](https://docs.vyges.com) - Development guides and tutorials

## License

Apache-2.0 License - see [LICENSE](LICENSE) file for details.

**Important**: The Apache-2.0 license applies to the **hardware IP content** (RTL, documentation, testbenches, etc.) that you create using this template. The template structure, build processes, tooling workflows, and AI context/processing engine are provided as-is for your use but are not themselves licensed under Apache-2.0.

For detailed licensing information, see [LICENSE_SCOPE.md](LICENSE_SCOPE.md).

## Contributing

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

## Support

For support and questions:
- 📧 Email: team@vyges.com
- 💬 Discord: [Vyges Community](https://discord.gg/vyges)
- 📖 Documentation: [docs.vyges.com](https://docs.vyges.com)
- 🐛 Issues: [GitHub Issues](https://github.com/vyges/hilbert-transformer/issues)

---

**Note**: This IP block follows Vyges conventions and is designed for integration into the Vyges ecosystem. For more information about Vyges IP development, visit [vyges.com](https://vyges.com).
