# Architecture: Hilbert Transformer IP

## Overview

This document describes the internal architecture, AXI-Stream interface, and design details of the `vyges/hilbert-transformer` fully pipelined digital Hilbert transformer. The module is parameterizable and supports configurable data widths, filter orders, and pipeline stages for optimal FPGA and ASIC implementations.

---

## Block Diagram

```
                    ┌─────────────────────────────────────┐
                    │         HILBERT_TRANSFORMER         │
                    │                                     │
    ┌───────────────┤  Clock/Reset Interface              │
    │ clk_i         │  ┌─────────┐    ┌─────────┐        │
    │ rst_n_i       │  │ Clock   │    │ Reset   │        │
    └───────────────┤  │ clk_i   │    │ rst_n_i │        │
                    │  └─────────┘    └─────────┘        │
    ┌───────────────┤                                     │
    │ AXI-Stream    │  ┌─────────────────────────┐        │
    │ Input         │  │    Input Interface      │        │
    │ tdata_i[W-1:0]│  │ tdata_i[W-1:0]         │        │
    │ tvalid_i      │  │ tvalid_i                │        │
    │ tready_o      │  │ tready_o                │        │
    └───────────────┤  └─────────────────────────┘        │
                    │                                     │
    ┌───────────────┤  ┌─────────────────────────┐        │
    │ AXI-Stream    │  │   Output Interface      │        │
    │ Output        │  │ tdata_o[W-1:0]         │        │
    │ tdata_o[W-1:0]│  │ tvalid_o                │        │
    │ tvalid_o      │  │ tready_i                │        │
    │ tready_i      │  └─────────────────────────┘        │
    └───────────────┤                                     │
                    │  ┌─────────────────────────┐        │
                    │  │   Control Interface     │        │
                    │  │ config_valid_i          │        │
                    │  │ config_data_i[31:0]     │        │
                    │  │ status_o[31:0]          │        │
                    │  └─────────────────────────┘        │
                    └─────────────────────────────────────┘
```

## Internal Architecture

```
                    ┌─────────────────────────────────────┐
                    │         HILBERT_TRANSFORMER         │
                    │                                     │
    ┌───────────────┤  ┌─────────────────────────┐        │
    │ Input         │  │    Input Buffer &       │        │
    │ Interface     │  │    Handshake Logic      │        │
    └───────────────┤  └─────────────────────────┘        │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────┐        │
                    │  │    Delay Line Buffer    │        │
                    │  │   (FILTER_ORDER taps)   │        │
                    │  └─────────────────────────┘        │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────┐        │
                    │  │   Coefficient ROM       │        │
                    │  │   (Pre-computed FIR     │        │
                    │  │    coefficients)        │        │
                    │  └─────────────────────────┘        │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────┐        │
                    │  │   Multiplier Array      │        │
                    │  │   (FILTER_ORDER/2       │        │
                    │  │    multipliers)         │        │
                    │  └─────────────────────────┘        │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────┐        │
                    │  │     Adder Tree          │        │
                    │  │   (Pipelined addition)  │        │
                    │  └─────────────────────────┘        │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────┐        │
                    │  │   Output Buffer &       │        │
                    │  │    Handshake Logic      │        │
                    │  └─────────────────────────┘        │
                    │              │                      │
    ┌───────────────┤              ▼                      │
    │ Output        │  ┌─────────────────────────┐        │
    │ Interface     │  │   Output Interface      │        │
    └───────────────┤  └─────────────────────────┘        │
                    │                                     │
                    │  ┌─────────────────────────┐        │
                    │  │   Configuration &       │        │
                    │  │    Status Logic         │        │
                    │  └─────────────────────────┘        │
                    └─────────────────────────────────────┘
```

## Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `DATA_WIDTH` | int | 16 | 8-32 | Bit-width of input/output data |
| `FILTER_ORDER` | int | 64 | 16-256 | Number of FIR filter taps |
| `PIPELINE_STAGES` | int | 8 | 4-16 | Number of pipeline stages |
| `COEFF_WIDTH` | int | 18 | 16-24 | Bit-width of filter coefficients |
| `ACCUM_WIDTH` | int | 32 | - | Accumulator bit-width |

### Derived Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `ADDR_WIDTH` | int | `$clog2(FILTER_ORDER)` - Address width for coefficient ROM |
| `MULT_WIDTH` | int | `DATA_WIDTH + COEFF_WIDTH` - Multiplier output width |
| `LATENCY` | int | `PIPELINE_STAGES + FILTER_ORDER/2` - Total pipeline latency |

## Interface Specifications

### Clock and Reset Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk_i` | input | 1 | System clock input |
| `rst_n_i` | input | 1 | Active-low reset input |

### AXI-Stream Input Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `tdata_i` | input | DATA_WIDTH | Input data stream |
| `tvalid_i` | input | 1 | Input data valid signal |
| `tready_o` | output | 1 | Ready to accept input signal |

### AXI-Stream Output Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `tdata_o` | output | DATA_WIDTH | Output data stream (Hilbert transformed) |
| `tvalid_o` | output | 1 | Output data valid signal |
| `tready_i` | input | 1 | Downstream ready signal |

### Control Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `config_valid_i` | input | 1 | Configuration data valid signal |
| `config_data_i` | input | 32 | Configuration data register |
| `status_o` | output | 32 | Status information register |

## Internal Modules

### 1. Input Buffer & Handshake Logic
- **Purpose**: Manages AXI-Stream input protocol and data buffering
- **Features**: 
  - Handshake protocol implementation (tvalid_i, tready_o)
  - Input data buffering for pipeline feeding
  - Backpressure handling and flow control
- **Implementation**: FIFO-based buffer with configurable depth

### 2. Delay Line Buffer
- **Purpose**: Stores historical samples for FIR filter processing
- **Features**:
  - FILTER_ORDER deep shift register
  - Configurable tap access for symmetric FIR structure
  - Efficient memory usage through anti-symmetric coefficient properties
- **Implementation**: Dual-port RAM or shift register array

### 3. Coefficient ROM
- **Purpose**: Stores pre-computed FIR filter coefficients
- **Features**:
  - Pre-computed Hilbert transform coefficients
  - Anti-symmetric coefficient storage optimization
  - Configurable coefficient precision (COEFF_WIDTH)
- **Implementation**: ROM with configurable coefficient sets

### 4. Multiplier Array
- **Purpose**: Performs coefficient multiplication for FIR filtering
- **Features**:
  - FILTER_ORDER/2 parallel multipliers (anti-symmetric optimization)
  - Configurable precision multiplication
  - DSP block optimization for FPGA implementations
- **Implementation**: Array of signed multipliers with proper rounding

### 5. Adder Tree
- **Purpose**: Accumulates multiplier outputs to produce filter result
- **Features**:
  - Pipelined addition tree for high-frequency operation
  - Configurable pipeline stages for timing optimization
  - Overflow protection and saturation handling
- **Implementation**: Balanced binary tree with pipeline registers

### 6. Output Buffer & Handshake Logic
- **Purpose**: Manages AXI-Stream output protocol and data formatting
- **Features**:
  - Handshake protocol implementation (tvalid_o, tready_i)
  - Output data formatting and alignment
  - Flow control and backpressure handling
- **Implementation**: FIFO-based buffer with configurable depth

### 7. Configuration & Status Logic
- **Purpose**: Manages configuration registers and status reporting
- **Features**:
  - Configuration register access and validation
  - Status monitoring and error reporting
  - Sample counting and performance metrics
- **Implementation**: Register-based control logic with status counters

## Pipeline Architecture

### Stage Breakdown

| Stage | Function | Latency | Description |
|-------|----------|---------|-------------|
| 1 | Input Buffering | 1 cycle | Input data validation and buffering |
| 2 | Delay Line | 1 cycle | Historical sample management |
| 3-6 | Multiplier Array | 4 cycles | Coefficient multiplication |
| 7 | Adder Tree | 1 cycle | Accumulation and addition |
| 8 | Output Formatting | 1 cycle | Output data formatting and handshake |

### Pipeline Flow
```
Input → Stage 1 → Stage 2 → Stages 3-6 → Stage 7 → Stage 8 → Output
   ↓       ↓        ↓         ↓         ↓        ↓        ↓
  Data   Buffer   Delay    Multiply   Add     Format   Output
```

## FIR Filter Design

### Coefficient Generation
- **Method**: Pre-computed using MATLAB/Octave or similar tools
- **Algorithm**: Parks-McClellan optimal FIR filter design
- **Characteristics**: Anti-symmetric coefficients for Hilbert transform
- **Optimization**: Minimized passband ripple and stopband attenuation

### Symmetry Exploitation
- **Anti-symmetric Property**: h[n] = -h[N-1-n] for Hilbert transform
- **Memory Reduction**: Store only half the coefficients
- **Computation Reduction**: FILTER_ORDER/2 multipliers instead of FILTER_ORDER
- **Implementation**: Coefficient ROM with address mapping for symmetry

### Multiplier Optimization
- **DSP Block Usage**: Efficient utilization of FPGA DSP blocks
- **Precision Management**: Configurable coefficient and data precision
- **Rounding**: Proper rounding for coefficient quantization effects
- **Saturation**: Overflow protection for extreme input values

## Memory Architecture

### Coefficient Storage
- **Type**: ROM-based coefficient storage
- **Size**: FILTER_ORDER/2 × COEFF_WIDTH bits
- **Access**: Single-cycle read access for all coefficients
- **Optimization**: Anti-symmetric coefficient storage

### Delay Line Storage
- **Type**: Dual-port RAM or shift register array
- **Size**: FILTER_ORDER × DATA_WIDTH bits
- **Access**: Read/write access for sample history
- **Optimization**: Efficient tap access for symmetric FIR structure

### Buffer Storage
- **Input Buffer**: FIFO for input data buffering
- **Output Buffer**: FIFO for output data buffering
- **Size**: Configurable depth based on pipeline requirements
- **Access**: First-in-first-out access pattern

## Timing and Performance

### Critical Paths
1. **Multiplier Path**: Input data → Multiplier → Pipeline register
2. **Adder Tree Path**: Multiplier output → Adder tree → Pipeline register
3. **Buffer Path**: Input buffer → Delay line → Output buffer

### Performance Characteristics
- **Maximum Frequency**: 200 MHz (FPGA), 500 MHz (ASIC)
- **Throughput**: 1 sample per clock cycle (fully pipelined)
- **Latency**: Configurable from 8 to 64 clock cycles
- **Setup Time**: 2.5 ns (FPGA), 1.0 ns (ASIC)
- **Hold Time**: 0.5 ns (FPGA), 0.2 ns (ASIC)

### Resource Utilization

#### FPGA Resources (Arty-A7-35)
- **LUTs**: ~2000-8000 (depending on DATA_WIDTH)
- **DSP Blocks**: 16-64 (depending on FILTER_ORDER)
- **BRAM**: 1-4 blocks (coefficient and buffer storage)
- **FFs**: ~1000-4000 (pipeline registers and control logic)

#### ASIC Resources (28nm process)
- **Area**: 0.1-0.5 mm² (depending on configuration)
- **Power**: 1-10 mW (typical operation)
- **Gate Count**: 50K-200K gates (depending on configuration)

## Error Handling and Monitoring

### Overflow Detection
- **Multiplier Overflow**: Monitors multiplication result overflow
- **Accumulator Overflow**: Monitors adder tree accumulation overflow
- **Buffer Overflow**: Monitors input/output buffer overflow conditions

### Error Reporting
- **Status Register**: Error flags in status_o register
- **Error Types**: Overflow, invalid configuration, protocol violations
- **Error Handling**: Graceful degradation and error recovery

### Performance Monitoring
- **Sample Counter**: Tracks processed sample count
- **Error Counter**: Tracks error occurrences
- **Performance Metrics**: Throughput and latency monitoring

## Configuration and Control

### Configuration Register (32-bit)
```
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ 31:24       │ 23:16       │ 15:8        │ 7:0         │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Reserved    │ Pipeline    │ Data Width  │ Filter      │
│             │ Mode        │ Config      │ Order       │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

### Status Register (32-bit)
```
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ 31:16       │ 15:8        │ 7:0         │             │
├─────────────┼─────────────┼─────────────┤             │
│ Sample      │ Error       │ Status      │             │
│ Count       │ Flags       │ Flags       │             │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

## Design Considerations

### Clock Domain
- **Single Clock Domain**: All logic operates on clk_i
- **No Clock Crossing**: Eliminates clock domain crossing complexity
- **Synchronous Reset**: All flip-flops use rst_n_i for initialization

### Power Management
- **Clock Gating**: Optional clock gating for power optimization
- **Power Domains**: Single power domain design
- **Dynamic Scaling**: Configurable pipeline stages for power/performance trade-off

### Testability
- **Scan Chain**: Support for scan chain insertion
- **BIST**: Built-in self-test capabilities
- **Debug Interface**: Optional debug interface for testing and validation

## Integration Guidelines

### SoC Integration
- **AXI-Stream Compatibility**: Standard streaming interface
- **Clock Integration**: Single clock domain for easy integration
- **Reset Integration**: Synchronous reset with proper initialization
- **Power Integration**: Standard power domain integration

### FPGA Integration
- **IP Core Compatibility**: Xilinx IP Integrator compatible
- **Resource Optimization**: Efficient FPGA resource utilization
- **Timing Closure**: Provided constraints for timing closure
- **Example Design**: Complete reference implementation

### ASIC Integration
- **Standard Cell Compatibility**: Compatible with standard cell libraries
- **Timing Constraints**: SDC files provided for synthesis
- **Physical Design**: Place and route ready design
- **Power Analysis**: Power consumption analysis and optimization

## Notes

- **Reset Behavior**: All registers and buffers are cleared on rst_n_i assertion
- **Configuration**: Configuration changes require proper timing and validation
- **Performance**: Maximum performance achieved with optimal pipeline configuration
- **Resource Usage**: Resource utilization scales with DATA_WIDTH and FILTER_ORDER parameters
- **Compatibility**: AXI-Stream protocol compliance ensures broad compatibility

---

*This architecture document provides the foundation for implementation, verification, and integration of the Hilbert Transformer IP block within the Vyges ecosystem.*
