# Hilbert Transformer IP - Integration Guide

This directory contains comprehensive integration examples and components for the Hilbert Transformer IP, supporting various platforms and use cases.

## Overview

The Hilbert Transformer IP is designed for easy integration into FPGA and ASIC designs. This guide provides:

- **SoC Integration Examples**: Complete system-on-chip integration
- **FPGA Integration**: Xilinx and Intel FPGA examples
- **ASIC Integration**: Standard cell library integration
- **Interface Adapters**: AXI-Stream to other protocol converters
- **Test Integration**: Integration testbenches and verification
- **Documentation**: Integration guides and reference designs

## Directory Structure

```
integration/
├── README.md                    # This file
├── soc/                         # System-on-Chip integration
│   ├── axi_stream_adapter.sv    # AXI-Stream protocol adapter
│   ├── clock_domain_crossing.sv # Clock domain crossing logic
│   ├── reset_synchronizer.sv    # Reset synchronization
│   ├── integration_tb.sv        # SoC integration testbench
│   └── example_soc.sv           # Example SoC integration
├── fpga/                        # FPGA-specific integration
│   ├── xilinx/                  # Xilinx FPGA examples
│   │   ├── arty_a7_example.sv   # Arty-A7-35 example design
│   │   ├── constraints.xdc      # FPGA constraints
│   │   └── ip_core.tcl          # IP core generation script
│   └── intel/                   # Intel FPGA examples
│       ├── de10_nano_example.sv # DE10-Nano example design
│       ├── constraints.sdc      # Intel constraints
│       └── ip_core.tcl          # IP core generation script
├── asic/                        # ASIC integration
│   ├── standard_cell/           # Standard cell integration
│   │   ├── synthesis_script.tcl # Synthesis script
│   │   ├── timing_constraints.sdc # Timing constraints
│   │   └── power_constraints.sdc # Power constraints
│   └── openlane/                # OpenLane ASIC flow
│       ├── config.tcl           # OpenLane configuration
│       ├── floorplan.tcl        # Floorplan script
│       └── integration.tcl      # Integration script
├── interfaces/                  # Interface adapters
│   ├── axi_stream_to_apb.sv     # AXI-Stream to APB bridge
│   ├── axi_stream_to_ahb.sv     # AXI-Stream to AHB bridge
│   ├── axi_stream_to_wishbone.sv # AXI-Stream to Wishbone bridge
│   └── axi_stream_to_avalon.sv  # AXI-Stream to Avalon bridge
├── verification/                # Integration verification
│   ├── integration_testbench.sv # Main integration testbench
│   ├── protocol_checker.sv      # Protocol compliance checker
│   ├── performance_monitor.sv   # Performance monitoring
│   └── coverage_collector.sv    # Coverage collection
└── examples/                    # Complete example designs
    ├── audio_processor/         # Audio processing example
    ├── communication_system/    # Communication system example
    └── radar_system/           # Radar system example
```

## Quick Start

### 1. Basic Integration

```systemverilog
// Basic Hilbert Transformer integration
module basic_integration (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [15:0] input_data_i,
    input  logic        input_valid_i,
    output logic        input_ready_o,
    output logic [15:0] output_data_o,
    output logic        output_valid_o,
    input  logic        output_ready_i
);

    // Instantiate Hilbert Transformer
    hilbert_transformer #(
        .DATA_WIDTH(16),
        .FILTER_ORDER(64),
        .PIPELINE_STAGES(8)
    ) hilbert_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .tdata_i(input_data_i),
        .tvalid_i(input_valid_i),
        .tready_o(input_ready_o),
        .tdata_o(output_data_o),
        .tvalid_o(output_valid_o),
        .tready_i(output_ready_i),
        .config_valid_i(1'b0),
        .config_data_i(32'h0),
        .status_o()
    );

endmodule
```

### 2. SoC Integration

```systemverilog
// SoC integration with AXI-Stream interface
module soc_integration (
    input  logic        clk_i,
    input  logic        rst_n_i,
    
    // AXI-Stream input interface
    input  logic [15:0] s_axis_tdata,
    input  logic        s_axis_tvalid,
    output logic        s_axis_tready,
    input  logic        s_axis_tlast,
    
    // AXI-Stream output interface
    output logic [15:0] m_axis_tdata,
    output logic        m_axis_tvalid,
    input  logic        m_axis_tready,
    output logic        m_axis_tlast,
    
    // Configuration interface
    input  logic [31:0] config_data_i,
    input  logic        config_valid_i,
    output logic [31:0] status_o
);

    // AXI-Stream adapter for input
    axi_stream_adapter #(
        .DATA_WIDTH(16)
    ) input_adapter (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .m_axis_tdata(hilbert_tdata_i),
        .m_axis_tvalid(hilbert_tvalid_i),
        .m_axis_tready(hilbert_tready_o),
        .m_axis_tlast()
    );

    // Hilbert Transformer core
    hilbert_transformer #(
        .DATA_WIDTH(16),
        .FILTER_ORDER(64),
        .PIPELINE_STAGES(8)
    ) hilbert_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .tdata_i(hilbert_tdata_i),
        .tvalid_i(hilbert_tvalid_i),
        .tready_o(hilbert_tready_o),
        .tdata_o(hilbert_tdata_o),
        .tvalid_o(hilbert_tvalid_o),
        .tready_i(hilbert_tready_i),
        .config_valid_i(config_valid_i),
        .config_data_i(config_data_i),
        .status_o(status_o)
    );

    // AXI-Stream adapter for output
    axi_stream_adapter #(
        .DATA_WIDTH(16)
    ) output_adapter (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(hilbert_tdata_o),
        .s_axis_tvalid(hilbert_tvalid_o),
        .s_axis_tready(hilbert_tready_i),
        .s_axis_tlast(1'b0),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast)
    );

endmodule
```

## Integration Examples

### FPGA Integration (Xilinx)

```tcl
# Xilinx IP Core Generation
create_ip -name hilbert_transformer -vendor vyges -library ip -version 1.0 -module_name hilbert_transformer_0

set_property -dict [list \
    CONFIG.DATA_WIDTH {16} \
    CONFIG.FILTER_ORDER {64} \
    CONFIG.PIPELINE_STAGES {8} \
] [get_ips hilbert_transformer_0]

generate_target all [get_ips]
```

### ASIC Integration (OpenLane)

```tcl
# OpenLane ASIC Integration
set ::env(DESIGN_NAME) hilbert_transformer_soc
set ::env(VERILOG_FILES) [glob $::env(DESIGN_DIR)/rtl/*.sv]
set ::env(VERILOG_FILES_BLACKBOX) [glob $::env(DESIGN_DIR)/blackbox/*.v]

set ::env(CLOCK_PERIOD) 2.0
set ::env(CLOCK_PORT) clk_i

set ::env(FP_SIZING) absolute
set ::env(DIE_AREA) "0 0 1000 1000"
set ::env(PLACE_PINS_ARGS) "-random"
```

## Interface Adapters

### AXI-Stream to APB Bridge

```systemverilog
module axi_stream_to_apb_bridge (
    input  logic        clk_i,
    input  logic        rst_n_i,
    
    // AXI-Stream interface
    input  logic [15:0] s_axis_tdata,
    input  logic        s_axis_tvalid,
    output logic        s_axis_tready,
    
    // APB interface
    input  logic        psel_i,
    input  logic        penable_i,
    input  logic        pwrite_i,
    input  logic [31:0] paddr_i,
    input  logic [31:0] pwdata_i,
    output logic [31:0] prdata_o,
    output logic        pready_o,
    output logic        pslverr_o
);

    // Implementation details...
    
endmodule
```

## Verification Integration

### Integration Testbench

```systemverilog
module integration_testbench;

    // Clock and reset
    logic clk_i, rst_n_i;
    
    // AXI-Stream interfaces
    logic [15:0] s_axis_tdata, m_axis_tdata;
    logic s_axis_tvalid, s_axis_tready, m_axis_tvalid, m_axis_tready;
    
    // DUT instantiation
    soc_integration dut (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready)
    );
    
    // Test stimulus and verification
    // ...

endmodule
```

## Performance Considerations

### Clock Domain Crossing

When integrating across different clock domains:

```systemverilog
module clock_domain_crossing #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                src_clk_i,
    input  logic                dst_clk_i,
    input  logic                rst_n_i,
    input  logic [DATA_WIDTH-1:0] src_data_i,
    input  logic                src_valid_i,
    output logic                src_ready_o,
    output logic [DATA_WIDTH-1:0] dst_data_o,
    output logic                dst_valid_o,
    input  logic                dst_ready_i
);

    // Dual-clock FIFO implementation
    // ...

endmodule
```

### Reset Synchronization

```systemverilog
module reset_synchronizer (
    input  logic clk_i,
    input  logic rst_n_i,
    output logic rst_n_o
);

    logic rst_meta, rst_sync;
    
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rst_meta <= 1'b0;
            rst_sync <= 1'b0;
        end else begin
            rst_meta <= 1'b1;
            rst_sync <= rst_meta;
        end
    end
    
    assign rst_n_o = rst_sync;

endmodule
```

## Configuration and Control

### Runtime Configuration

```systemverilog
module configuration_controller (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [31:0] config_data_i,
    input  logic        config_valid_i,
    output logic [31:0] status_o,
    output logic        config_ready_o
);

    // Configuration register bank
    logic [31:0] config_regs [4];
    logic [31:0] status_regs [4];
    
    // Configuration logic
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            config_regs <= '{default: 32'h0};
            status_regs <= '{default: 32'h0};
        end else if (config_valid_i) begin
            // Update configuration registers
            config_regs[0] <= config_data_i;
        end
    end
    
    assign status_o = status_regs[0];
    assign config_ready_o = 1'b1;

endmodule
```

## Power Management

### Clock Gating

```systemverilog
module clock_gating_controller (
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic enable_i,
    output logic clk_gated_o
);

    logic enable_latch;
    
    always_latch begin
        if (!clk_i) begin
            enable_latch <= enable_i;
        end
    end
    
    assign clk_gated_o = clk_i && enable_latch;

endmodule
```

## Testing and Validation

### Integration Test Suite

```bash
# Run integration tests
make -C integration test

# Run specific integration tests
make -C integration test-soc
make -C integration test-fpga
make -C integration test-asic

# Run with coverage
make -C integration test-coverage
```

### Performance Validation

```systemverilog
module performance_monitor (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        start_i,
    input  logic        stop_i,
    output logic [31:0] cycle_count_o,
    output logic [31:0] throughput_o
);

    // Performance monitoring logic
    // ...

endmodule
```

## Troubleshooting

### Common Integration Issues

1. **Clock Domain Issues**
   - Use proper clock domain crossing logic
   - Ensure reset synchronization
   - Check timing constraints

2. **Protocol Violations**
   - Verify AXI-Stream handshake compliance
   - Check backpressure handling
   - Validate data integrity

3. **Performance Issues**
   - Monitor throughput and latency
   - Check resource utilization
   - Verify timing closure

### Debug Tools

- **Protocol Checker**: Validates AXI-Stream compliance
- **Performance Monitor**: Measures throughput and latency
- **Coverage Collector**: Tracks functional coverage
- **Waveform Viewer**: Visualizes signal behavior

## Support

For integration support:

1. Check the troubleshooting section above
2. Review the example designs in this directory
3. Consult the main project documentation
4. Contact the Vyges team for support

## License

This work is licensed under the Apache License, Version 2.0. See the LICENSE file for details. 