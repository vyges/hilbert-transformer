//=============================================================================
// Example SoC Integration
//=============================================================================
// Description: Complete SoC integration example for Hilbert Transformer IP
//              Demonstrates AXI-Stream integration, configuration, and control
//
// Features:
// - AXI-Stream interface integration
// - Configuration and status management
// - Clock and reset management
// - Performance monitoring
// - Error handling and reporting
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

module example_soc #(
    parameter int DATA_WIDTH = 16,
    parameter int FILTER_ORDER = 64,
    parameter int PIPELINE_STAGES = 8,
    parameter int COEFF_WIDTH = 18,
    parameter int ACCUM_WIDTH = 32
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    
    // AXI-Stream input interface
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata,
    input  logic                    s_axis_tvalid,
    output logic                    s_axis_tready,
    input  logic                    s_axis_tlast,
    input  logic [7:0]              s_axis_tuser,
    input  logic [3:0]              s_axis_tid,
    input  logic [3:0]              s_axis_tdest,
    
    // AXI-Stream output interface
    output logic [DATA_WIDTH-1:0]   m_axis_tdata,
    output logic                    m_axis_tvalid,
    input  logic                    m_axis_tready,
    output logic                    m_axis_tlast,
    output logic [7:0]              m_axis_tuser,
    output logic [3:0]              m_axis_tid,
    output logic [3:0]              m_axis_tdest,
    
    // Configuration interface
    input  logic [31:0]             config_data_i,
    input  logic                    config_valid_i,
    output logic [31:0]             status_o,
    output logic                    config_ready_o,
    
    // Interrupt interface
    output logic                    irq_o,
    output logic [7:0]              irq_id_o,
    
    // Debug interface
    output logic [31:0]             debug_o
);

    //=============================================================================
    // Internal Signals
    //=============================================================================
    // Clock and reset
    logic clk_sys, rst_n_sys;
    logic clk_dsp, rst_n_dsp;
    
    // AXI-Stream internal signals
    logic [DATA_WIDTH-1:0] hilbert_tdata_i, hilbert_tdata_o;
    logic hilbert_tvalid_i, hilbert_tvalid_o;
    logic hilbert_tready_o, hilbert_tready_i;
    logic hilbert_tlast_i, hilbert_tlast_o;
    logic [7:0] hilbert_tuser_i, hilbert_tuser_o;
    logic [3:0] hilbert_tid_i, hilbert_tid_o;
    logic [3:0] hilbert_tdest_i, hilbert_tdest_o;
    
    // Configuration and status
    logic [31:0] hilbert_config, hilbert_status;
    logic [31:0] adapter_config, adapter_status;
    logic [31:0] performance_counters;
    
    // Control and status
    logic enable_processing;
    logic error_detected;
    logic overflow_detected;
    logic underflow_detected;
    
    //=============================================================================
    // Clock and Reset Management
    //=============================================================================
    // Clock domain crossing for reset
    reset_synchronizer reset_sync_sys (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .rst_n_o(rst_n_sys)
    );
    
    // DSP clock (same as system clock for this example)
    assign clk_dsp = clk_i;
    assign rst_n_dsp = rst_n_sys;
    
    //=============================================================================
    // Input AXI-Stream Adapter
    //=============================================================================
    axi_stream_adapter #(
        .DATA_WIDTH(DATA_WIDTH),
        .FIFO_DEPTH(32),
        .TUSER_WIDTH(8),
        .TID_WIDTH(4),
        .TDEST_WIDTH(4)
    ) input_adapter (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .s_axis_tuser(s_axis_tuser),
        .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest),
        .m_axis_tdata(hilbert_tdata_i),
        .m_axis_tvalid(hilbert_tvalid_i),
        .m_axis_tready(hilbert_tready_o),
        .m_axis_tlast(hilbert_tlast_i),
        .m_axis_tuser(hilbert_tuser_i),
        .m_axis_tid(hilbert_tid_i),
        .m_axis_tdest(hilbert_tdest_i),
        .status_o(adapter_status),
        .config_i(adapter_config),
        .config_valid_i(config_valid_i)
    );
    
    //=============================================================================
    // Hilbert Transformer Core
    //=============================================================================
    hilbert_transformer #(
        .DATA_WIDTH(DATA_WIDTH),
        .FILTER_ORDER(FILTER_ORDER),
        .PIPELINE_STAGES(PIPELINE_STAGES),
        .COEFF_WIDTH(COEFF_WIDTH),
        .ACCUM_WIDTH(ACCUM_WIDTH)
    ) hilbert_inst (
        .clk_i(clk_dsp),
        .rst_n_i(rst_n_dsp),
        .tdata_i(hilbert_tdata_i),
        .tvalid_i(hilbert_tvalid_i),
        .tready_o(hilbert_tready_o),
        .tdata_o(hilbert_tdata_o),
        .tvalid_o(hilbert_tvalid_o),
        .tready_i(hilbert_tready_i),
        .config_valid_i(config_valid_i),
        .config_data_i(hilbert_config),
        .status_o(hilbert_status)
    );
    
    //=============================================================================
    // Output AXI-Stream Adapter
    //=============================================================================
    axi_stream_adapter #(
        .DATA_WIDTH(DATA_WIDTH),
        .FIFO_DEPTH(32),
        .TUSER_WIDTH(8),
        .TID_WIDTH(4),
        .TDEST_WIDTH(4)
    ) output_adapter (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .s_axis_tdata(hilbert_tdata_o),
        .s_axis_tvalid(hilbert_tvalid_o),
        .s_axis_tready(hilbert_tready_i),
        .s_axis_tlast(hilbert_tlast_o),
        .s_axis_tuser(hilbert_tuser_o),
        .s_axis_tid(hilbert_tid_o),
        .s_axis_tdest(hilbert_tdest_o),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast),
        .m_axis_tuser(m_axis_tuser),
        .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest),
        .status_o(),
        .config_i(32'h0),
        .config_valid_i(1'b0)
    );
    
    //=============================================================================
    // Configuration Controller
    //=============================================================================
    configuration_controller config_ctrl (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .config_data_i(config_data_i),
        .config_valid_i(config_valid_i),
        .status_o(status_o),
        .config_ready_o(config_ready_o),
        .hilbert_config_o(hilbert_config),
        .adapter_config_o(adapter_config),
        .enable_processing_o(enable_processing)
    );
    
    //=============================================================================
    // Performance Monitor
    //=============================================================================
    performance_monitor perf_mon (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .enable_i(enable_processing),
        .input_valid_i(s_axis_tvalid),
        .input_ready_i(s_axis_tready),
        .output_valid_i(m_axis_tvalid),
        .output_ready_i(m_axis_tready),
        .error_detected_i(error_detected),
        .overflow_detected_i(overflow_detected),
        .underflow_detected_i(underflow_detected),
        .performance_counters_o(performance_counters)
    );
    
    //=============================================================================
    // Error Detection and Handling
    //=============================================================================
    error_detector error_detect (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .adapter_status_i(adapter_status),
        .hilbert_status_i(hilbert_status),
        .error_detected_o(error_detected),
        .overflow_detected_o(overflow_detected),
        .underflow_detected_o(underflow_detected)
    );
    
    //=============================================================================
    // Interrupt Controller
    //=============================================================================
    interrupt_controller irq_ctrl (
        .clk_i(clk_sys),
        .rst_n_i(rst_n_sys),
        .error_detected_i(error_detected),
        .overflow_detected_i(overflow_detected),
        .underflow_detected_i(underflow_detected),
        .performance_counters_i(performance_counters),
        .irq_o(irq_o),
        .irq_id_o(irq_id_o)
    );
    
    //=============================================================================
    // Debug Interface
    //=============================================================================
    assign debug_o = {
        error_detected,              // [31]
        overflow_detected,           // [30]
        underflow_detected,          // [29]
        enable_processing,           // [28]
        hilbert_status[27:0]         // [27:0]
    };
    
    //=============================================================================
    // Assertions
    //=============================================================================
    // Protocol compliance assertions
    property axi_stream_protocol;
        @(posedge clk_sys) disable iff (!rst_n_sys)
        s_axis_tvalid && !s_axis_tready |-> ##1 s_axis_tvalid;
    endproperty
    
    property output_protocol;
        @(posedge clk_sys) disable iff (!rst_n_sys)
        m_axis_tvalid && !m_axis_tready |-> ##1 m_axis_tvalid;
    endproperty
    
    // Assertion instances
    assert property (axi_stream_protocol) else
        $error("Input AXI-Stream protocol violation");
    
    assert property (output_protocol) else
        $error("Output AXI-Stream protocol violation");
    
    //=============================================================================
    // Coverage
    //=============================================================================
    // Coverage group for SoC integration
    covergroup soc_cg @(posedge clk_sys);
        input_valid: coverpoint s_axis_tvalid;
        input_ready: coverpoint s_axis_tready;
        output_valid: coverpoint m_axis_tvalid;
        output_ready: coverpoint m_axis_tready;
        error_state: coverpoint error_detected;
        overflow_state: coverpoint overflow_detected;
        underflow_state: coverpoint underflow_detected;
        enable_state: coverpoint enable_processing;
        
        // Cross coverage
        input_handshake: cross input_valid, input_ready;
        output_handshake: cross output_valid, output_ready;
        error_cross: cross error_state, overflow_state, underflow_state;
    endgroup
    
    soc_cg cg_inst = new();

endmodule : example_soc

//=============================================================================
// Configuration Controller
//=============================================================================
module configuration_controller (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [31:0] config_data_i,
    input  logic        config_valid_i,
    output logic [31:0] status_o,
    output logic        config_ready_o,
    output logic [31:0] hilbert_config_o,
    output logic [31:0] adapter_config_o,
    output logic        enable_processing_o
);

    // Configuration registers
    logic [31:0] config_regs [8];
    logic [31:0] status_regs [8];
    logic [7:0] config_addr;
    
    // Configuration logic
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            config_regs <= '{default: 32'h0};
            status_regs <= '{default: 32'h0};
            config_addr <= 8'h0;
        end else if (config_valid_i) begin
            config_addr <= config_data_i[15:8];
            if (config_data_i[7:0] == 8'h00) begin
                // Write configuration
                config_regs[config_data_i[15:8]] <= config_data_i[31:16];
            end else if (config_data_i[7:0] == 8'h01) begin
                // Read status
                status_regs[config_data_i[15:8]] <= config_data_i[31:16];
            end
        end
    end
    
    // Output assignments
    assign hilbert_config_o = config_regs[0];
    assign adapter_config_o = config_regs[1];
    assign enable_processing_o = config_regs[2][0];
    assign status_o = status_regs[0];
    assign config_ready_o = 1'b1;

endmodule : configuration_controller

//=============================================================================
// Performance Monitor
//=============================================================================
module performance_monitor (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        enable_i,
    input  logic        input_valid_i,
    input  logic        input_ready_i,
    input  logic        output_valid_i,
    input  logic        output_ready_i,
    input  logic        error_detected_i,
    input  logic        overflow_detected_i,
    input  logic        underflow_detected_i,
    output logic [31:0] performance_counters_o
);

    // Performance counters
    logic [31:0] input_transfers;
    logic [31:0] output_transfers;
    logic [31:0] error_count;
    logic [31:0] overflow_count;
    logic [31:0] underflow_count;
    
    // Counter logic
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            input_transfers <= 32'h0;
            output_transfers <= 32'h0;
            error_count <= 32'h0;
            overflow_count <= 32'h0;
            underflow_count <= 32'h0;
        end else if (enable_i) begin
            if (input_valid_i && input_ready_i) begin
                input_transfers <= input_transfers + 1;
            end
            if (output_valid_i && output_ready_i) begin
                output_transfers <= output_transfers + 1;
            end
            if (error_detected_i) begin
                error_count <= error_count + 1;
            end
            if (overflow_detected_i) begin
                overflow_count <= overflow_count + 1;
            end
            if (underflow_detected_i) begin
                underflow_count <= underflow_count + 1;
            end
        end
    end
    
    // Performance counters output
    assign performance_counters_o = {
        error_count[7:0],           // [31:24]
        overflow_count[7:0],        // [23:16]
        underflow_count[7:0],       // [15:8]
        input_transfers[7:0]        // [7:0]
    };

endmodule : performance_monitor

//=============================================================================
// Error Detector
//=============================================================================
module error_detector (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [31:0] adapter_status_i,
    input  logic [31:0] hilbert_status_i,
    output logic        error_detected_o,
    output logic        overflow_detected_o,
    output logic        underflow_detected_o
);

    // Error detection logic
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            error_detected_o <= 1'b0;
            overflow_detected_o <= 1'b0;
            underflow_detected_o <= 1'b0;
        end else begin
            // Check for protocol errors
            error_detected_o <= adapter_status_i[26] || hilbert_status_i[8];
            
            // Check for overflow/underflow
            overflow_detected_o <= hilbert_status_i[9];
            underflow_detected_o <= hilbert_status_i[10];
        end
    end

endmodule : error_detector

//=============================================================================
// Interrupt Controller
//=============================================================================
module interrupt_controller (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        error_detected_i,
    input  logic        overflow_detected_i,
    input  logic        underflow_detected_i,
    input  logic [31:0] performance_counters_i,
    output logic        irq_o,
    output logic [7:0]  irq_id_o
);

    // Interrupt generation logic
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            irq_o <= 1'b0;
            irq_id_o <= 8'h0;
        end else begin
            if (error_detected_i) begin
                irq_o <= 1'b1;
                irq_id_o <= 8'h01; // Error interrupt
            end else if (overflow_detected_i) begin
                irq_o <= 1'b1;
                irq_id_o <= 8'h02; // Overflow interrupt
            end else if (underflow_detected_i) begin
                irq_o <= 1'b1;
                irq_id_o <= 8'h03; // Underflow interrupt
            end else begin
                irq_o <= 1'b0;
                irq_id_o <= 8'h0;
            end
        end
    end

endmodule : interrupt_controller

//=============================================================================
// Reset Synchronizer
//=============================================================================
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

endmodule : reset_synchronizer 