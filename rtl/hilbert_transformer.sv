//=============================================================================
// Module Name: hilbert_transformer
//=============================================================================
// Description: Fully pipelined digital Hilbert transformer for DSP applications
//              Implements FIR filter-based Hilbert transform with AXI-Stream interface
//              Supports configurable data width, filter order, and pipeline stages
//
// Features:
// - Fully pipelined architecture for maximum throughput
// - Configurable data width (8-32 bits)
// - Configurable filter order (16-256 taps)
// - AXI-Stream input/output interface
// - Configuration and status registers
// - Overflow detection and error reporting
//
// Applications: Single sideband modulation/demodulation, amplitude/phase detection,
//               quadrature signal processing, digital communications
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

`timescale 1ns / 1ps

module hilbert_transformer #(
    parameter int DATA_WIDTH = 16,        // Data width (8, 16, 24, 32)
    parameter int FILTER_ORDER = 64,      // FIR filter order (16, 32, 64, 128, 256)
    parameter int PIPELINE_STAGES = 8,    // Number of pipeline stages (4-16)
    parameter int COEFF_WIDTH = 18,       // Coefficient width (16-24)
    parameter int ACCUM_WIDTH = 32        // Accumulator width
)(
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_n_i,
    
    // AXI-Stream Input Interface
    input  logic [DATA_WIDTH-1:0] tdata_i,
    input  logic                  tvalid_i,
    output logic                  tready_o,
    
    // AXI-Stream Output Interface
    output logic [DATA_WIDTH-1:0] tdata_o,
    output logic                  tvalid_o,
    input  logic                  tready_i,
    
    // Control Interface
    input  logic         config_valid_i,
    input  logic [31:0]  config_data_i,
    output logic [31:0]  status_o
);

    //=============================================================================
    // Local Parameters and Types
    //=============================================================================
    localparam int ADDR_WIDTH = $clog2(FILTER_ORDER);
    localparam int MULT_WIDTH = DATA_WIDTH + COEFF_WIDTH;
    localparam int LATENCY = PIPELINE_STAGES + FILTER_ORDER/2;
    localparam int NUM_MULTIPLIERS = FILTER_ORDER/2;
    
    // Configuration register structure
    typedef struct packed {
        logic [7:0]  filter_order;    // Filter order selection
        logic [7:0]  data_width;      // Data width configuration
        logic [7:0]  pipeline_mode;   // Pipeline configuration
        logic [7:0]  reserved;        // Reserved for future use
    } config_reg_t;
    
    // Status register structure
    typedef struct packed {
        logic [15:0] sample_count;    // Processed sample count
        logic [7:0]  error_flags;     // Error status flags
        logic [7:0]  status_flags;    // General status flags
    } status_reg_t;
    
    //=============================================================================
    // Internal Signals
    //=============================================================================
    config_reg_t config_reg;
    status_reg_t status_reg;
    
    // Delay line interface
    logic [DATA_WIDTH-1:0] delay_line_data [FILTER_ORDER-1:0];
    logic                  delay_line_write_en;
    logic [ADDR_WIDTH-1:0]  delay_line_read_addr;
    logic [DATA_WIDTH-1:0]  delay_line_read_data;
    
    // Coefficient ROM interface
    logic [ADDR_WIDTH-1:0]  coeff_rom_addr;
    logic [COEFF_WIDTH-1:0] coeff_rom_data;
    
    // Multiplier array interface
    logic [DATA_WIDTH-1:0]   mult_data_array [FILTER_ORDER-1:0];
    logic [COEFF_WIDTH-1:0]  mult_coeff_array [NUM_MULTIPLIERS-1:0];
    logic [MULT_WIDTH-1:0]   mult_results [NUM_MULTIPLIERS-1:0];
    logic                    mult_overflow;
    
    // Adder tree interface
    logic [MULT_WIDTH-1:0]   adder_inputs [NUM_MULTIPLIERS-1:0];
    logic [ACCUM_WIDTH-1:0]  adder_result;
    logic                    adder_overflow;
    
    // Pipeline registers
    logic [DATA_WIDTH-1:0] pipeline_data [PIPELINE_STAGES-1:0];
    logic                  pipeline_valid [PIPELINE_STAGES-1:0];
    
    // Control signals
    logic                  processing;
    logic                  overflow_detected;
    logic [15:0]           sample_counter;
    logic                  input_handshake;
    logic                  output_handshake;
    
    //=============================================================================
    // AXI-Stream Handshake Logic
    //=============================================================================
    assign input_handshake = tvalid_i && tready_o;
    assign output_handshake = tvalid_o && tready_i;
    
    // Input ready logic
    assign tready_o = !processing || (pipeline_valid[PIPELINE_STAGES-1] && tready_i);
    
    // Output valid logic
    assign tvalid_o = pipeline_valid[PIPELINE_STAGES-1];
    
    //=============================================================================
    // Configuration and Status Registers
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            config_reg <= '0;
            status_reg <= '0;
        end else begin
            if (config_valid_i) begin
                config_reg <= config_data_i;
            end
            
            // Update status register
            status_reg.sample_count <= sample_counter;
            status_reg.error_flags <= {overflow_detected, mult_overflow, adder_overflow, 5'b0};
            status_reg.status_flags <= {processing, 7'b0};
        end
    end
    
    assign status_o = status_reg;
    
    //=============================================================================
    // Delay Line Buffer
    //=============================================================================
    assign delay_line_write_en = input_handshake;
    assign delay_line_read_addr = 0; // Read from all taps in parallel
    
    hilbert_delay_line #(
        .DATA_WIDTH(DATA_WIDTH),
        .FILTER_ORDER(FILTER_ORDER)
    ) delay_line_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .write_en_i(delay_line_write_en),
        .data_i(tdata_i),
        .read_addr_i(delay_line_read_addr),
        .data_o(delay_line_read_data)
    );
    
    // Connect delay line data to multiplier array
    always_comb begin
        for (int i = 0; i < FILTER_ORDER; i++) begin
            delay_line_data[i] = delay_line_read_data;
        end
    end
    
    //=============================================================================
    // Coefficient ROM
    //=============================================================================
    assign coeff_rom_addr = 0; // Read all coefficients in parallel
    
    hilbert_coefficient_rom #(
        .FILTER_ORDER(FILTER_ORDER),
        .COEFF_WIDTH(COEFF_WIDTH)
    ) coeff_rom_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .addr_i(coeff_rom_addr),
        .coeff_o(coeff_rom_data)
    );
    
    // Connect coefficient data to multiplier array
    always_comb begin
        for (int i = 0; i < NUM_MULTIPLIERS; i++) begin
            mult_coeff_array[i] = coeff_rom_data;
        end
    end
    
    //=============================================================================
    // Multiplier Array
    //=============================================================================
    assign mult_data_array = delay_line_data;
    assign adder_inputs = mult_results;
    
    hilbert_multiplier_array #(
        .DATA_WIDTH(DATA_WIDTH),
        .COEFF_WIDTH(COEFF_WIDTH),
        .FILTER_ORDER(FILTER_ORDER)
    ) multiplier_array_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(processing),
        .data_array_i(mult_data_array),
        .coeff_array_i(mult_coeff_array),
        .mult_results_o(mult_results),
        .overflow_o(mult_overflow)
    );
    
    //=============================================================================
    // Adder Tree
    //=============================================================================
    hilbert_adder_tree #(
        .MULT_WIDTH(MULT_WIDTH),
        .ACCUM_WIDTH(ACCUM_WIDTH),
        .NUM_INPUTS(NUM_MULTIPLIERS),
        .PIPELINE_STAGES(PIPELINE_STAGES/2)
    ) adder_tree_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(processing),
        .mult_inputs_i(adder_inputs),
        .accum_result_o(adder_result),
        .overflow_o(adder_overflow)
    );
    
    //=============================================================================
    // Pipeline Stages
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            for (int i = 0; i < PIPELINE_STAGES; i++) begin
                pipeline_data[i] <= '0;
                pipeline_valid[i] <= 1'b0;
            end
        end else begin
            // Pipeline stage 0: Adder tree output
            pipeline_data[0] <= adder_result[DATA_WIDTH-1:0];
            pipeline_valid[0] <= processing;
            
            // Remaining pipeline stages
            for (int i = 1; i < PIPELINE_STAGES; i++) begin
                pipeline_data[i] <= pipeline_data[i-1];
                pipeline_valid[i] <= pipeline_valid[i-1];
            end
        end
    end
    
    //=============================================================================
    // Output Assignment
    //=============================================================================
    assign tdata_o = pipeline_data[PIPELINE_STAGES-1];
    
    //=============================================================================
    // Control Logic
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            processing <= 1'b0;
            sample_counter <= '0;
            overflow_detected <= 1'b0;
        end else begin
            if (input_handshake) begin
                processing <= 1'b1;
                sample_counter <= sample_counter + 1;
            end
            
            // Overflow detection
            if (mult_overflow || adder_overflow) begin
                overflow_detected <= 1'b1;
            end
        end
    end
    
    //=============================================================================
    // Assertions and Coverage
    //=============================================================================
    
    // Check for valid parameter combinations
    initial begin
        assert (DATA_WIDTH >= 8 && DATA_WIDTH <= 32) else
            $error("DATA_WIDTH must be between 8 and 32");
        assert (FILTER_ORDER >= 16 && FILTER_ORDER <= 256) else
            $error("FILTER_ORDER must be between 16 and 256");
        assert (PIPELINE_STAGES >= 4 && PIPELINE_STAGES <= 16) else
            $error("PIPELINE_STAGES must be between 4 and 16");
        assert (COEFF_WIDTH >= 16 && COEFF_WIDTH <= 24) else
            $error("COEFF_WIDTH must be between 16 and 24");
        assert (ACCUM_WIDTH >= 16 && ACCUM_WIDTH <= 48) else
            $error("ACCUM_WIDTH must be between 16 and 48");
        assert (FILTER_ORDER % 2 == 0) else
            $error("FILTER_ORDER must be even");
    end
    
    // AXI-Stream protocol assertions
    property axi_stream_valid_ready;
        @(posedge clk_i) disable iff (!rst_n_i)
        tvalid_i && !tready_o |-> ##1 tvalid_i;
    endproperty
    
    property axi_stream_ready_after_valid;
        @(posedge clk_i) disable iff (!rst_n_i)
        tvalid_i && tready_o |-> ##1 tready_o;
    endproperty
    
    assert property (axi_stream_valid_ready) else
        $error("AXI-Stream: tvalid must remain asserted until tready");
    
    assert property (axi_stream_ready_after_valid) else
        $error("AXI-Stream: tready must remain asserted after handshake");
    
    // Coverage points
    covergroup hilbert_transformer_cg @(posedge clk_i);
        input_valid: coverpoint tvalid_i;
        input_ready: coverpoint tready_o;
        output_valid: coverpoint tvalid_o;
        output_ready: coverpoint tready_i;
        config_valid: coverpoint config_valid_i;
        overflow: coverpoint overflow_detected;
        mult_overflow: coverpoint mult_overflow;
        adder_overflow: coverpoint adder_overflow;
        
        // Cross coverage
        input_handshake: cross input_valid, input_ready;
        output_handshake: cross output_valid, output_ready;
        overflow_types: cross overflow, mult_overflow, adder_overflow;
    endgroup
    
    hilbert_transformer_cg cg_inst = new();
    
endmodule : hilbert_transformer 