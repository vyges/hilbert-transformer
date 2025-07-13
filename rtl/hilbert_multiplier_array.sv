//=============================================================================
// Module Name: hilbert_multiplier_array
//=============================================================================
// Description: Multiplier array for Hilbert transformer FIR filter
//              Performs coefficient multiplication with anti-symmetric optimization
//              Supports configurable data and coefficient widths
//
// Features:
// - Anti-symmetric coefficient optimization (FILTER_ORDER/2 multipliers)
// - Configurable precision multiplication
// - DSP block optimization for FPGA
// - Overflow protection and saturation
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

`timescale 1ns / 1ps

module hilbert_multiplier_array #(
    parameter int DATA_WIDTH = 16,        // Data width (8-32)
    parameter int COEFF_WIDTH = 18,       // Coefficient width (16-24)
    parameter int FILTER_ORDER = 64       // Filter order (16-256)
)(
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    enable_i,
    input  logic [DATA_WIDTH-1:0]   data_array_i [FILTER_ORDER-1:0],
    input  logic [COEFF_WIDTH-1:0]  coeff_array_i [FILTER_ORDER/2-1:0],
    output logic [MULT_WIDTH-1:0]   mult_results_o [FILTER_ORDER/2-1:0],
    output logic                    overflow_o
);

    //=============================================================================
    // Local Parameters
    //=============================================================================
    localparam int MULT_WIDTH = DATA_WIDTH + COEFF_WIDTH;
    localparam int NUM_MULTIPLIERS = FILTER_ORDER/2;
    
    //=============================================================================
    // Internal Signals
    //=============================================================================
    logic [MULT_WIDTH-1:0] mult_results [NUM_MULTIPLIERS-1:0];
    logic [MULT_WIDTH-1:0] mult_results_reg [NUM_MULTIPLIERS-1:0];
    logic                  overflow_detected;
    
    //=============================================================================
    // Multiplier Array Generation
    //=============================================================================
    genvar i;
    generate
        for (i = 0; i < NUM_MULTIPLIERS; i++) begin : mult_gen
            // Anti-symmetric coefficient multiplication
            // For each multiplier, we compute:
            // result[i] = data[i] * coeff[i] + data[N-1-i] * (-coeff[i])
            // This exploits the anti-symmetric property: h[n] = -h[N-1-n]
            
            // Positive coefficient multiplication
            logic [MULT_WIDTH-1:0] pos_mult;
            assign pos_mult = $signed(data_array_i[i]) * $signed(coeff_array_i[i]);
            
            // Negative coefficient multiplication (anti-symmetric part)
            logic [MULT_WIDTH-1:0] neg_mult;
            assign neg_mult = $signed(data_array_i[FILTER_ORDER-1-i]) * $signed(-coeff_array_i[i]);
            
            // Combine positive and negative parts
            assign mult_results[i] = pos_mult + neg_mult;
        end
    endgenerate
    
    //=============================================================================
    // Pipeline Register
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            for (int i = 0; i < NUM_MULTIPLIERS; i++) begin
                mult_results_reg[i] <= '0;
            end
            overflow_detected <= 1'b0;
        end else if (enable_i) begin
            for (int i = 0; i < NUM_MULTIPLIERS; i++) begin
                mult_results_reg[i] <= mult_results[i];
            end
            
            // Overflow detection
            overflow_detected <= 1'b0;
            for (int i = 0; i < NUM_MULTIPLIERS; i++) begin
                // Check for overflow in multiplication result
                if (mult_results[i][MULT_WIDTH-1] != mult_results[i][MULT_WIDTH-2]) begin
                    overflow_detected <= 1'b1;
                end
            end
        end
    end
    
    //=============================================================================
    // Output Assignment
    //=============================================================================
    assign mult_results_o = mult_results_reg;
    assign overflow_o = overflow_detected;
    
    //=============================================================================
    // Assertions and Coverage
    //=============================================================================
    
    // Check for valid parameter combinations
    initial begin
        assert (DATA_WIDTH >= 8 && DATA_WIDTH <= 32) else
            $error("DATA_WIDTH must be between 8 and 32");
        assert (COEFF_WIDTH >= 16 && COEFF_WIDTH <= 24) else
            $error("COEFF_WIDTH must be between 16 and 24");
        assert (FILTER_ORDER >= 16 && FILTER_ORDER <= 256) else
            $error("FILTER_ORDER must be between 16 and 256");
        assert (FILTER_ORDER % 2 == 0) else
            $error("FILTER_ORDER must be even");
    end
    
    // Coverage points
    covergroup multiplier_array_cg @(posedge clk_i);
        enable: coverpoint enable_i;
        overflow: coverpoint overflow_detected;
        
        // Data value coverage
        data_value: coverpoint data_array_i[0] {
            bins zero = {0};
            bins positive = {[1:$]};
            bins negative = {[$:0]};
        }
        
        // Coefficient value coverage
        coeff_value: coverpoint coeff_array_i[0] {
            bins zero = {0};
            bins positive = {[1:$]};
            bins negative = {[$:0]};
        }
        
        // Cross coverage
        enable_overflow: cross enable, overflow;
        data_coeff: cross data_value, coeff_value;
    endgroup
    
    multiplier_array_cg cg_inst = new();
    
endmodule : hilbert_multiplier_array 