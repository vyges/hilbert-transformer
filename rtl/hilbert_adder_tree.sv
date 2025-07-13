//=============================================================================
// Module Name: hilbert_adder_tree
//=============================================================================
// Description: Pipelined adder tree for Hilbert transformer
//              Accumulates multiplier results with configurable pipeline stages
//              Supports overflow protection and saturation
//
// Features:
// - Configurable pipeline stages for timing optimization
// - Overflow protection and saturation handling
// - Balanced binary tree structure
// - Configurable accumulator width
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

`timescale 1ns / 1ps

module hilbert_adder_tree #(
    parameter int MULT_WIDTH = 34,        // Multiplier output width
    parameter int ACCUM_WIDTH = 32,       // Accumulator width
    parameter int NUM_INPUTS = 32,        // Number of inputs (FILTER_ORDER/2)
    parameter int PIPELINE_STAGES = 4     // Number of pipeline stages
)(
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    enable_i,
    input  logic [MULT_WIDTH-1:0]   mult_inputs_i [NUM_INPUTS-1:0],
    output logic [ACCUM_WIDTH-1:0]  accum_result_o,
    output logic                    overflow_o
);

    //=============================================================================
    // Local Parameters
    //=============================================================================
    localparam int TREE_LEVELS = $clog2(NUM_INPUTS);
    localparam int STAGES_PER_LEVEL = PIPELINE_STAGES / TREE_LEVELS;
    
    //=============================================================================
    // Internal Signals
    //=============================================================================
    logic [ACCUM_WIDTH-1:0] tree_nodes [TREE_LEVELS][NUM_INPUTS-1:0];
    logic [ACCUM_WIDTH-1:0] tree_nodes_reg [TREE_LEVELS][NUM_INPUTS-1:0];
    logic                  overflow_detected;
    
    //=============================================================================
    // Adder Tree Generation
    //=============================================================================
    genvar level, node;
    generate
        // Level 0: Input stage with sign extension and saturation
        for (node = 0; node < NUM_INPUTS; node++) begin : level0
            // Sign extend and saturate multiplier outputs to accumulator width
            always_comb begin
                if (MULT_WIDTH > ACCUM_WIDTH) begin
                    // Truncate and saturate
                    if (mult_inputs_i[node][MULT_WIDTH-1] == 1'b0) begin
                        // Positive number
                        if (mult_inputs_i[node][MULT_WIDTH-1:ACCUM_WIDTH-1] != '0) begin
                            tree_nodes[0][node] = {1'b0, {(ACCUM_WIDTH-1){1'b1}}}; // Saturate to max positive
                        end else begin
                            tree_nodes[0][node] = mult_inputs_i[node][ACCUM_WIDTH-1:0];
                        end
                    end else begin
                        // Negative number
                        if (mult_inputs_i[node][MULT_WIDTH-1:ACCUM_WIDTH-1] != '1) begin
                            tree_nodes[0][node] = {1'b1, {(ACCUM_WIDTH-1){1'b0}}}; // Saturate to max negative
                        end else begin
                            tree_nodes[0][node] = mult_inputs_i[node][ACCUM_WIDTH-1:0];
                        end
                    end
                end else begin
                    // Sign extend
                    tree_nodes[0][node] = $signed(mult_inputs_i[node]);
                end
            end
        end
        
        // Higher levels: Adder tree
        for (level = 1; level < TREE_LEVELS; level++) begin : tree_level
            for (node = 0; node < NUM_INPUTS/(2**level); node++) begin : tree_node
                // Add pairs of nodes from previous level
                always_comb begin
                    tree_nodes[level][node] = $signed(tree_nodes_reg[level-1][2*node]) + 
                                             $signed(tree_nodes_reg[level-1][2*node+1]);
                end
            end
        end
    endgenerate
    
    //=============================================================================
    // Pipeline Registers
    //=============================================================================
    genvar pl, pn;
    generate
        for (pl = 0; pl < TREE_LEVELS; pl++) begin : pipe_level
            for (pn = 0; pn < NUM_INPUTS/(2**pl); pn++) begin : pipe_node
                always_ff @(posedge clk_i or negedge rst_n_i) begin
                    if (!rst_n_i) begin
                        tree_nodes_reg[pl][pn] <= '0;
                    end else if (enable_i) begin
                        tree_nodes_reg[pl][pn] <= tree_nodes[pl][pn];
                    end
                end
            end
        end
    endgenerate
    
    //=============================================================================
    // Final Accumulator
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            accum_result_o <= '0;
            overflow_detected <= 1'b0;
        end else if (enable_i) begin
            // Final result is the sum of the last level
            accum_result_o <= tree_nodes_reg[TREE_LEVELS-1][0];
            
            // Overflow detection
            overflow_detected <= 1'b0;
            for (int i = 0; i < TREE_LEVELS; i++) begin
                for (int j = 0; j < NUM_INPUTS/(2**i); j++) begin
                    // Check for overflow in addition
                    if (tree_nodes[i][j][ACCUM_WIDTH-1] != tree_nodes[i][j][ACCUM_WIDTH-2]) begin
                        overflow_detected <= 1'b1;
                    end
                end
            end
        end
    end
    
    assign overflow_o = overflow_detected;
    
    //=============================================================================
    // Assertions and Coverage
    //=============================================================================
    
    // Check for valid parameter combinations
    initial begin
        assert (MULT_WIDTH >= 16 && MULT_WIDTH <= 48) else
            $error("MULT_WIDTH must be between 16 and 48");
        assert (ACCUM_WIDTH >= 16 && ACCUM_WIDTH <= 48) else
            $error("ACCUM_WIDTH must be between 16 and 48");
        assert (NUM_INPUTS >= 2 && NUM_INPUTS <= 128) else
            $error("NUM_INPUTS must be between 2 and 128");
        assert (PIPELINE_STAGES >= 1 && PIPELINE_STAGES <= 8) else
            $error("PIPELINE_STAGES must be between 1 and 8");
        assert (NUM_INPUTS % 2 == 0) else
            $error("NUM_INPUTS must be even");
    end
    
    // Coverage points
    covergroup adder_tree_cg @(posedge clk_i);
        enable: coverpoint enable_i;
        overflow: coverpoint overflow_detected;
        
        // Input value coverage
        input_value: coverpoint mult_inputs_i[0] {
            bins zero = {0};
            bins positive = {[1:$]};
            bins negative = {[$:0]};
        }
        
        // Result value coverage
        result_value: coverpoint accum_result_o {
            bins zero = {0};
            bins positive = {[1:$]};
            bins negative = {[$:0]};
        }
        
        // Cross coverage
        enable_overflow: cross enable, overflow;
        input_result: cross input_value, result_value;
    endgroup
    
    adder_tree_cg cg_inst = new();
    
endmodule : hilbert_adder_tree 