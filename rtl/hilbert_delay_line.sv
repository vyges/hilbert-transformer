//=============================================================================
// Module Name: hilbert_delay_line
//=============================================================================
// Description: Delay line buffer for Hilbert transformer
//              Stores historical samples for FIR filter processing
//              Supports configurable filter orders and data widths
//
// Features:
// - Configurable delay depth (FILTER_ORDER)
// - Configurable data width
// - Efficient memory usage
// - Single-cycle read access
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

`timescale 1ns / 1ps

module hilbert_delay_line #(
    parameter int DATA_WIDTH = 16,        // Data width (8-32)
    parameter int FILTER_ORDER = 64       // Filter order (16-256)
)(
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    write_en_i,
    input  logic [DATA_WIDTH-1:0]   data_i,
    input  logic [ADDR_WIDTH-1:0]   read_addr_i,
    output logic [DATA_WIDTH-1:0]   data_o
);

    //=============================================================================
    // Local Parameters
    //=============================================================================
    localparam int ADDR_WIDTH = $clog2(FILTER_ORDER);
    
    //=============================================================================
    // Delay Line Memory
    //=============================================================================
    logic [DATA_WIDTH-1:0] delay_memory [FILTER_ORDER-1:0];
    
    //=============================================================================
    // Write Logic (Shift Register Behavior)
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            // Initialize all delay elements to zero
            for (int i = 0; i < FILTER_ORDER; i++) begin
                delay_memory[i] <= '0;
            end
        end else if (write_en_i) begin
            // Shift all elements and insert new data at position 0
            for (int i = FILTER_ORDER-1; i > 0; i--) begin
                delay_memory[i] <= delay_memory[i-1];
            end
            delay_memory[0] <= data_i;
        end
    end
    
    //=============================================================================
    // Read Logic
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            data_o <= '0;
        end else begin
            if (read_addr_i < FILTER_ORDER) begin
                data_o <= delay_memory[read_addr_i];
            end else begin
                data_o <= '0; // Out of range access returns zero
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
    end
    
    // Coverage points
    covergroup delay_line_cg @(posedge clk_i);
        write_enable: coverpoint write_en_i;
        read_addr: coverpoint read_addr_i {
            bins valid_addr = {[0:FILTER_ORDER-1]};
            bins invalid_addr = {[FILTER_ORDER:$]};
        }
        data_value: coverpoint data_i {
            bins zero = {0};
            bins positive = {[1:$]};
            bins negative = {[$:0]};
        }
        
        // Cross coverage
        write_read: cross write_enable, read_addr;
        write_data: cross write_enable, data_value;
    endgroup
    
    delay_line_cg cg_inst = new();
    
endmodule : hilbert_delay_line 