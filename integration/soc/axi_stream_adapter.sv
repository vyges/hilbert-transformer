//=============================================================================
// AXI-Stream Protocol Adapter
//=============================================================================
// Description: AXI-Stream protocol adapter for SoC integration
//              Provides buffering, handshake management, and protocol compliance
//
// Features:
// - AXI-Stream protocol compliance
// - Configurable FIFO buffering
// - Backpressure handling
// - Protocol validation
// - Performance monitoring
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

module axi_stream_adapter #(
    parameter int DATA_WIDTH = 16,
    parameter int FIFO_DEPTH = 16,
    parameter int TUSER_WIDTH = 0,
    parameter int TID_WIDTH = 0,
    parameter int TDEST_WIDTH = 0
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    
    // Slave AXI-Stream interface (input)
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata,
    input  logic                    s_axis_tvalid,
    output logic                    s_axis_tready,
    input  logic                    s_axis_tlast,
    input  logic [TUSER_WIDTH-1:0]  s_axis_tuser,
    input  logic [TID_WIDTH-1:0]    s_axis_tid,
    input  logic [TDEST_WIDTH-1:0]  s_axis_tdest,
    
    // Master AXI-Stream interface (output)
    output logic [DATA_WIDTH-1:0]   m_axis_tdata,
    output logic                    m_axis_tvalid,
    input  logic                    m_axis_tready,
    output logic                    m_axis_tlast,
    output logic [TUSER_WIDTH-1:0]  m_axis_tuser,
    output logic [TID_WIDTH-1:0]    m_axis_tid,
    output logic [TDEST_WIDTH-1:0]  m_axis_tdest,
    
    // Status and control
    output logic [31:0]             status_o,
    input  logic [31:0]             config_i,
    input  logic                    config_valid_i
);

    //=============================================================================
    // Internal Signals
    //=============================================================================
    logic [DATA_WIDTH-1:0] fifo_data_in, fifo_data_out;
    logic [TUSER_WIDTH-1:0] fifo_user_in, fifo_user_out;
    logic [TID_WIDTH-1:0] fifo_id_in, fifo_id_out;
    logic [TDEST_WIDTH-1:0] fifo_dest_in, fifo_dest_out;
    logic fifo_last_in, fifo_last_out;
    logic fifo_wr_en, fifo_rd_en;
    logic fifo_full, fifo_empty;
    logic fifo_almost_full, fifo_almost_empty;
    
    // Handshake signals
    logic s_handshake, m_handshake;
    logic s_valid_reg, m_valid_reg;
    
    // Status counters
    logic [31:0] transfer_count;
    logic [31:0] error_count;
    logic [31:0] backpressure_count;
    
    // Configuration registers
    logic [7:0] fifo_threshold;
    logic enable_flow_control;
    logic enable_protocol_checking;
    
    //=============================================================================
    // Configuration Interface
    //=============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            fifo_threshold <= 8'd8;
            enable_flow_control <= 1'b1;
            enable_protocol_checking <= 1'b1;
        end else if (config_valid_i) begin
            fifo_threshold <= config_i[7:0];
            enable_flow_control <= config_i[8];
            enable_protocol_checking <= config_i[9];
        end
    end
    
    //=============================================================================
    // FIFO Implementation
    //=============================================================================
    // Data FIFO
    fifo_sync #(
        .DATA_WIDTH(DATA_WIDTH + TUSER_WIDTH + TID_WIDTH + TDEST_WIDTH + 1),
        .FIFO_DEPTH(FIFO_DEPTH)
    ) data_fifo (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .wr_en_i(fifo_wr_en),
        .rd_en_i(fifo_rd_en),
        .data_in_i({fifo_data_in, fifo_user_in, fifo_id_in, fifo_dest_in, fifo_last_in}),
        .data_out_o({fifo_data_out, fifo_user_out, fifo_id_out, fifo_dest_out, fifo_last_out}),
        .full_o(fifo_full),
        .empty_o(fifo_empty),
        .almost_full_o(fifo_almost_full),
        .almost_empty_o(fifo_almost_empty)
    );
    
    //=============================================================================
    // Handshake Logic
    //=============================================================================
    assign s_handshake = s_axis_tvalid && s_axis_tready;
    assign m_handshake = m_axis_tvalid && m_axis_tready;
    
    // Slave interface handshake
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            s_valid_reg <= 1'b0;
        end else begin
            if (s_handshake) begin
                s_valid_reg <= 1'b0;
            end else if (s_axis_tvalid && !fifo_full) begin
                s_valid_reg <= 1'b1;
            end
        end
    end
    
    // Master interface handshake
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            m_valid_reg <= 1'b0;
        end else begin
            if (m_handshake) begin
                m_valid_reg <= 1'b0;
            end else if (!fifo_empty) begin
                m_valid_reg <= 1'b1;
            end
        end
    end
    
    //=============================================================================
    // FIFO Control
    //=============================================================================
    // Write control
    assign fifo_wr_en = s_handshake && !fifo_full;
    assign fifo_data_in = s_axis_tdata;
    assign fifo_user_in = s_axis_tuser;
    assign fifo_id_in = s_axis_tid;
    assign fifo_dest_in = s_axis_tdest;
    assign fifo_last_in = s_axis_tlast;
    
    // Read control
    assign fifo_rd_en = m_handshake && !fifo_empty;
    
    //=============================================================================
    // Interface Control
    //=============================================================================
    // Slave ready signal
    assign s_axis_tready = enable_flow_control ? 
                          (!fifo_full && (!s_valid_reg || s_handshake)) : 
                          1'b1;
    
    // Master valid signal
    assign m_axis_tvalid = m_valid_reg && !fifo_empty;
    assign m_axis_tdata = fifo_data_out;
    assign m_axis_tuser = fifo_user_out;
    assign m_axis_tid = fifo_id_out;
    assign m_axis_tdest = fifo_dest_out;
    assign m_axis_tlast = fifo_last_out;
    
    //=============================================================================
    // Protocol Checking
    //=============================================================================
    generate
        if (enable_protocol_checking) begin : protocol_checker
            // Protocol validation logic
            always_ff @(posedge clk_i or negedge rst_n_i) begin
                if (!rst_n_i) begin
                    error_count <= 32'h0;
                end else begin
                    // Check for protocol violations
                    if (s_axis_tvalid && !s_axis_tready && s_valid_reg) begin
                        error_count <= error_count + 1;
                    end
                end
            end
        end
    endgenerate
    
    //=============================================================================
    // Performance Monitoring
    //=============================================================================
    // Transfer counter
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            transfer_count <= 32'h0;
        end else if (s_handshake) begin
            transfer_count <= transfer_count + 1;
        end
    end
    
    // Backpressure counter
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            backpressure_count <= 32'h0;
        end else if (s_axis_tvalid && !s_axis_tready) begin
            backpressure_count <= backpressure_count + 1;
        end
    end
    
    //=============================================================================
    // Status Output
    //=============================================================================
    assign status_o = {
        fifo_almost_full,           // [31]
        fifo_almost_empty,          // [30]
        fifo_full,                  // [29]
        fifo_empty,                 // [28]
        enable_flow_control,        // [27]
        enable_protocol_checking,   // [26]
        2'b00,                      // [25:24]
        fifo_threshold,             // [23:16]
        backpressure_count[7:0]     // [15:8]
    };
    
    //=============================================================================
    // Assertions
    //=============================================================================
    // AXI-Stream protocol assertions
    property axi_stream_valid_ready;
        @(posedge clk_i) disable iff (!rst_n_i)
        s_axis_tvalid && !s_axis_tready |-> ##1 s_axis_tvalid;
    endproperty
    
    property axi_stream_ready_after_valid;
        @(posedge clk_i) disable iff (!rst_n_i)
        s_axis_tvalid && s_axis_tready |-> ##1 s_axis_tready;
    endproperty
    
    // Assertion instances
    assert property (axi_stream_valid_ready) else
        $error("AXI-Stream: tvalid must remain asserted until tready");
    
    assert property (axi_stream_ready_after_valid) else
        $error("AXI-Stream: tready must remain asserted after handshake");
    
    //=============================================================================
    // Coverage
    //=============================================================================
    // Coverage group for AXI-Stream interface
    covergroup axi_stream_cg @(posedge clk_i);
        s_valid: coverpoint s_axis_tvalid;
        s_ready: coverpoint s_axis_tready;
        m_valid: coverpoint m_axis_tvalid;
        m_ready: coverpoint m_axis_tready;
        fifo_full_cp: coverpoint fifo_full;
        fifo_empty_cp: coverpoint fifo_empty;
        
        // Cross coverage
        s_handshake_cross: cross s_valid, s_ready;
        m_handshake_cross: cross m_valid, m_ready;
        fifo_state_cross: cross fifo_full_cp, fifo_empty_cp;
    endgroup
    
    axi_stream_cg cg_inst = new();

endmodule : axi_stream_adapter

//=============================================================================
// Synchronous FIFO Module
//=============================================================================
module fifo_sync #(
    parameter int DATA_WIDTH = 32,
    parameter int FIFO_DEPTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    wr_en_i,
    input  logic                    rd_en_i,
    input  logic [DATA_WIDTH-1:0]   data_in_i,
    output logic [DATA_WIDTH-1:0]   data_out_o,
    output logic                    full_o,
    output logic                    empty_o,
    output logic                    almost_full_o,
    output logic                    almost_empty_o
);

    // FIFO memory
    logic [DATA_WIDTH-1:0] fifo_mem [FIFO_DEPTH-1:0];
    
    // Pointers
    logic [$clog2(FIFO_DEPTH):0] wr_ptr, rd_ptr;
    logic [$clog2(FIFO_DEPTH):0] count;
    
    // Status signals
    assign full_o = (count == FIFO_DEPTH);
    assign empty_o = (count == 0);
    assign almost_full_o = (count >= FIFO_DEPTH - 1);
    assign almost_empty_o = (count <= 1);
    
    // Write operation
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
            count <= 0;
        end else begin
            if (wr_en_i && !full_o) begin
                fifo_mem[wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= data_in_i;
                wr_ptr <= (wr_ptr == FIFO_DEPTH - 1) ? 0 : wr_ptr + 1;
                count <= count + 1;
            end
            
            if (rd_en_i && !empty_o) begin
                rd_ptr <= (rd_ptr == FIFO_DEPTH - 1) ? 0 : rd_ptr + 1;
                count <= count - 1;
            end
        end
    end
    
    // Read operation
    assign data_out_o = fifo_mem[rd_ptr[$clog2(FIFO_DEPTH)-1:0]];

endmodule : fifo_sync 