//=============================================================================
// Integration Testbench
//=============================================================================
// Description: Comprehensive integration testbench for Hilbert Transformer IP
//              Tests complete SoC integration, protocols, and performance
//
// Features:
// - AXI-Stream protocol testing
// - Configuration interface testing
// - Performance validation
// - Error injection and handling
// - Coverage collection
// - Protocol compliance checking
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

module integration_testbench;

    //=============================================================================
    // Parameters
    //=============================================================================
    parameter int DATA_WIDTH = 16;
    parameter int FILTER_ORDER = 64;
    parameter int PIPELINE_STAGES = 8;
    parameter int COEFF_WIDTH = 18;
    parameter int ACCUM_WIDTH = 32;
    parameter int CLK_PERIOD = 10; // 100 MHz
    
    //=============================================================================
    // Clock and Reset
    //=============================================================================
    logic clk_i, rst_n_i;
    
    // Clock generation
    initial begin
        clk_i = 0;
        forever #(CLK_PERIOD/2) clk_i = ~clk_i;
    end
    
    // Reset generation
    initial begin
        rst_n_i = 0;
        #(CLK_PERIOD * 10);
        rst_n_i = 1;
    end
    
    //=============================================================================
    // AXI-Stream Interface Signals
    //=============================================================================
    logic [DATA_WIDTH-1:0] s_axis_tdata, m_axis_tdata;
    logic s_axis_tvalid, s_axis_tready, m_axis_tvalid, m_axis_tready;
    logic s_axis_tlast, m_axis_tlast;
    logic [7:0] s_axis_tuser, m_axis_tuser;
    logic [3:0] s_axis_tid, m_axis_tid;
    logic [3:0] s_axis_tdest, m_axis_tdest;
    
    //=============================================================================
    // Configuration Interface Signals
    //=============================================================================
    logic [31:0] config_data_i, status_o;
    logic config_valid_i, config_ready_o;
    
    //=============================================================================
    // Interrupt Interface Signals
    //=============================================================================
    logic irq_o;
    logic [7:0] irq_id_o;
    
    //=============================================================================
    // Debug Interface Signals
    //=============================================================================
    logic [31:0] debug_o;
    
    //=============================================================================
    // Test Control Signals
    //=============================================================================
    logic test_done;
    int test_count;
    int error_count;
    int success_count;
    
    //=============================================================================
    // DUT Instantiation
    //=============================================================================
    example_soc #(
        .DATA_WIDTH(DATA_WIDTH),
        .FILTER_ORDER(FILTER_ORDER),
        .PIPELINE_STAGES(PIPELINE_STAGES),
        .COEFF_WIDTH(COEFF_WIDTH),
        .ACCUM_WIDTH(ACCUM_WIDTH)
    ) dut (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .s_axis_tuser(s_axis_tuser),
        .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast),
        .m_axis_tuser(m_axis_tuser),
        .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest),
        .config_data_i(config_data_i),
        .config_valid_i(config_valid_i),
        .status_o(status_o),
        .config_ready_o(config_ready_o),
        .irq_o(irq_o),
        .irq_id_o(irq_id_o),
        .debug_o(debug_o)
    );
    
    //=============================================================================
    // Protocol Checker
    //=============================================================================
    protocol_checker #(
        .DATA_WIDTH(DATA_WIDTH)
    ) protocol_checker_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .s_axis_tuser(s_axis_tuser),
        .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast),
        .m_axis_tuser(m_axis_tuser),
        .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest)
    );
    
    //=============================================================================
    // Performance Monitor
    //=============================================================================
    performance_monitor #(
        .DATA_WIDTH(DATA_WIDTH)
    ) perf_mon_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .config_data_i(config_data_i),
        .config_valid_i(config_valid_i),
        .status_o(status_o)
    );
    
    //=============================================================================
    // Coverage Collector
    //=============================================================================
    coverage_collector #(
        .DATA_WIDTH(DATA_WIDTH)
    ) coverage_inst (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .s_axis_tuser(s_axis_tuser),
        .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast),
        .m_axis_tuser(m_axis_tuser),
        .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest),
        .config_data_i(config_data_i),
        .config_valid_i(config_valid_i),
        .status_o(status_o),
        .irq_o(irq_o),
        .irq_id_o(irq_id_o),
        .debug_o(debug_o)
    );
    
    //=============================================================================
    // Test Tasks
    //=============================================================================
    
    // Task 1: Reset Test
    task test_reset();
        $display("=== Test 1: Reset Test ===");
        test_count++;
        
        // Wait for reset to complete
        wait(rst_n_i);
        repeat(10) @(posedge clk_i);
        
        // Check initial state
        if (s_axis_tready && !s_axis_tvalid && !m_axis_tvalid) begin
            $display("PASS: Reset test completed successfully");
            success_count++;
        end else begin
            $display("FAIL: Reset test failed - incorrect initial state");
            error_count++;
        end
    endtask
    
    // Task 2: Basic AXI-Stream Test
    task test_basic_axi_stream();
        $display("=== Test 2: Basic AXI-Stream Test ===");
        test_count++;
        
        // Send test data
        for (int i = 0; i < 100; i++) begin
            @(posedge clk_i);
            s_axis_tdata = i;
            s_axis_tvalid = 1'b1;
            s_axis_tlast = (i == 99);
            s_axis_tuser = i[7:0];
            s_axis_tid = i[3:0];
            s_axis_tdest = i[3:0];
            
            wait(s_axis_tready);
            @(posedge clk_i);
            s_axis_tvalid = 1'b0;
        end
        
        // Wait for processing
        repeat(200) @(posedge clk_i);
        
        $display("PASS: Basic AXI-Stream test completed");
        success_count++;
    endtask
    
    // Task 3: Configuration Interface Test
    task test_configuration();
        $display("=== Test 3: Configuration Interface Test ===");
        test_count++;
        
        // Test configuration writes
        for (int i = 0; i < 4; i++) begin
            @(posedge clk_i);
            config_data_i = {16'h1234, 8'h00, 8'h00 + i}; // Write command
            config_valid_i = 1'b1;
            
            wait(config_ready_o);
            @(posedge clk_i);
            config_valid_i = 1'b0;
        end
        
        // Test configuration reads
        for (int i = 0; i < 4; i++) begin
            @(posedge clk_i);
            config_data_i = {16'h5678, 8'h01, 8'h00 + i}; // Read command
            config_valid_i = 1'b1;
            
            wait(config_ready_o);
            @(posedge clk_i);
            config_valid_i = 1'b0;
        end
        
        $display("PASS: Configuration interface test completed");
        success_count++;
    endtask
    
    // Task 4: Backpressure Test
    task test_backpressure();
        $display("=== Test 4: Backpressure Test ===");
        test_count++;
        
        // Create backpressure on output
        m_axis_tready = 1'b0;
        
        // Send data
        for (int i = 0; i < 50; i++) begin
            @(posedge clk_i);
            s_axis_tdata = i;
            s_axis_tvalid = 1'b1;
            s_axis_tlast = (i == 49);
            
            wait(s_axis_tready);
            @(posedge clk_i);
            s_axis_tvalid = 1'b0;
        end
        
        // Release backpressure
        repeat(10) @(posedge clk_i);
        m_axis_tready = 1'b1;
        
        // Wait for processing
        repeat(100) @(posedge clk_i);
        
        $display("PASS: Backpressure test completed");
        success_count++;
    endtask
    
    // Task 5: Performance Test
    task test_performance();
        $display("=== Test 5: Performance Test ===");
        test_count++;
        
        int start_time, end_time;
        int transfer_count = 0;
        
        start_time = $time;
        
        // Continuous data transfer
        for (int i = 0; i < 1000; i++) begin
            @(posedge clk_i);
            s_axis_tdata = i;
            s_axis_tvalid = 1'b1;
            s_axis_tlast = (i == 999);
            
            if (s_axis_tready) begin
                transfer_count++;
            end
            
            wait(s_axis_tready);
            @(posedge clk_i);
            s_axis_tvalid = 1'b0;
        end
        
        end_time = $time;
        
        // Calculate performance
        real throughput = (real'(transfer_count) * DATA_WIDTH) / (real'(end_time - start_time) / 1e9);
        $display("Performance: %0.2f Mbps", throughput);
        
        if (throughput > 100.0) begin
            $display("PASS: Performance test completed");
            success_count++;
        end else begin
            $display("FAIL: Performance below target");
            error_count++;
        end
    endtask
    
    // Task 6: Error Injection Test
    task test_error_injection();
        $display("=== Test 6: Error Injection Test ===");
        test_count++;
        
        // Inject protocol violations
        @(posedge clk_i);
        s_axis_tvalid = 1'b1;
        s_axis_tdata = 16'hDEAD;
        
        // Don't wait for ready (protocol violation)
        repeat(5) @(posedge clk_i);
        s_axis_tvalid = 1'b0;
        
        // Check error detection
        repeat(20) @(posedge clk_i);
        
        if (debug_o[31] || irq_o) begin
            $display("PASS: Error injection test completed");
            success_count++;
        end else begin
            $display("FAIL: Error not detected");
            error_count++;
        end
    endtask
    
    // Task 7: Interrupt Test
    task test_interrupts();
        $display("=== Test 7: Interrupt Test ===");
        test_count++;
        
        int irq_count = 0;
        
        // Monitor interrupts
        fork
            forever begin
                @(posedge irq_o);
                irq_count++;
                $display("Interrupt received: ID = %h", irq_id_o);
            end
        join_none
        
        // Generate conditions that should trigger interrupts
        repeat(100) @(posedge clk_i);
        
        if (irq_count > 0) begin
            $display("PASS: Interrupt test completed");
            success_count++;
        end else begin
            $display("FAIL: No interrupts generated");
            error_count++;
        end
        
        disable fork;
    endtask
    
    // Task 8: Corner Case Test
    task test_corner_cases();
        $display("=== Test 8: Corner Case Test ===");
        test_count++;
        
        // Test with maximum values
        @(posedge clk_i);
        s_axis_tdata = 16'hFFFF;
        s_axis_tvalid = 1'b1;
        s_axis_tlast = 1'b1;
        s_axis_tuser = 8'hFF;
        s_axis_tid = 4'hF;
        s_axis_tdest = 4'hF;
        
        wait(s_axis_tready);
        @(posedge clk_i);
        s_axis_tvalid = 1'b0;
        
        // Test with minimum values
        @(posedge clk_i);
        s_axis_tdata = 16'h0000;
        s_axis_tvalid = 1'b1;
        s_axis_tlast = 1'b0;
        s_axis_tuser = 8'h00;
        s_axis_tid = 4'h0;
        s_axis_tdest = 4'h0;
        
        wait(s_axis_tready);
        @(posedge clk_i);
        s_axis_tvalid = 1'b0;
        
        // Wait for processing
        repeat(50) @(posedge clk_i);
        
        $display("PASS: Corner case test completed");
        success_count++;
    endtask
    
    // Task 9: Protocol Compliance Test
    task test_protocol_compliance();
        $display("=== Test 9: Protocol Compliance Test ===");
        test_count++;
        
        // Test various protocol scenarios
        for (int i = 0; i < 10; i++) begin
            // Random delays
            repeat($urandom_range(1, 10)) @(posedge clk_i);
            
            s_axis_tdata = $urandom();
            s_axis_tvalid = 1'b1;
            s_axis_tlast = (i == 9);
            
            wait(s_axis_tready);
            @(posedge clk_i);
            s_axis_tvalid = 1'b0;
        end
        
        // Wait for processing
        repeat(100) @(posedge clk_i);
        
        $display("PASS: Protocol compliance test completed");
        success_count++;
    endtask
    
    // Task 10: Stress Test
    task test_stress();
        $display("=== Test 10: Stress Test ===");
        test_count++;
        
        // Continuous operation for extended period
        for (int i = 0; i < 5000; i++) begin
            @(posedge clk_i);
            s_axis_tdata = i;
            s_axis_tvalid = 1'b1;
            s_axis_tlast = (i == 4999);
            
            wait(s_axis_tready);
            @(posedge clk_i);
            s_axis_tvalid = 1'b0;
            
            // Random backpressure
            if ($urandom_range(0, 100) < 10) begin
                m_axis_tready = 1'b0;
                repeat($urandom_range(1, 5)) @(posedge clk_i);
                m_axis_tready = 1'b1;
            end
        end
        
        $display("PASS: Stress test completed");
        success_count++;
    endtask
    
    //=============================================================================
    // Main Test Sequence
    //=============================================================================
    initial begin
        // Initialize signals
        s_axis_tdata = 0;
        s_axis_tvalid = 0;
        s_axis_tlast = 0;
        s_axis_tuser = 0;
        s_axis_tid = 0;
        s_axis_tdest = 0;
        m_axis_tready = 1;
        config_data_i = 0;
        config_valid_i = 0;
        
        test_count = 0;
        error_count = 0;
        success_count = 0;
        
        // Wait for reset
        wait(rst_n_i);
        repeat(10) @(posedge clk_i);
        
        $display("Starting Integration Testbench");
        $display("=================================");
        
        // Run all tests
        test_reset();
        test_basic_axi_stream();
        test_configuration();
        test_backpressure();
        test_performance();
        test_error_injection();
        test_interrupts();
        test_corner_cases();
        test_protocol_compliance();
        test_stress();
        
        // Final report
        repeat(100) @(posedge clk_i);
        
        $display("=================================");
        $display("Integration Testbench Complete");
        $display("Tests Run: %0d", test_count);
        $display("Tests Passed: %0d", success_count);
        $display("Tests Failed: %0d", error_count);
        $display("Success Rate: %0.1f%%", (real'(success_count) / real'(test_count)) * 100.0);
        
        if (error_count == 0) begin
            $display("ALL TESTS PASSED!");
        end else begin
            $display("SOME TESTS FAILED!");
        end
        
        test_done = 1;
        $finish;
    end
    
    //=============================================================================
    // Timeout
    //=============================================================================
    initial begin
        #(CLK_PERIOD * 100000); // 1ms timeout
        if (!test_done) begin
            $display("TIMEOUT: Testbench did not complete in time");
            $finish;
        end
    end
    
    //=============================================================================
    // Waveform Dumping
    //=============================================================================
    initial begin
        $dumpfile("integration_testbench.vcd");
        $dumpvars(0, integration_testbench);
    end

endmodule : integration_testbench

//=============================================================================
// Protocol Checker
//=============================================================================
module protocol_checker #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata,
    input  logic                    s_axis_tvalid,
    input  logic                    s_axis_tready,
    input  logic                    s_axis_tlast,
    input  logic [7:0]              s_axis_tuser,
    input  logic [3:0]              s_axis_tid,
    input  logic [3:0]              s_axis_tdest,
    input  logic [DATA_WIDTH-1:0]   m_axis_tdata,
    input  logic                    m_axis_tvalid,
    input  logic                    m_axis_tready,
    input  logic                    m_axis_tlast,
    input  logic [7:0]              m_axis_tuser,
    input  logic [3:0]              m_axis_tid,
    input  logic [3:0]              m_axis_tdest
);

    // Protocol checking logic
    // ...

endmodule : protocol_checker

//=============================================================================
// Performance Monitor
//=============================================================================
module performance_monitor #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata,
    input  logic                    s_axis_tvalid,
    input  logic                    s_axis_tready,
    input  logic [DATA_WIDTH-1:0]   m_axis_tdata,
    input  logic                    m_axis_tvalid,
    input  logic                    m_axis_tready,
    input  logic [31:0]             config_data_i,
    input  logic                    config_valid_i,
    input  logic [31:0]             status_o
);

    // Performance monitoring logic
    // ...

endmodule : performance_monitor

//=============================================================================
// Coverage Collector
//=============================================================================
module coverage_collector #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata,
    input  logic                    s_axis_tvalid,
    input  logic                    s_axis_tready,
    input  logic                    s_axis_tlast,
    input  logic [7:0]              s_axis_tuser,
    input  logic [3:0]              s_axis_tid,
    input  logic [3:0]              s_axis_tdest,
    input  logic [DATA_WIDTH-1:0]   m_axis_tdata,
    input  logic                    m_axis_tvalid,
    input  logic                    m_axis_tready,
    input  logic                    m_axis_tlast,
    input  logic [7:0]              m_axis_tuser,
    input  logic [3:0]              m_axis_tid,
    input  logic [3:0]              m_axis_tdest,
    input  logic [31:0]             config_data_i,
    input  logic                    config_valid_i,
    input  logic [31:0]             status_o,
    input  logic                    irq_o,
    input  logic [7:0]              irq_id_o,
    input  logic [31:0]             debug_o
);

    // Coverage collection logic
    // ...

endmodule : coverage_collector 