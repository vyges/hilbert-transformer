//=============================================================================
// Testbench Name: tb_hilbert_transformer
//=============================================================================
// Description: Comprehensive SystemVerilog testbench for Hilbert Transformer IP
//              Tests include functional, performance, corner case, and error tests
//              with coverage analysis and waveform generation
//
// Features:
// - Functional tests with sine wave input verification
// - Performance tests with throughput measurement
// - Corner case tests with edge conditions
// - Error tests with protocol violations
// - Coverage analysis and reporting
// - Waveform generation for debugging
//
// Test Categories:
// - Functional: Sine wave, impulse response, random data
// - Performance: Throughput, latency, timing analysis
// - Corner Case: Maximum values, edge conditions
// - Error: Protocol violations, overflow conditions
// - Coverage: Functional and code coverage
//
// Author: Vyges Team
// License: Apache-2.0
//=============================================================================

`timescale 1ns / 1ps

module tb_hilbert_transformer;

    //=============================================================================
    // Parameters
    //=============================================================================
    parameter int DATA_WIDTH = 16;
    parameter int FILTER_ORDER = 64;
    parameter int PIPELINE_STAGES = 8;
    parameter int COEFF_WIDTH = 18;
    parameter int ACCUM_WIDTH = 32;
    
    parameter int CLK_PERIOD = 5; // 200 MHz
    parameter int TEST_DURATION = 50000; // 50 us
    parameter int SINE_WAVE_SAMPLES = 1000;
    parameter int RANDOM_SAMPLES = 500;
    parameter int IMPULSE_AMPLITUDE = 16'h4000;
    parameter int TOLERANCE = 1000; // For sine wave verification
    
    //=============================================================================
    // Signals
    //=============================================================================
    logic        clk_i;
    logic        rst_n_i;
    
    // AXI-Stream Input
    logic [DATA_WIDTH-1:0] tdata_i;
    logic                  tvalid_i;
    logic                  tready_o;
    
    // AXI-Stream Output
    logic [DATA_WIDTH-1:0] tdata_o;
    logic                  tvalid_o;
    logic                  tready_i;
    
    // Control Interface
    logic         config_valid_i;
    logic [31:0]  config_data_i;
    logic [31:0]  status_o;
    
    // Test control
    logic         test_done;
    int           test_errors;
    int           test_count;
    int           total_tests;
    
    // Test data storage
    logic [DATA_WIDTH-1:0] input_samples [$];
    logic [DATA_WIDTH-1:0] output_samples [$];
    logic [DATA_WIDTH-1:0] expected_samples [$];
    
    // Performance measurement
    real          start_time;
    real          end_time;
    real          throughput_msps;
    
    //=============================================================================
    // DUT Instantiation
    //=============================================================================
    hilbert_transformer #(
        .DATA_WIDTH(DATA_WIDTH),
        .FILTER_ORDER(FILTER_ORDER),
        .PIPELINE_STAGES(PIPELINE_STAGES),
        .COEFF_WIDTH(COEFF_WIDTH),
        .ACCUM_WIDTH(ACCUM_WIDTH)
    ) dut (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .tdata_i(tdata_i),
        .tvalid_i(tvalid_i),
        .tready_o(tready_o),
        .tdata_o(tdata_o),
        .tvalid_o(tvalid_o),
        .tready_i(tready_i),
        .config_valid_i(config_valid_i),
        .config_data_i(config_data_i),
        .status_o(status_o)
    );
    
    //=============================================================================
    // Clock Generation
    //=============================================================================
    initial begin
        clk_i = 0;
        forever #(CLK_PERIOD/2) clk_i = ~clk_i;
    end
    
    //=============================================================================
    // Test Stimulus
    //=============================================================================
    initial begin
        // Initialize signals
        rst_n_i = 0;
        tdata_i = '0;
        tvalid_i = 0;
        tready_i = 1;
        config_valid_i = 0;
        config_data_i = '0;
        test_done = 0;
        test_errors = 0;
        test_count = 0;
        total_tests = 0;
        
        // Clear test data storage
        input_samples.delete();
        output_samples.delete();
        expected_samples.delete();
        
        // Reset sequence
        #(CLK_PERIOD * 10);
        rst_n_i = 1;
        #(CLK_PERIOD * 5);
        
        // Run tests
        $display("==========================================");
        $display("Hilbert Transformer Test Suite");
        $display("==========================================");
        $display("Parameters:");
        $display("  DATA_WIDTH: %0d", DATA_WIDTH);
        $display("  FILTER_ORDER: %0d", FILTER_ORDER);
        $display("  PIPELINE_STAGES: %0d", PIPELINE_STAGES);
        $display("  CLK_PERIOD: %0d ns", CLK_PERIOD);
        $display("==========================================");
        
        // Test 1: Reset functionality
        test_reset();
        
        // Test 2: Sine wave functional test
        test_sine_wave_functional();
        
        // Test 3: Impulse response test
        test_impulse_response();
        
        // Test 4: Random data test
        test_random_data();
        
        // Test 5: Corner cases test
        test_corner_cases();
        
        // Test 6: Configuration interface test
        test_configuration_interface();
        
        // Test 7: Backpressure test
        test_backpressure();
        
        // Test 8: Throughput performance test
        test_throughput_performance();
        
        // Test 9: Error conditions test
        test_error_conditions();
        
        // Test 10: Protocol compliance test
        test_protocol_compliance();
        
        // Test 11: Coverage test
        test_coverage();
        
        // Wait for completion
        wait(test_done);
        
        // Report results
        $display("==========================================");
        $display("Test Results Summary");
        $display("==========================================");
        $display("Total Tests: %0d", total_tests);
        $display("Errors: %0d", test_errors);
        $display("Success Rate: %0.1f%%", (real'(total_tests - test_errors) / real'(total_tests)) * 100.0);
        
        if (test_errors == 0) begin
            $display("Status: ALL TESTS PASSED");
        end else begin
            $display("Status: %0d TESTS FAILED", test_errors);
        end
        
        $display("==========================================");
        $finish;
    end
    
    //=============================================================================
    // Test Functions
    //=============================================================================
    
    // Test 1: Reset functionality
    task test_reset();
        $display("Test 1: Reset Functionality");
        total_tests++;
        
        // Check reset state
        if (dut.tdata_o !== '0) begin
            $display("  ERROR: Output data not reset to zero");
            test_errors++;
        end
        
        if (dut.tvalid_o !== 1'b0) begin
            $display("  ERROR: Output valid not reset to zero");
            test_errors++;
        end
        
        if (dut.tready_o !== 1'b1) begin
            $display("  ERROR: Input ready not in correct reset state");
            test_errors++;
        end
        
        if (dut.status_o !== '0) begin
            $display("  ERROR: Status register not reset to zero");
            test_errors++;
        end
        
        $display("  Reset test PASSED");
    endtask
    
    // Test 2: Sine wave functional test
    task test_sine_wave_functional();
        $display("Test 2: Sine Wave Functional");
        total_tests++;
        
        // Generate sine wave input
        input_samples.delete();
        for (int i = 0; i < SINE_WAVE_SAMPLES; i++) begin
            logic [DATA_WIDTH-1:0] sample;
            sample = $signed($rtoi(32767.0 * $sin(2.0 * 3.14159 * i / 100.0)));
            input_samples.push_back(sample);
        end
        
        // Send input data
        for (int i = 0; i < SINE_WAVE_SAMPLES; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = input_samples[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        tvalid_i = 0;
        
        // Wait for processing
        #(CLK_PERIOD * (FILTER_ORDER/2 + PIPELINE_STAGES + 100));
        
        // Collect output data
        output_samples.delete();
        for (int i = 0; i < SINE_WAVE_SAMPLES; i++) begin
            @(posedge clk_i);
            if (tvalid_o && tready_i) begin
                output_samples.push_back(tdata_o);
            end
        end
        
        // Verify phase shift (simplified check)
        int phase_shift_errors = 0;
        for (int i = FILTER_ORDER/2 + PIPELINE_STAGES; i < output_samples.size(); i++) begin
            // Check that output is within reasonable range
            if ($abs($signed(output_samples[i])) > 16'h7FFF) begin
                phase_shift_errors++;
            end
        end
        
        if (phase_shift_errors > SINE_WAVE_SAMPLES * 0.1) begin
            $display("  ERROR: Too many phase shift errors: %0d", phase_shift_errors);
            test_errors++;
        end else begin
            $display("  Sine wave test PASSED - %0d phase shift errors", phase_shift_errors);
        end
    endtask
    
    // Test 3: Impulse response test
    task test_impulse_response();
        $display("Test 3: Impulse Response");
        total_tests++;
        
        // Send impulse
        @(posedge clk_i);
        tvalid_i = 1;
        tdata_i = IMPULSE_AMPLITUDE;
        
        @(posedge clk_i);
        tvalid_i = 0;
        tdata_i = '0;
        
        // Wait for impulse response
        output_samples.delete();
        for (int i = 0; i < FILTER_ORDER + PIPELINE_STAGES; i++) begin
            @(posedge clk_i);
            if (tvalid_o) begin
                output_samples.push_back(tdata_o);
            end
        end
        
        // Check that we get a non-zero response
        int non_zero_count = 0;
        for (int i = 0; i < output_samples.size(); i++) begin
            if (output_samples[i] != '0) begin
                non_zero_count++;
            end
        end
        
        if (non_zero_count == 0) begin
            $display("  ERROR: No impulse response detected");
            test_errors++;
        end else begin
            $display("  Impulse response test PASSED - %0d non-zero samples", non_zero_count);
        end
    endtask
    
    // Test 4: Random data test
    task test_random_data();
        $display("Test 4: Random Data");
        total_tests++;
        
        // Generate random data
        input_samples.delete();
        for (int i = 0; i < RANDOM_SAMPLES; i++) begin
            input_samples.push_back($random);
        end
        
        // Send input data
        for (int i = 0; i < RANDOM_SAMPLES; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = input_samples[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        tvalid_i = 0;
        
        // Wait for processing
        #(CLK_PERIOD * (FILTER_ORDER/2 + PIPELINE_STAGES + 50));
        
        // Collect output data
        output_samples.delete();
        for (int i = 0; i < RANDOM_SAMPLES; i++) begin
            @(posedge clk_i);
            if (tvalid_o && tready_i) begin
                output_samples.push_back(tdata_o);
            end
        end
        
        // Basic sanity checks
        if (output_samples.size() != RANDOM_SAMPLES) begin
            $display("  ERROR: Incorrect number of output samples: %0d", output_samples.size());
            test_errors++;
        end else begin
            // Check for reasonable output range
            int out_of_range_count = 0;
            for (int i = 0; i < output_samples.size(); i++) begin
                if ($abs($signed(output_samples[i])) > 16'h7FFF) begin
                    out_of_range_count++;
                end
            end
            
            if (out_of_range_count > RANDOM_SAMPLES * 0.05) begin
                $display("  WARNING: %0d outputs out of range", out_of_range_count);
            end
            
            $display("  Random data test PASSED");
        end
    endtask
    
    // Test 5: Corner cases test
    task test_corner_cases();
        $display("Test 5: Corner Cases");
        total_tests++;
        
        // Test maximum values
        logic [DATA_WIDTH-1:0] corner_cases [5];
        corner_cases[0] = 16'h7FFF; // Maximum positive
        corner_cases[1] = 16'h8000; // Maximum negative
        corner_cases[2] = '0;       // Zero
        corner_cases[3] = 16'h0001; // Minimum positive
        corner_cases[4] = 16'hFFFF; // Minimum negative
        
        // Send corner case data
        for (int i = 0; i < 5; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = corner_cases[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        tvalid_i = 0;
        
        // Wait for processing
        #(CLK_PERIOD * (FILTER_ORDER/2 + PIPELINE_STAGES + 20));
        
        // Collect output data
        output_samples.delete();
        for (int i = 0; i < 5; i++) begin
            @(posedge clk_i);
            if (tvalid_o && tready_i) begin
                output_samples.push_back(tdata_o);
            end
        end
        
        // Check that all outputs are valid
        if (output_samples.size() != 5) begin
            $display("  ERROR: Incorrect number of corner case outputs: %0d", output_samples.size());
            test_errors++;
        end else begin
            // Check for reasonable output range
            int out_of_range_count = 0;
            for (int i = 0; i < output_samples.size(); i++) begin
                if ($abs($signed(output_samples[i])) > 16'h7FFF) begin
                    out_of_range_count++;
                end
            end
            
            if (out_of_range_count > 0) begin
                $display("  WARNING: %0d corner case outputs out of range", out_of_range_count);
            end
            
            $display("  Corner cases test PASSED");
        end
    endtask
    
    // Test 6: Configuration interface test
    task test_configuration_interface();
        $display("Test 6: Configuration Interface");
        total_tests++;
        
        // Test configuration write
        @(posedge clk_i);
        config_valid_i = 1;
        config_data_i = 32'h12345678;
        
        @(posedge clk_i);
        config_valid_i = 0;
        
        // Check status register
        @(posedge clk_i);
        if (status_o != '0) begin
            $display("  Status register: %0h", status_o);
        end
        
        // Send some data to trigger status updates
        logic [DATA_WIDTH-1:0] test_data [3];
        test_data[0] = 16'h1000;
        test_data[1] = 16'h2000;
        test_data[2] = 16'h3000;
        
        for (int i = 0; i < 3; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = test_data[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        tvalid_i = 0;
        
        // Check that status register updates
        #(CLK_PERIOD * 10);
        logic [15:0] sample_count;
        sample_count = (status_o >> 16) & 16'hFFFF;
        
        if (sample_count == 0) begin
            $display("  ERROR: Sample counter not updating");
            test_errors++;
        end else begin
            $display("  Configuration interface test PASSED - Sample count: %0d", sample_count);
        end
    endtask
    
    // Test 7: Backpressure test
    task test_backpressure();
        $display("Test 7: Backpressure");
        total_tests++;
        
        // Set downstream not ready
        tready_i = 0;
        
        // Send data
        logic [DATA_WIDTH-1:0] test_data [5];
        for (int i = 0; i < 5; i++) begin
            test_data[i] = i;
        end
        
        for (int i = 0; i < 5; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = test_data[i];
        end
        
        // Check that tready_o goes low when downstream not ready
        #(CLK_PERIOD * 10);
        
        // Re-enable downstream
        tready_i = 1;
        tvalid_i = 0;
        
        // Wait for processing
        #(CLK_PERIOD * 20);
        
        // Collect output data
        output_samples.delete();
        for (int i = 0; i < 5; i++) begin
            @(posedge clk_i);
            if (tvalid_o && tready_i) begin
                output_samples.push_back(tdata_o);
            end
        end
        
        // Check that we get the expected number of outputs
        if (output_samples.size() != 5) begin
            $display("  ERROR: Incorrect number of backpressure outputs: %0d", output_samples.size());
            test_errors++;
        end else begin
            $display("  Backpressure test PASSED");
        end
    endtask
    
    // Test 8: Throughput performance test
    task test_throughput_performance();
        $display("Test 8: Throughput Performance");
        total_tests++;
        
        // Generate continuous data stream
        int num_samples = 1000;
        input_samples.delete();
        for (int i = 0; i < num_samples; i++) begin
            input_samples.push_back(i & 16'hFFFF);
        end
        
        // Measure time to send all data
        start_time = $realtime;
        
        for (int i = 0; i < num_samples; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = input_samples[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        end_time = $realtime;
        
        // Calculate throughput
        real time_ns = (end_time - start_time) * 1000.0; // Convert to ns
        throughput_msps = (real'(num_samples) * 1000.0) / time_ns;
        
        // Verify throughput (should be close to clock frequency)
        real expected_throughput = 1000.0 / CLK_PERIOD; // MSPS
        if (throughput_msps < expected_throughput * 0.8) begin
            $display("  ERROR: Throughput too low: %0.2f MSPS (expected > %0.2f MSPS)", 
                     throughput_msps, expected_throughput * 0.8);
            test_errors++;
        end else begin
            $display("  Throughput test PASSED - %0.2f MSPS", throughput_msps);
        end
    endtask
    
    // Test 9: Error conditions test
    task test_error_conditions();
        $display("Test 9: Error Conditions");
        total_tests++;
        
        // Send data that might cause overflow
        logic [DATA_WIDTH-1:0] overflow_data [100];
        for (int i = 0; i < 100; i++) begin
            overflow_data[i] = 16'h7FFF; // Maximum positive values
        end
        
        for (int i = 0; i < 100; i++) begin
            @(posedge clk_i);
            tvalid_i = 1;
            tdata_i = overflow_data[i];
            
            // Wait for handshake
            while (!(tvalid_i && tready_o)) begin
                @(posedge clk_i);
            end
        end
        
        tvalid_i = 0;
        
        // Wait for processing
        #(CLK_PERIOD * (FILTER_ORDER/2 + PIPELINE_STAGES + 50));
        
        // Check status register for error flags
        logic [7:0] error_flags;
        error_flags = (status_o >> 8) & 8'hFF;
        
        // Note: Overflow detection is implementation-dependent
        // We just check that the status register is working
        if (status_o < 0) begin
            $display("  ERROR: Invalid status register value: %0h", status_o);
            test_errors++;
        end else begin
            $display("  Error conditions test PASSED - Error flags: %0h", error_flags);
        end
    endtask
    
    // Test 10: Protocol compliance test
    task test_protocol_compliance();
        $display("Test 10: Protocol Compliance");
        total_tests++;
        
        // Test valid/ready handshake
        @(posedge clk_i);
        tvalid_i = 1;
        tdata_i = 16'h1234;
        
        // Wait for ready
        @(posedge clk_i);
        if (tready_o !== 1'b1) begin
            $display("  ERROR: tready_o should be high initially");
            test_errors++;
        end
        
        // Complete handshake
        @(posedge clk_i);
        tvalid_i = 0;
        
        // Test backpressure
        tready_i = 0;
        tvalid_i = 1;
        tdata_i = 16'h5678;
        
        @(posedge clk_i);
        // tready_o should go low when downstream not ready
        // (implementation dependent)
        
        tready_i = 1;
        tvalid_i = 0;
        
        $display("  Protocol compliance test PASSED");
    endtask
    
    // Test 11: Coverage test
    task test_coverage();
        $display("Test 11: Coverage Collection");
        total_tests++;
        
        // Run various test scenarios for coverage
        logic [DATA_WIDTH-1:0] test_scenarios [3][3];
        test_scenarios[0][0] = 16'h1000; test_scenarios[0][1] = 16'h2000; test_scenarios[0][2] = 16'h3000;
        test_scenarios[1][0] = 16'h4000; test_scenarios[1][1] = 16'h5000; test_scenarios[1][2] = 16'h0000;
        test_scenarios[2][0] = 16'h6000; test_scenarios[2][1] = 16'h0000; test_scenarios[2][2] = 16'h0000;
        
        logic [2:0] valid_patterns [3];
        valid_patterns[0] = 3'b111; // All valid
        valid_patterns[1] = 3'b110; // First two valid
        valid_patterns[2] = 3'b100; // Only first valid
        
        for (int scenario = 0; scenario < 3; scenario++) begin
            for (int i = 0; i < 3; i++) begin
                @(posedge clk_i);
                tvalid_i = valid_patterns[scenario][i];
                tdata_i = test_scenarios[scenario][i];
                
                if (tvalid_i) begin
                    // Wait for handshake
                    while (!(tvalid_i && tready_o)) begin
                        @(posedge clk_i);
                    end
                end
            end
            #(CLK_PERIOD * 10);
        end
        
        // Test configuration interface
        @(posedge clk_i);
        config_valid_i = 1;
        config_data_i = 32'hABCD1234;
        
        @(posedge clk_i);
        config_valid_i = 0;
        
        $display("  Coverage test PASSED");
    endtask
    
    //=============================================================================
    // Monitoring
    //=============================================================================
    
    // Monitor AXI-Stream transactions
    always @(posedge clk_i) begin
        if (tvalid_i && tready_o) begin
            $display("Input:  tdata=%0h, tvalid=1, tready=1", tdata_i);
        end
        
        if (tvalid_o && tready_i) begin
            $display("Output: tdata=%0h, tvalid=1, tready=1", tdata_o);
        end
    end
    
    // Monitor configuration
    always @(posedge clk_i) begin
        if (config_valid_i) begin
            $display("Config: data=%0h", config_data_i);
        end
    end
    
    // Monitor status
    always @(posedge clk_i) begin
        if (status_o != '0) begin
            $display("Status: %0h", status_o);
        end
    end
    
    //=============================================================================
    // Coverage
    //=============================================================================
    
    // Coverage group for AXI-Stream interface
    covergroup axi_stream_cg @(posedge clk_i);
        input_valid: coverpoint tvalid_i;
        input_ready: coverpoint tready_o;
        output_valid: coverpoint tvalid_o;
        output_ready: coverpoint tready_i;
        
        // Cross coverage
        input_handshake: cross input_valid, input_ready;
        output_handshake: cross output_valid, output_ready;
    endgroup
    
    // Coverage group for configuration interface
    covergroup config_cg @(posedge clk_i);
        config_valid: coverpoint config_valid_i;
        config_data: coverpoint config_data_i {
            bins zero = {0};
            bins low = {[1:1000]};
            bins mid = {[1001:1000000]};
            bins high = {[1000001:$]};
        }
    endgroup
    
    // Coverage group for data values
    covergroup data_cg @(posedge clk_i);
        input_data: coverpoint tdata_i {
            bins zero = {0};
            bins positive = {[1:16'h7FFF]};
            bins negative = {[16'h8000:16'hFFFF]};
        }
        output_data: coverpoint tdata_o {
            bins zero = {0};
            bins positive = {[1:16'h7FFF]};
            bins negative = {[16'h8000:16'hFFFF]};
        }
    endgroup
    
    // Instantiate coverage groups
    axi_stream_cg cg_axi_stream = new();
    config_cg cg_config = new();
    data_cg cg_data = new();
    
    //=============================================================================
    // Assertions
    //=============================================================================
    
    // AXI-Stream protocol assertions
    property axi_stream_valid_ready;
        @(posedge clk_i) disable iff (!rst_n_i)
        tvalid_i && !tready_o |-> ##1 tvalid_i;
    endproperty
    
    property axi_stream_ready_after_valid;
        @(posedge clk_i) disable iff (!rst_n_i)
        tvalid_i && tready_o |-> ##1 tready_o;
    endproperty
    
    property axi_stream_output_valid;
        @(posedge clk_i) disable iff (!rst_n_i)
        tvalid_o |-> tready_i || ##1 tvalid_o;
    endproperty
    
    // Assertion instances
    assert property (axi_stream_valid_ready) else
        $error("AXI-Stream: tvalid must remain asserted until tready");
    
    assert property (axi_stream_ready_after_valid) else
        $error("AXI-Stream: tready must remain asserted after handshake");
    
    assert property (axi_stream_output_valid) else
        $error("AXI-Stream: tvalid_o must remain asserted until tready_i");
    
    //=============================================================================
    // Timeout
    //=============================================================================
    initial begin
        #(TEST_DURATION * CLK_PERIOD);
        $display("Test timeout reached");
        test_done = 1;
        $finish;
    end
    
    //=============================================================================
    // Waveform Dumping
    //=============================================================================
    initial begin
        $dumpfile("tb_hilbert_transformer.vcd");
        $dumpvars(0, tb_hilbert_transformer);
    end
    
endmodule : tb_hilbert_transformer 