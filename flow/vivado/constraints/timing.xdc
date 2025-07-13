#==============================================================================
# Timing Constraints: Hilbert Transformer IP
#==============================================================================
# Description: Detailed timing constraints for the Hilbert Transformer IP
#              including clock domains, setup/hold times, and performance targets
#
# Target Frequency: 200 MHz (5 ns period)
# Clock Domain: Single synchronous domain
# Interface: AXI-Stream with handshake protocol
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

#==============================================================================
# Clock Definitions
#==============================================================================

# Primary system clock
create_clock -period 5.000 -name clk_i -waveform {0.000 2.500} [get_ports clk_i]

# Clock uncertainty for synthesis and implementation
set_clock_uncertainty 0.050 [get_clocks clk_i]

#==============================================================================
# Clock Groups
#==============================================================================

# Single clock domain - no clock domain crossing
set_clock_groups -asynchronous -group [get_clocks clk_i]

#==============================================================================
# Input Timing Constraints
#==============================================================================

# AXI-Stream Input Data
set_input_delay -clock clk_i -max 1.500 [get_ports {tdata_i[*]}]
set_input_delay -clock clk_i -min 0.300 [get_ports {tdata_i[*]}]

# AXI-Stream Input Control
set_input_delay -clock clk_i -max 1.000 [get_ports tvalid_i]
set_input_delay -clock clk_i -min 0.200 [get_ports tvalid_i]

set_input_delay -clock clk_i -max 1.000 [get_ports tready_i]
set_input_delay -clock clk_i -min 0.200 [get_ports tready_i]

# Configuration Interface
set_input_delay -clock clk_i -max 1.000 [get_ports config_valid_i]
set_input_delay -clock clk_i -min 0.200 [get_ports config_valid_i]

set_input_delay -clock clk_i -max 1.500 [get_ports {config_data_i[*]}]
set_input_delay -clock clk_i -min 0.300 [get_ports {config_data_i[*]}]

#==============================================================================
# Output Timing Constraints
#==============================================================================

# AXI-Stream Output Data
set_output_delay -clock clk_i -max 1.500 [get_ports {tdata_o[*]}]
set_output_delay -clock clk_i -min 0.300 [get_ports {tdata_o[*]}]

# AXI-Stream Output Control
set_output_delay -clock clk_i -max 1.000 [get_ports tvalid_o]
set_output_delay -clock clk_i -min 0.200 [get_ports tvalid_o]

set_output_delay -clock clk_i -max 1.000 [get_ports tready_o]
set_output_delay -clock clk_i -min 0.200 [get_ports tready_o]

# Status Interface
set_output_delay -clock clk_i -max 1.500 [get_ports {status_o[*]}]
set_output_delay -clock clk_i -min 0.300 [get_ports {status_o[*]}]

#==============================================================================
# False Paths
#==============================================================================

# Configuration interface can be asynchronous
set_false_path -from [get_ports config_valid_i]
set_false_path -from [get_ports {config_data_i[*]}]

# Status interface can be asynchronous
set_false_path -to [get_ports {status_o[*]}]

# Reset signal
set_false_path -from [get_ports rst_n_i]

#==============================================================================
# Multicycle Paths
#==============================================================================

# Configuration interface can have multiple cycles
set_multicycle_path -setup 2 -from [get_ports config_valid_i]
set_multicycle_path -hold 1 -from [get_ports config_valid_i]

set_multicycle_path -setup 2 -from [get_ports {config_data_i[*]}]
set_multicycle_path -hold 1 -from [get_ports {config_data_i[*]}]

# Status interface can have multiple cycles
set_multicycle_path -setup 2 -to [get_ports {status_o[*]}]
set_multicycle_path -hold 1 -to [get_ports {status_o[*]}]

#==============================================================================
# Maximum Delay Constraints
#==============================================================================

# Critical path constraints
set_max_delay 4.000 -from [all_registers] -to [all_registers]

# Combinational path constraints
set_max_delay 3.000 -from [all_inputs] -to [all_registers]
set_max_delay 3.000 -from [all_registers] -to [all_outputs]

#==============================================================================
# Minimum Delay Constraints
#==============================================================================

# Minimum delay for hold time compliance
set_min_delay 0.100 -from [all_registers] -to [all_registers]

#==============================================================================
# Clock-to-Output Constraints
#==============================================================================

# Clock-to-output delay for outputs
set_clock_to_output_delay -clock clk_i -max 2.000 [get_ports {tdata_o[*]}]
set_clock_to_output_delay -clock clk_i -max 1.500 [get_ports tvalid_o]
set_clock_to_output_delay -clock clk_i -max 1.500 [get_ports tready_o]
set_clock_to_output_delay -clock clk_i -max 2.000 [get_ports {status_o[*]}]

#==============================================================================
# Recovery and Removal Constraints
#==============================================================================

# Reset recovery and removal
set_input_delay -clock clk_i -max 0.500 [get_ports rst_n_i]
set_input_delay -clock clk_i -min 0.100 [get_ports rst_n_i]

#==============================================================================
# Area and Performance Constraints
#==============================================================================

# Maximum fanout
set_max_fanout 10000 [current_design]

# Maximum capacitance
set_max_capacitance 0.100 [current_design]

# Maximum transition time
set_max_transition 0.500 [current_design]

#==============================================================================
# Power Constraints
#==============================================================================

# Power optimization
set_power_opt_design -verbose true

# Operating conditions
set_operating_conditions -grade extended -grade_name commercial

#==============================================================================
# Timing Exceptions
#==============================================================================

# Exclude timing analysis for configuration and status interfaces
set_false_path -from [get_ports config_valid_i] -to [all_registers]
set_false_path -from [get_ports {config_data_i[*]}] -to [all_registers]
set_false_path -from [all_registers] -to [get_ports {status_o[*]}]

# Exclude timing analysis for reset
set_false_path -from [get_ports rst_n_i] -to [all_registers]

#==============================================================================
# Clock Domain Constraints
#==============================================================================

# Ensure single clock domain
set_clock_groups -exclusive -group [get_clocks clk_i]

#==============================================================================
# Performance Targets
#==============================================================================

# Target frequency: 200 MHz
set_property CLOCK_PERIOD 5.000 [get_clocks clk_i]

# Slack targets
set_property SLACK_TARGET 0.100 [get_clocks clk_i]

#==============================================================================
# Advanced Timing Constraints
#==============================================================================

# Pipeline stage timing
set_max_delay 4.500 -from [get_pins */hilbert_coefficient_rom_inst/*/C] -to [get_pins */hilbert_multiplier_array_inst/*/A]
set_max_delay 4.500 -from [get_pins */hilbert_delay_line_inst/*/Q] -to [get_pins */hilbert_multiplier_array_inst/*/B]
set_max_delay 4.500 -from [get_pins */hilbert_multiplier_array_inst/*/P] -to [get_pins */hilbert_adder_tree_inst/*/A]

# Critical path optimization
set_max_delay 4.000 -from [get_pins */hilbert_adder_tree_inst/*/S] -to [get_pins */tdata_o_reg*/D]

#==============================================================================
# Interface Timing
#==============================================================================

# AXI-Stream protocol timing
set_input_delay -clock clk_i -max 1.000 -add_delay [get_ports tvalid_i]
set_input_delay -clock clk_i -max 1.000 -add_delay [get_ports tready_i]

set_output_delay -clock clk_i -max 1.000 -add_delay [get_ports tvalid_o]
set_output_delay -clock clk_i -max 1.000 -add_delay [get_ports tready_o]

#==============================================================================
# Synthesis Timing Constraints
#==============================================================================

# Synthesis timing targets
set_property STEPS.SYNTH_DESIGN.ARGS.MAX_DELAY 4.000 [get_runs synth_1]
set_property STEPS.SYNTH_DESIGN.ARGS.MIN_DELAY 0.100 [get_runs synth_1]

#==============================================================================
# Implementation Timing Constraints
#==============================================================================

# Implementation timing targets
set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1] 