#==============================================================================
# TCL Script: Generate Timing Report for Hilbert Transformer IP
#==============================================================================
# Description: Generates comprehensive timing reports and analysis
#
# Usage: vivado -mode batch -source generate_timing_report.tcl -tclargs <project_file> <impl_run> <reports_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set impl_run [lindex $argv 1]
set reports_dir [lindex $argv 2]

# Open project
open_project $project_file

# Open implementation run
open_run $impl_run -name impl_1

# Generate timing summary report
puts "Generating timing summary report..."
report_timing_summary -file $reports_dir/timing_summary.rpt
puts "Timing summary report: $reports_dir/timing_summary.rpt"

# Generate detailed timing report
puts "Generating detailed timing report..."
report_timing -from [all_registers] -to [all_registers] -file $reports_dir/timing_detailed.rpt
puts "Detailed timing report: $reports_dir/timing_detailed.rpt"

# Generate critical path report
puts "Generating critical path report..."
report_timing -from [all_registers] -to [all_registers] -max_paths 10 -file $reports_dir/timing_critical.rpt
puts "Critical path report: $reports_dir/timing_critical.rpt"

# Generate setup timing report
puts "Generating setup timing report..."
report_timing -from [all_registers] -to [all_registers] -setup -file $reports_dir/timing_setup.rpt
puts "Setup timing report: $reports_dir/timing_setup.rpt"

# Generate hold timing report
puts "Generating hold timing report..."
report_timing -from [all_registers] -to [all_registers] -hold -file $reports_dir/timing_hold.rpt
puts "Hold timing report: $reports_dir/timing_hold.rpt"

# Generate clock-to-output timing report
puts "Generating clock-to-output timing report..."
report_timing -from [all_registers] -to [all_outputs] -file $reports_dir/timing_clock_to_output.rpt
puts "Clock-to-output timing report: $reports_dir/timing_clock_to_output.rpt"

# Generate input-to-clock timing report
puts "Generating input-to-clock timing report..."
report_timing -from [all_inputs] -to [all_registers] -file $reports_dir/timing_input_to_clock.rpt
puts "Input-to-clock timing report: $reports_dir/timing_input_to_clock.rpt"

# Generate timing constraints report
puts "Generating timing constraints report..."
report_timing_constraints -file $reports_dir/timing_constraints.rpt
puts "Timing constraints report: $reports_dir/timing_constraints.rpt"

# Generate clock utilization report
puts "Generating clock utilization report..."
report_clock_utilization -file $reports_dir/clock_utilization.rpt
puts "Clock utilization report: $reports_dir/clock_utilization.rpt"

# Generate clock interaction report
puts "Generating clock interaction report..."
report_clock_interaction -file $reports_dir/clock_interaction.rpt
puts "Clock interaction report: $reports_dir/clock_interaction.rpt"

# Generate timing summary for specific paths
puts "Generating specific path timing reports..."

# AXI-Stream interface timing
report_timing -from [get_pins */tdata_i_reg*/C] -to [get_pins */hilbert_delay_line_inst/*/D] -file $reports_dir/timing_axi_input.rpt
puts "AXI-Stream input timing report: $reports_dir/timing_axi_input.rpt"

report_timing -from [get_pins */hilbert_adder_tree_inst/*/S] -to [get_pins */tdata_o_reg*/D] -file $reports_dir/timing_axi_output.rpt
puts "AXI-Stream output timing report: $reports_dir/timing_axi_output.rpt"

# Pipeline timing
report_timing -from [get_pins */hilbert_coefficient_rom_inst/*/C] -to [get_pins */hilbert_multiplier_array_inst/*/A] -file $reports_dir/timing_pipeline_coeff.rpt
puts "Pipeline coefficient timing report: $reports_dir/timing_pipeline_coeff.rpt"

report_timing -from [get_pins */hilbert_delay_line_inst/*/Q] -to [get_pins */hilbert_multiplier_array_inst/*/B] -file $reports_dir/timing_pipeline_data.rpt
puts "Pipeline data timing report: $reports_dir/timing_pipeline_data.rpt"

report_timing -from [get_pins */hilbert_multiplier_array_inst/*/P] -to [get_pins */hilbert_adder_tree_inst/*/A] -file $reports_dir/timing_pipeline_mult.rpt
puts "Pipeline multiplier timing report: $reports_dir/timing_pipeline_mult.rpt"

# Generate timing summary
set summary_file "$reports_dir/timing_summary.txt"
set fp [open $summary_file w]
puts $fp "Timing Analysis Summary"
puts $fp "======================"
puts $fp "Project: $project_file"
puts $fp "Implementation Run: $impl_run"
puts $fp "Timestamp: [clock format [clock seconds]]"
puts $fp ""
puts $fp "Reports Generated:"
puts $fp "- Timing Summary: timing_summary.rpt"
puts $fp "- Detailed Timing: timing_detailed.rpt"
puts $fp "- Critical Paths: timing_critical.rpt"
puts $fp "- Setup Timing: timing_setup.rpt"
puts $fp "- Hold Timing: timing_hold.rpt"
puts $fp "- Clock-to-Output: timing_clock_to_output.rpt"
puts $fp "- Input-to-Clock: timing_input_to_clock.rpt"
puts $fp "- Timing Constraints: timing_constraints.rpt"
puts $fp "- Clock Utilization: clock_utilization.rpt"
puts $fp "- Clock Interaction: clock_interaction.rpt"
puts $fp "- AXI-Stream Input: timing_axi_input.rpt"
puts $fp "- AXI-Stream Output: timing_axi_output.rpt"
puts $fp "- Pipeline Coefficient: timing_pipeline_coeff.rpt"
puts $fp "- Pipeline Data: timing_pipeline_data.rpt"
puts $fp "- Pipeline Multiplier: timing_pipeline_mult.rpt"
puts $fp ""
puts $fp "Timing Analysis completed successfully"

close $fp
puts "Timing analysis summary: $summary_file"

puts "Timing analysis completed successfully"
puts "Reports directory: $reports_dir" 