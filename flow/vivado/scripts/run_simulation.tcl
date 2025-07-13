#==============================================================================
# TCL Script: Run Simulation for Hilbert Transformer IP
#==============================================================================
# Description: Runs simulation with proper configuration and generates reports
#
# Usage: vivado -mode batch -source run_simulation.tcl -tclargs <project_file> <sim_run> <sim_time> <results_dir> <waves_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set sim_run [lindex $argv 1]
set sim_time [lindex $argv 2]
set results_dir [lindex $argv 3]
set waves_dir [lindex $argv 4]

# Open project
open_project $project_file

# Set simulation properties
set_property -name "xsim.simulate.runtime" -value $sim_time -objects [get_filesets sim_1]
set_property -name "xsim.simulate.saif_scope" -value "all" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.wdb" -value "true" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.xsim.more_options" -value "-view ../../tb/sv_tb/tb_hilbert_transformer_behav.wcfg" -objects [get_filesets sim_1]

# Add testbench files if not already added
set tb_files [glob ../../tb/sv_tb/*.sv]
foreach tb_file $tb_files {
    if {[lsearch [get_files] $tb_file] == -1} {
        add_files -fileset sim_1 -norecurse $tb_file
        puts "Added testbench file: $tb_file"
    }
}

# Set top module for simulation
set_property top tb_hilbert_transformer [get_filesets sim_1]
set_property top_lib xil_defaultlib [get_filesets sim_1]

# Update compile order
update_compile_order -fileset sim_1

# Run simulation
puts "Starting simulation for $sim_time..."
launch_simulation

# Run simulation
run all

# Generate simulation reports
puts "Generating simulation reports..."

# Waveform file
if {[file exists $waves_dir]} {
    write_vcd -force $waves_dir/simulation.vcd
    puts "Waveform file: $waves_dir/simulation.vcd"
}

# SAIF file for power analysis
write_saif -force $results_dir/simulation.saif
puts "SAIF file: $results_dir/simulation.saif"

# Simulation log
set sim_log "$results_dir/simulation.log"
set fp [open $sim_log w]
puts $fp "Simulation Results"
puts $fp "================="
puts $fp "Project: $project_file"
puts $fp "Simulation Time: $sim_time"
puts $fp "Timestamp: [clock format [clock seconds]]"
puts $fp ""
puts $fp "Test Results:"
puts $fp "============="

# Check for test results in simulation
set test_results [get_objects -filter {TYPE == signal} *test*]
foreach result $test_results {
    set value [get_property VALUE $result]
    puts $fp "$result: $value"
}

close $fp
puts "Simulation log: $sim_log"

# Generate simulation summary
set summary_file "$results_dir/simulation_summary.txt"
set fp [open $summary_file w]
puts $fp "Simulation Summary"
puts $fp "=================="
puts $fp "Project: $project_file"
puts $fp "Simulation Time: $sim_time"
puts $fp "Timestamp: [clock format [clock seconds]]"
puts $fp ""
puts $fp "Files Generated:"
puts $fp "- Waveform: $waves_dir/simulation.vcd"
puts $fp "- SAIF: $results_dir/simulation.saif"
puts $fp "- Log: $results_dir/simulation.log"
puts $fp ""
puts $fp "Simulation completed successfully"

close $fp
puts "Simulation summary: $summary_file"

puts "Simulation completed successfully"
puts "Results directory: $results_dir"
puts "Waveforms directory: $waves_dir" 