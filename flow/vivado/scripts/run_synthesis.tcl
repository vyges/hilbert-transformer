#==============================================================================
# TCL Script: Run Synthesis for Hilbert Transformer IP
#==============================================================================
# Description: Runs synthesis with proper configuration and generates reports
#
# Usage: vivado -mode batch -source run_synthesis.tcl -tclargs <project_file> <synth_run> <strategy> <results_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set synth_run [lindex $argv 1]
set strategy [lindex $argv 2]
set results_dir [lindex $argv 3]

# Open project
open_project $project_file

# Set synthesis strategy
set_property STEPS.SYNTH_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $synth_run]

# Configure synthesis settings
set_property STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY none [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.FSM_EXTRACTION one_hot [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.RESOURCE_SHARING off [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.SHREG_MIN_SIZE 3 [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.KEEP_EQUIVALENT_REGISTERS true [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.BUFG 12 [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.FANOUT_LIMIT 10000 [get_runs $synth_run]

# Set synthesis constraints
set_property STEPS.SYNTH_DESIGN.ARGS.MAX_BRAM -1 [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.MAX_DSP -1 [get_runs $synth_run]
set_property STEPS.SYNTH_DESIGN.ARGS.MAX_U RAM -1 [get_runs $synth_run]

# Run synthesis
puts "Starting synthesis with strategy: $strategy"
launch_runs $synth_run
wait_on_run $synth_run

# Check synthesis status
if {[get_property PROGRESS [get_runs $synth_run]] == "100%"} {
    puts "Synthesis completed successfully"
    
    # Generate synthesis reports
    open_run $synth_run -name synth_1
    
    # Resource utilization report
    report_utilization -file $results_dir/utilization_synth.rpt
    puts "Resource utilization report: $results_dir/utilization_synth.rpt"
    
    # Timing summary report
    report_timing_summary -file $results_dir/timing_synth.rpt
    puts "Timing summary report: $results_dir/timing_synth.rpt"
    
    # Power analysis report
    report_power -file $results_dir/power_synth.rpt
    puts "Power analysis report: $results_dir/power_synth.rpt"
    
    # DRC report
    report_drc -file $results_dir/drc_synth.rpt
    puts "DRC report: $results_dir/drc_synth.rpt"
    
    # Create completion marker
    set completion_file "$results_dir/synth_complete.rpt"
    set fp [open $completion_file w]
    puts $fp "Synthesis completed successfully"
    puts $fp "Strategy: $strategy"
    puts $fp "Timestamp: [clock format [clock seconds]]"
    close $fp
    
    puts "Synthesis completion marker: $completion_file"
    
} else {
    puts "Synthesis failed"
    
    # Generate error report
    set error_file "$results_dir/synthesis_errors.rpt"
    set fp [open $error_file w]
    puts $fp "Synthesis failed"
    puts $fp "Strategy: $strategy"
    puts $fp "Timestamp: [clock format [clock seconds]]"
    puts $fp ""
    puts $fp "Error messages:"
    
    # Get synthesis log
    set log_file "[get_property DIRECTORY [get_runs $synth_run]]/runme.log"
    if {[file exists $log_file]} {
        set log_fp [open $log_file r]
        while {[gets $log_fp line] >= 0} {
            if {[string match "*ERROR*" $line] || [string match "*CRITICAL*" $line]} {
                puts $fp $line
            }
        }
        close $log_fp
    }
    
    close $fp
    puts "Error report: $error_file"
    
    error "Synthesis failed - see $error_file for details"
}

puts "Synthesis run completed" 