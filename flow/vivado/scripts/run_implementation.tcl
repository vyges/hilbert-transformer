#==============================================================================
# TCL Script: Run Implementation for Hilbert Transformer IP
#==============================================================================
# Description: Runs implementation with proper configuration and generates reports
#
# Usage: vivado -mode batch -source run_implementation.tcl -tclargs <project_file> <impl_run> <strategy> <results_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set impl_run [lindex $argv 1]
set strategy [lindex $argv 2]
set results_dir [lindex $argv 3]

# Open project
open_project $project_file

# Set implementation strategy
set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]
set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]
set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]

# Configure implementation settings
set_property STEPS.OPT_DESIGN.ARGS.FANOUT_LIMIT 10000 [get_runs $impl_run]
set_property STEPS.OPT_DESIGN.ARGS.BUFG 12 [get_runs $impl_run]
set_property STEPS.OPT_DESIGN.ARGS.RETIMING true [get_runs $impl_run]

set_property STEPS.PLACE_DESIGN.ARGS.CONSTRAINTS_FILE {} [get_runs $impl_run]
set_property STEPS.PLACE_DESIGN.ARGS.INCREMENTAL false [get_runs $impl_run]

set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]
set_property STEPS.ROUTE_DESIGN.ARGS.TDR_VIOLATION_VERBOSE true [get_runs $impl_run]

set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE $strategy [get_runs $impl_run]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.PLACEMENT true [get_runs $impl_run]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.ROUTING true [get_runs $impl_run]

# Run implementation
puts "Starting implementation with strategy: $strategy"
launch_runs $impl_run
wait_on_run $impl_run

# Check implementation status
if {[get_property PROGRESS [get_runs $impl_run]] == "100%"} {
    puts "Implementation completed successfully"
    
    # Generate implementation reports
    open_run $impl_run -name impl_1
    
    # Resource utilization report
    report_utilization -file $results_dir/utilization_impl.rpt
    puts "Resource utilization report: $results_dir/utilization_impl.rpt"
    
    # Timing summary report
    report_timing_summary -file $results_dir/timing_impl.rpt
    puts "Timing summary report: $results_dir/timing_impl.rpt"
    
    # Power analysis report
    report_power -file $results_dir/power_impl.rpt
    puts "Power analysis report: $results_dir/power_impl.rpt"
    
    # DRC report
    report_drc -file $results_dir/drc_impl.rpt
    puts "DRC report: $results_dir/drc_impl.rpt"
    
    # Route status report
    report_route_status -file $results_dir/route_status.rpt
    puts "Route status report: $results_dir/route_status.rpt"
    
    # Clock utilization report
    report_clock_utilization -file $results_dir/clock_utilization.rpt
    puts "Clock utilization report: $results_dir/clock_utilization.rpt"
    
    # Create completion marker
    set completion_file "$results_dir/impl_complete.rpt"
    set fp [open $completion_file w]
    puts $fp "Implementation completed successfully"
    puts $fp "Strategy: $strategy"
    puts $fp "Timestamp: [clock format [clock seconds]]"
    close $fp
    
    puts "Implementation completion marker: $completion_file"
    
} else {
    puts "Implementation failed"
    
    # Generate error report
    set error_file "$results_dir/implementation_errors.rpt"
    set fp [open $error_file w]
    puts $fp "Implementation failed"
    puts $fp "Strategy: $strategy"
    puts $fp "Timestamp: [clock format [clock seconds]]"
    puts $fp ""
    puts $fp "Error messages:"
    
    # Get implementation log
    set log_file "[get_property DIRECTORY [get_runs $impl_run]]/runme.log"
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
    
    error "Implementation failed - see $error_file for details"
}

puts "Implementation run completed" 