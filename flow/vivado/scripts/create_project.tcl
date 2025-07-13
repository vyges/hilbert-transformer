#==============================================================================
# TCL Script: Create Vivado Project for Hilbert Transformer IP
#==============================================================================
# Description: Creates a new Vivado project with proper configuration
#              for the Hilbert Transformer IP implementation
#
# Usage: vivado -mode batch -source create_project.tcl -tclargs <project_name> <part> <build_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_name [lindex $argv 0]
set part [lindex $argv 1]
set build_dir [lindex $argv 2]

# Create project
create_project $project_name $build_dir -part $part -force

# Set project properties
set_property board_part digilentinc:arty-a7-35:part0:1.0 [current_project]
set_property target_language Verilog [current_project]
set_property default_lib work [current_project]

# Set project settings
set_property STEPS.SYNTH_DESIGN.TCL.PRE {} [get_runs synth_1]
set_property STEPS.SYNTH_DESIGN.TCL.POST {} [get_runs synth_1]
set_property STEPS.WRITE_BITSTREAM.TCL.PRE {} [get_runs impl_1]
set_property STEPS.WRITE_BITSTREAM.TCL.POST {} [get_runs impl_1]

# Configure synthesis run
set_property STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY none [get_runs synth_1]
set_property STEPS.SYNTH_DESIGN.ARGS.FSM_EXTRACTION one_hot [get_runs synth_1]
set_property STEPS.SYNTH_DESIGN.ARGS.RESOURCE_SHARING off [get_runs synth_1]
set_property STEPS.SYNTH_DESIGN.ARGS.SHREG_MIN_SIZE 3 [get_runs synth_1]

# Configure implementation run
set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs impl_1]

# Set simulation properties
set_property target_simulator XSim [current_project]
set_property compxlib.compiled_library_dir {} [current_project]
set_property top_lib xil_defaultlib [current_fileset -simset]
set_property top_file {} [current_fileset -simset]

# Create simulation run
create_fileset -simset sim_1
set_property top hilbert_transformer [get_filesets sim_1]
set_property top_lib xil_defaultlib [get_filesets sim_1]

# Configure simulation run
set_property -name "xsim.simulate.runtime" -value "1000ns" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.saif_scope" -value "all" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.wdb" -value "true" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.xsim.more_options" -value "-view ../../tb/sv_tb/tb_hilbert_transformer_behav.wcfg" -objects [get_filesets sim_1]

# Set project properties
set_property XPM_LIBRARIES {XPM_CDC XPM_MEMORY XPM_FIFO} [current_project]

# Create IP run
create_ip_run [get_ips]

# Set IP run properties
set_property STEPS.IPX_PACKAGE.TCL.PRE {} [get_runs synth_1]
set_property STEPS.IPX_PACKAGE.TCL.POST {} [get_runs synth_1]

# Update compile order
update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

puts "Project $project_name created successfully in $build_dir"
puts "Part: $part"
puts "Board: Arty-A7-35" 