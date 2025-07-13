#==============================================================================
# TCL Script: Add Sources to Vivado Project
#==============================================================================
# Description: Adds RTL source files and constraints to the Vivado project
#
# Usage: vivado -mode batch -source add_sources.tcl -tclargs <project_file> <rtl_sources> <constraints>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set rtl_sources [lindex $argv 1]
set constraints [lindex $argv 2]

# Open project
open_project $project_file

# Add RTL source files
if {[string length $rtl_sources] > 0} {
    set rtl_list [split $rtl_sources " "]
    foreach rtl_file $rtl_list {
        if {[file exists $rtl_file]} {
            add_files -norecurse $rtl_file
            puts "Added RTL file: $rtl_file"
        } else {
            puts "Warning: RTL file not found: $rtl_file"
        }
    }
}

# Add constraint files
if {[string length $constraints] > 0} {
    set constraint_list [split $constraints " "]
    foreach constraint_file $constraint_list {
        if {[file exists $constraint_file]} {
            add_files -fileset constrs_1 -norecurse $constraint_file
            puts "Added constraint file: $constraint_file"
        } else {
            puts "Warning: Constraint file not found: $constraint_file"
        }
    }
}

# Set top module
set_property top hilbert_transformer [current_fileset]
set_property top_file "../../rtl/hilbert_transformer.sv" [current_fileset]

# Update compile order
update_compile_order -fileset sources_1

# Set file properties for SystemVerilog files
set_property file_type SystemVerilog [get_files *.sv]

# Set file properties for constraint files
set_property file_type XDC [get_files *.xdc]

puts "Sources added successfully to project"
puts "Top module: hilbert_transformer"
puts "Top file: ../../rtl/hilbert_transformer.sv" 