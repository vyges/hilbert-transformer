#==============================================================================
# TCL Script: Generate Bitstream for Hilbert Transformer IP
#==============================================================================
# Description: Generates bitstream file for FPGA programming
#
# Usage: vivado -mode batch -source generate_bitstream.tcl -tclargs <project_file> <impl_run> <results_dir>
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

# Get command line arguments
set project_file [lindex $argv 0]
set impl_run [lindex $argv 1]
set results_dir [lindex $argv 2]

# Open project
open_project $project_file

# Open implementation run
open_run $impl_run -name impl_1

# Configure bitstream settings
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR Yes [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN Pullup [current_design]
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN Div-1 [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE Yes [current_design]

# Generate bitstream
puts "Generating bitstream..."
write_bitstream -force $results_dir/hilbert_transformer.bit

# Generate memory configuration file
puts "Generating memory configuration file..."
write_cfgmem -force -format bin -interface spix4 -size 16 -loadbit "up 0 $results_dir/hilbert_transformer.bit" $results_dir/hilbert_transformer.bin

# Generate debug probes file
puts "Generating debug probes file..."
write_debug_probes -force $results_dir/hilbert_transformer.ltx

# Generate hardware platform file
puts "Generating hardware platform file..."
write_hw_platform -fixed -force -include_bit -file $results_dir/hilbert_transformer.xsa

# Generate bitstream properties
puts "Generating bitstream properties..."
set bitstream_file "$results_dir/hilbert_transformer.bit"
if {[file exists $bitstream_file]} {
    set fp [open "$results_dir/bitstream_properties.txt" w]
    puts $fp "Bitstream Properties"
    puts $fp "==================="
    puts $fp "File: $bitstream_file"
    puts $fp "Size: [file size $bitstream_file] bytes"
    puts $fp "Generated: [clock format [clock seconds]]"
    puts $fp ""
    puts $fp "Configuration:"
    puts $fp "- SPI Bus Width: 4"
    puts $fp "- Config Rate: 33 MHz"
    puts $fp "- SPI 32-bit Address: Yes"
    puts $fp "- Unused Pins: Pullup"
    puts $fp "- External Master CCLK: Div-1"
    puts $fp "- SPI Fall Edge: Yes"
    close $fp
    
    puts "Bitstream properties: $results_dir/bitstream_properties.txt"
}

puts "Bitstream generation completed successfully"
puts "Bitstream file: $results_dir/hilbert_transformer.bit"
puts "Memory config file: $results_dir/hilbert_transformer.bin"
puts "Debug probes file: $results_dir/hilbert_transformer.ltx"
puts "Hardware platform file: $results_dir/hilbert_transformer.xsa" 