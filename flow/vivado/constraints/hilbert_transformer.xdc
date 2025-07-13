#==============================================================================
# XDC Constraints: Hilbert Transformer IP for Arty-A7-35
#==============================================================================
# Description: Pin assignments and physical constraints for the Hilbert Transformer IP
#              targeting the Digilent Arty-A7-35 FPGA board
#
# Board: Digilent Arty-A7-35
# Part: xc7a35ticsg324-1L
# Package: csg324
#
# Author: Vyges Team
# License: Apache-2.0
#==============================================================================

#==============================================================================
# Clock Constraints
#==============================================================================

# System clock (100 MHz from Arty-A7-35)
create_clock -period 10.000 -name clk_i -waveform {0.000 5.000} [get_ports clk_i]

# Clock uncertainty
set_clock_uncertainty 0.100 [get_clocks clk_i]

#==============================================================================
# Pin Assignments
#==============================================================================

# Clock and Reset
set_property PACKAGE_PIN W5 [get_ports clk_i]
set_property IOSTANDARD LVCMOS33 [get_ports clk_i]

set_property PACKAGE_PIN U18 [get_ports rst_n_i]
set_property IOSTANDARD LVCMOS33 [get_ports rst_n_i]

# AXI-Stream Input Interface
set_property PACKAGE_PIN V17 [get_ports {tdata_i[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[0]}]

set_property PACKAGE_PIN V16 [get_ports {tdata_i[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[1]}]

set_property PACKAGE_PIN W16 [get_ports {tdata_i[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[2]}]

set_property PACKAGE_PIN W17 [get_ports {tdata_i[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[3]}]

set_property PACKAGE_PIN W15 [get_ports {tdata_i[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[4]}]

set_property PACKAGE_PIN V15 [get_ports {tdata_i[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[5]}]

set_property PACKAGE_PIN W14 [get_ports {tdata_i[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[6]}]

set_property PACKAGE_PIN W13 [get_ports {tdata_i[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[7]}]

set_property PACKAGE_PIN V12 [get_ports {tdata_i[8]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[8]}]

set_property PACKAGE_PIN V11 [get_ports {tdata_i[9]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[9]}]

set_property PACKAGE_PIN U10 [get_ports {tdata_i[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[10]}]

set_property PACKAGE_PIN U9 [get_ports {tdata_i[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[11]}]

set_property PACKAGE_PIN E3 [get_ports {tdata_i[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[12]}]

set_property PACKAGE_PIN F3 [get_ports {tdata_i[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[13]}]

set_property PACKAGE_PIN G3 [get_ports {tdata_i[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[14]}]

set_property PACKAGE_PIN H3 [get_ports {tdata_i[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[15]}]

set_property PACKAGE_PIN D3 [get_ports {tdata_i[16]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[16]}]

set_property PACKAGE_PIN E2 [get_ports {tdata_i[17]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[17]}]

set_property PACKAGE_PIN F2 [get_ports {tdata_i[18]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[18]}]

set_property PACKAGE_PIN G2 [get_ports {tdata_i[19]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[19]}]

set_property PACKAGE_PIN H2 [get_ports {tdata_i[20]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[20]}]

set_property PACKAGE_PIN C2 [get_ports {tdata_i[21]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[21]}]

set_property PACKAGE_PIN D2 [get_ports {tdata_i[22]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[22]}]

set_property PACKAGE_PIN E1 [get_ports {tdata_i[23]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[23]}]

set_property PACKAGE_PIN F1 [get_ports {tdata_i[24]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[24]}]

set_property PACKAGE_PIN G1 [get_ports {tdata_i[25]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[25]}]

set_property PACKAGE_PIN H1 [get_ports {tdata_i[26]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[26]}]

set_property PACKAGE_PIN C1 [get_ports {tdata_i[27]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[27]}]

set_property PACKAGE_PIN D1 [get_ports {tdata_i[28]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[28]}]

set_property PACKAGE_PIN E0 [get_ports {tdata_i[29]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[29]}]

set_property PACKAGE_PIN F0 [get_ports {tdata_i[30]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[30]}]

set_property PACKAGE_PIN G0 [get_ports {tdata_i[31]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_i[31]}]

set_property PACKAGE_PIN U16 [get_ports tvalid_i]
set_property IOSTANDARD LVCMOS33 [get_ports tvalid_i]

set_property PACKAGE_PIN E19 [get_ports tready_o]
set_property IOSTANDARD LVCMOS33 [get_ports tready_o]

# AXI-Stream Output Interface
set_property PACKAGE_PIN U13 [get_ports {tdata_o[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[0]}]

set_property PACKAGE_PIN V13 [get_ports {tdata_o[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[1]}]

set_property PACKAGE_PIN V14 [get_ports {tdata_o[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[2]}]

set_property PACKAGE_PIN U14 [get_ports {tdata_o[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[3]}]

set_property PACKAGE_PIN U15 [get_ports {tdata_o[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[4]}]

set_property PACKAGE_PIN W13 [get_ports {tdata_o[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[5]}]

set_property PACKAGE_PIN V12 [get_ports {tdata_o[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[6]}]

set_property PACKAGE_PIN V11 [get_ports {tdata_o[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[7]}]

set_property PACKAGE_PIN U10 [get_ports {tdata_o[8]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[8]}]

set_property PACKAGE_PIN U9 [get_ports {tdata_o[9]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[9]}]

set_property PACKAGE_PIN E3 [get_ports {tdata_o[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[10]}]

set_property PACKAGE_PIN F3 [get_ports {tdata_o[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[11]}]

set_property PACKAGE_PIN G3 [get_ports {tdata_o[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[12]}]

set_property PACKAGE_PIN H3 [get_ports {tdata_o[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[13]}]

set_property PACKAGE_PIN D3 [get_ports {tdata_o[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[14]}]

set_property PACKAGE_PIN E2 [get_ports {tdata_o[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[15]}]

set_property PACKAGE_PIN F2 [get_ports {tdata_o[16]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[16]}]

set_property PACKAGE_PIN G2 [get_ports {tdata_o[17]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[17]}]

set_property PACKAGE_PIN H2 [get_ports {tdata_o[18]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[18]}]

set_property PACKAGE_PIN C2 [get_ports {tdata_o[19]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[19]}]

set_property PACKAGE_PIN D2 [get_ports {tdata_o[20]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[20]}]

set_property PACKAGE_PIN E1 [get_ports {tdata_o[21]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[21]}]

set_property PACKAGE_PIN F1 [get_ports {tdata_o[22]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[22]}]

set_property PACKAGE_PIN G1 [get_ports {tdata_o[23]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[23]}]

set_property PACKAGE_PIN H1 [get_ports {tdata_o[24]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[24]}]

set_property PACKAGE_PIN C1 [get_ports {tdata_o[25]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[25]}]

set_property PACKAGE_PIN D1 [get_ports {tdata_o[26]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[26]}]

set_property PACKAGE_PIN E0 [get_ports {tdata_o[27]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[27]}]

set_property PACKAGE_PIN F0 [get_ports {tdata_o[28]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[28]}]

set_property PACKAGE_PIN G0 [get_ports {tdata_o[29]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[29]}]

set_property PACKAGE_PIN H0 [get_ports {tdata_o[30]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[30]}]

set_property PACKAGE_PIN C0 [get_ports {tdata_o[31]}]
set_property IOSTANDARD LVCMOS33 [get_ports {tdata_o[31]}]

set_property PACKAGE_PIN U16 [get_ports tvalid_o]
set_property IOSTANDARD LVCMOS33 [get_ports tvalid_o]

set_property PACKAGE_PIN E19 [get_ports tready_i]
set_property IOSTANDARD LVCMOS33 [get_ports tready_i]

# Control Interface
set_property PACKAGE_PIN U17 [get_ports config_valid_i]
set_property IOSTANDARD LVCMOS33 [get_ports config_valid_i]

set_property PACKAGE_PIN V18 [get_ports {config_data_i[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[0]}]

set_property PACKAGE_PIN U15 [get_ports {config_data_i[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[1]}]

set_property PACKAGE_PIN U14 [get_ports {config_data_i[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[2]}]

set_property PACKAGE_PIN V14 [get_ports {config_data_i[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[3]}]

set_property PACKAGE_PIN V13 [get_ports {config_data_i[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[4]}]

set_property PACKAGE_PIN V12 [get_ports {config_data_i[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[5]}]

set_property PACKAGE_PIN V11 [get_ports {config_data_i[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[6]}]

set_property PACKAGE_PIN V10 [get_ports {config_data_i[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[7]}]

set_property PACKAGE_PIN U9 [get_ports {config_data_i[8]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[8]}]

set_property PACKAGE_PIN U8 [get_ports {config_data_i[9]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[9]}]

set_property PACKAGE_PIN V8 [get_ports {config_data_i[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[10]}]

set_property PACKAGE_PIN U7 [get_ports {config_data_i[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[11]}]

set_property PACKAGE_PIN V7 [get_ports {config_data_i[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[12]}]

set_property PACKAGE_PIN U6 [get_ports {config_data_i[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[13]}]

set_property PACKAGE_PIN V6 [get_ports {config_data_i[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[14]}]

set_property PACKAGE_PIN U5 [get_ports {config_data_i[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[15]}]

set_property PACKAGE_PIN V5 [get_ports {config_data_i[16]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[16]}]

set_property PACKAGE_PIN U4 [get_ports {config_data_i[17]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[17]}]

set_property PACKAGE_PIN V4 [get_ports {config_data_i[18]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[18]}]

set_property PACKAGE_PIN U3 [get_ports {config_data_i[19]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[19]}]

set_property PACKAGE_PIN V3 [get_ports {config_data_i[20]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[20]}]

set_property PACKAGE_PIN U2 [get_ports {config_data_i[21]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[21]}]

set_property PACKAGE_PIN V2 [get_ports {config_data_i[22]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[22]}]

set_property PACKAGE_PIN U1 [get_ports {config_data_i[23]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[23]}]

set_property PACKAGE_PIN V1 [get_ports {config_data_i[24]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[24]}]

set_property PACKAGE_PIN U0 [get_ports {config_data_i[25]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[25]}]

set_property PACKAGE_PIN V0 [get_ports {config_data_i[26]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[26]}]

set_property PACKAGE_PIN U19 [get_ports {config_data_i[27]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[27]}]

set_property PACKAGE_PIN V19 [get_ports {config_data_i[28]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[28]}]

set_property PACKAGE_PIN U20 [get_ports {config_data_i[29]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[29]}]

set_property PACKAGE_PIN V20 [get_ports {config_data_i[30]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[30]}]

set_property PACKAGE_PIN U21 [get_ports {config_data_i[31]}]
set_property IOSTANDARD LVCMOS33 [get_ports {config_data_i[31]}]

# Status Interface
set_property PACKAGE_PIN V21 [get_ports {status_o[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[0]}]

set_property PACKAGE_PIN U22 [get_ports {status_o[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[1]}]

set_property PACKAGE_PIN V22 [get_ports {status_o[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[2]}]

set_property PACKAGE_PIN U23 [get_ports {status_o[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[3]}]

set_property PACKAGE_PIN V23 [get_ports {status_o[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[4]}]

set_property PACKAGE_PIN U24 [get_ports {status_o[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[5]}]

set_property PACKAGE_PIN V24 [get_ports {status_o[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[6]}]

set_property PACKAGE_PIN U25 [get_ports {status_o[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[7]}]

set_property PACKAGE_PIN V25 [get_ports {status_o[8]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[8]}]

set_property PACKAGE_PIN U26 [get_ports {status_o[9]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[9]}]

set_property PACKAGE_PIN V26 [get_ports {status_o[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[10]}]

set_property PACKAGE_PIN U27 [get_ports {status_o[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[11]}]

set_property PACKAGE_PIN V27 [get_ports {status_o[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[12]}]

set_property PACKAGE_PIN U28 [get_ports {status_o[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[13]}]

set_property PACKAGE_PIN V28 [get_ports {status_o[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[14]}]

set_property PACKAGE_PIN U29 [get_ports {status_o[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[15]}]

set_property PACKAGE_PIN V29 [get_ports {status_o[16]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[16]}]

set_property PACKAGE_PIN U30 [get_ports {status_o[17]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[17]}]

set_property PACKAGE_PIN V30 [get_ports {status_o[18]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[18]}]

set_property PACKAGE_PIN U31 [get_ports {status_o[19]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[19]}]

set_property PACKAGE_PIN V31 [get_ports {status_o[20]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[20]}]

set_property PACKAGE_PIN U32 [get_ports {status_o[21]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[21]}]

set_property PACKAGE_PIN V32 [get_ports {status_o[22]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[22]}]

set_property PACKAGE_PIN U33 [get_ports {status_o[23]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[23]}]

set_property PACKAGE_PIN V33 [get_ports {status_o[24]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[24]}]

set_property PACKAGE_PIN U34 [get_ports {status_o[25]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[25]}]

set_property PACKAGE_PIN V34 [get_ports {status_o[26]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[26]}]

set_property PACKAGE_PIN U35 [get_ports {status_o[27]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[27]}]

set_property PACKAGE_PIN V35 [get_ports {status_o[28]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[28]}]

set_property PACKAGE_PIN U36 [get_ports {status_o[29]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[29]}]

set_property PACKAGE_PIN V36 [get_ports {status_o[30]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[30]}]

set_property PACKAGE_PIN U37 [get_ports {status_o[31]}]
set_property IOSTANDARD LVCMOS33 [get_ports {status_o[31]}]

#==============================================================================
# Timing Constraints
#==============================================================================

# Input delay constraints
set_input_delay -clock clk_i -max 2.000 [get_ports {tdata_i[*]}]
set_input_delay -clock clk_i -min 0.500 [get_ports {tdata_i[*]}]

set_input_delay -clock clk_i -max 1.000 [get_ports tvalid_i]
set_input_delay -clock clk_i -min 0.200 [get_ports tvalid_i]

set_input_delay -clock clk_i -max 1.000 [get_ports tready_i]
set_input_delay -clock clk_i -min 0.200 [get_ports tready_i]

set_input_delay -clock clk_i -max 1.000 [get_ports config_valid_i]
set_input_delay -clock clk_i -min 0.200 [get_ports config_valid_i]

set_input_delay -clock clk_i -max 2.000 [get_ports {config_data_i[*]}]
set_input_delay -clock clk_i -min 0.500 [get_ports {config_data_i[*]}]

# Output delay constraints
set_output_delay -clock clk_i -max 2.000 [get_ports {tdata_o[*]}]
set_output_delay -clock clk_i -min 0.500 [get_ports {tdata_o[*]}]

set_output_delay -clock clk_i -max 1.000 [get_ports tvalid_o]
set_output_delay -clock clk_i -min 0.200 [get_ports tvalid_o]

set_output_delay -clock clk_i -max 1.000 [get_ports tready_o]
set_output_delay -clock clk_i -min 0.200 [get_ports tready_o]

set_output_delay -clock clk_i -max 2.000 [get_ports {status_o[*]}]
set_output_delay -clock clk_i -min 0.500 [get_ports {status_o[*]}]

#==============================================================================
# False Paths
#==============================================================================

# Configuration interface can be asynchronous
set_false_path -from [get_ports config_valid_i]
set_false_path -from [get_ports {config_data_i[*]}]

# Status interface can be asynchronous
set_false_path -to [get_ports {status_o[*]}]

#==============================================================================
# Area Constraints
#==============================================================================

# Set maximum fanout
set_max_fanout 10000 [current_design]

# Set maximum delay
set_max_delay 8.000 -from [all_registers] -to [all_registers]

#==============================================================================
# Power Constraints
#==============================================================================

# Set power optimization
set_power_opt_design -verbose true

# Set power constraints
set_operating_conditions -grade extended -grade_name commercial 