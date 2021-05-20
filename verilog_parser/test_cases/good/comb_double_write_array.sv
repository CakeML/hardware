//`define expected_error CombError

// Old note:
// We do variable-level analysis of overlapping writes instead of
// (as the standard says) element-level analysis; hence, this fails!

module comb_double_write_array(input logic clk,
                               output logic[1:0] a);

always_comb
 a[0] = 1'b0;

always_comb
 a[1] = 1'b1;

endmodule
