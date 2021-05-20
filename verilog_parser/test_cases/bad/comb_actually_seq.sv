`define expected_error CombError

module comb_actually_seq(input logic clk,
                         output logic[3:0] a);

always_comb
 a = a + 4'b1;

endmodule
