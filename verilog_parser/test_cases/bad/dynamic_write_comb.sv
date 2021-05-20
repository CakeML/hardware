`define expected_error CombError

module dynamic_write_comb(input logic clk,
                          input logic[5:0] sel,
                          output logic[3:0] a);

always_comb
 a[sel] = 1'b1;

endmodule
