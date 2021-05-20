`define expected_error CombError

module comb_partly_comb(input logic clk,
                        input logic inp,
                        output logic [1:0] b = 2'd0);

logic[1:0] a;

// a[0] is not comb, but could allow this since we never read a[0]
always_comb
  a[1] = inp;

always_ff @ (posedge clk)
  b[1] <= a[1];

endmodule
