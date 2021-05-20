module comb_before(input logic clk,
                   input logic[3:0] inp,
                   output logic[3:0] b);

logic[3:0] a = 4'd0;

always_ff @ (posedge clk)
  a <= b;

always_comb
  b = inp + a;

endmodule
