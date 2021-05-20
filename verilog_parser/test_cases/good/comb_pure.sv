module comb_pure(input logic clk,
                 input logic[3:0] inp,
                 output logic[3:0] a);

always_comb
  a = 4'd1 + inp;

endmodule
