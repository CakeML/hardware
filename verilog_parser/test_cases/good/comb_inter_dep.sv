module comb_inter_dep(input logic clk,
                      output logic[3:0] a = 4'd0);

logic[3:0] b;
logic[3:0] c;

always_comb
  b = 4'd1 + a;

always_comb
  c = 4'd1 + b;

always_ff @ (posedge clk)
  a <= c;

endmodule
