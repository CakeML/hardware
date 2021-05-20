module comb_after_reg(input logic clk,
                      input logic [3:0] inp,
                      output logic [3:0] a = 4'd0);

logic[3:0] b;

always_ff @ (posedge clk)
  a <= b;

always_comb
  b = a + inp;

endmodule
