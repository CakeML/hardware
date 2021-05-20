module comb_after(input logic clk,
                  input logic[3:0] inp,
                  output logic[3:0] b);

logic[3:0] a = 4'd0;

always_ff @ (posedge clk)
  a <= inp;

always_comb
  b = a + inp;

endmodule
