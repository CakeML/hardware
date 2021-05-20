module case_ff(input logic clk,
               input logic[1:0] inp,
               output logic[3:0] b);

always_ff @ (posedge clk)
 case (inp)
  2'd0: b = 4'd2;
  2'd3: b = 4'd2;
 endcase

endmodule
