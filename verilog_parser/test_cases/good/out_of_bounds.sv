module out_of_bounds(input logic clk,
                     output logic[1:0] a2,
                     output logic[1:0] b2);

logic[1:0] a1;
logic[1:0] b1;

always_comb
 if (1'b0)
  a1[5'd8] = 1'b1;

always_ff @ (posedge clk)
 b1[5'd8] <= 1'b1;

always_ff @ (posedge clk) begin
 a2 <= a1;
 b2 <= b1;
end

endmodule
