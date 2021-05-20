module comb_intra_dep(input logic clk,
                      input logic[3:0] inp,
                      output logic[3:0] b);

logic[3:0] a;

always_comb begin
   a = inp + 4'd1;
   b = a + 4'd1;
end

endmodule
