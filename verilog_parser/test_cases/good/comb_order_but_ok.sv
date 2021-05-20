module comb_order_but_ok(input logic clk,
                         input logic[3:0] inp0,
                         input logic[3:0] inp1,
                         output logic[3:0] a,
                         output logic[3:0] b);

always_comb begin
 a = inp0;
 b = a + 4'd1;
 a = inp1;
end

endmodule
