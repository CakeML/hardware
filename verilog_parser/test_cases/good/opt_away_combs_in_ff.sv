module opt_away_combs_in_ff(input logic clk,
                            input logic[1:0] inp0,
                            input logic inp1,
                            input logic inp2,
                            output logic[1:0] c);

logic[1:0] a;
logic[1:0] b;

always_ff @ (posedge clk) begin
 a = inp0;
 b[0] = inp1;
 b[1] = inp2;
 c <= a + b;
end

endmodule
