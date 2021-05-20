`define expected_error CombError

module comb_intra_cycle(input logic clk,
                        output logic[3:0] a = 4'd0,
                        output logic[3:0] b = 4'd0);

always_comb begin
   a = b + 4'd1;
   b = a + 4'd1;
end

endmodule
