`define expected_error CycleError

module comb_inter_cycle(input logic clk,
                        output logic[3:0] a = 4'd0,
                        output logic[3:0] b = 4'd0);

always_comb a = b + 4'd1;

always_comb b = a + 4'd1;

endmodule
