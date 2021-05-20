module case_overfull(input logic clk,
                     input logic[1:0] sel,
                     input logic[3:0] inp0,
                     input logic[3:0] inp1,
                     input logic[3:0] inp2,
                     input logic[3:0] inp3,
                     output logic[3:0] a);

always_comb
 case (sel)
   2'b00: a = inp0;
   2'b01: a = inp1;
   2'b10: a = inp2;
   2'b11: a = inp3;
   default: a = 'x;
 endcase

endmodule
