// Could disallow this since standard says we can complain when
// multiple always_comb blocks write to the same var

module comb_double_write(input logic clk,
                         output logic[3:0] a);

always_comb
 a = 4'b0;

always_comb
 a = 4'b1;

endmodule
