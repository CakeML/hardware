module dynamic_write_ff(input logic clk,
                        input logic[5:0] sel,
                        output logic[3:0] a);

always_ff @ (posedge clk)
 a[sel] <= 1'b1;

endmodule
