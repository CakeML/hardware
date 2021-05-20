module dynamic_read_ff(input logic clk,
                       input logic[5:0] sel,
                       output logic[3:0] a,
                       output logic b);

always_ff @ (posedge clk)
 b = a[sel];

endmodule
