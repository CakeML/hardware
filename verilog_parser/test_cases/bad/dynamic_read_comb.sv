`define expected_error CombError

module dynamic_read_comb(input logic clk,
                         input logic[5:0] sel,
                         output logic[3:0] a,
                         output logic b);

// Does not compile because there's no default branch in the case expression the
// dynamic read is expanded to
always_comb
 b = a[sel];

endmodule
