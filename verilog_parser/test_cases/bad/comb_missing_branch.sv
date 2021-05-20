`define expected_error CombError

module comb_missing_branch(input logic clk,
                           input logic inp,
                           output logic[3:0] a);

always_comb
  if (inp)
    a = 4'd2;

endmodule
