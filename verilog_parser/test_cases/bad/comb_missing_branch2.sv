`define expected_error CombError

module comb_missing_branch2(input logic clk,
                            input logic inp,
                            output logic[3:0] a);

// Arguably this should pass, but currently does not
always_comb begin
 if (inp)
   a = 4'd2;

 a = 4'd0;
end

endmodule
