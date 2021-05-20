module comb_missing_branch_but_ok(input logic clk,
                                  input logic inp,
                                  output logic[3:0] a);

always_comb begin
 a = 4'd0;

 if (inp)
   a = 4'd2;
end

endmodule
