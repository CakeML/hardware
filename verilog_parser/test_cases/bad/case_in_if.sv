`define expected_error CombError

module case_in_if(input logic clk,
                  input logic inp0,
                  input logic[1:0] inp1,
                  output logic[1:0] a);

// This will fail since the temporary variable introduced for the
// case statement is only assigned in one of the branches of the if-statement
always_comb
 if (inp0)
  case (inp1)
   2'b00: a = 2'b01;
   2'b01: a = 2'b10;
   2'b10: a = 2'b11;
   2'b11: a = 2'b00;
   default: a = 'x;
  endcase
 else
  a = 2'b00;

endmodule
