// with some redundant parentheses and length-1 concatenations removed

// IO explanation:
//
// reg_7 is unused
// reg_8 is the C program
// finish is high when the C program as exited, low otherwise
// ret is the return value of the C program (in this case,
// the result of the computation) when finish is high

module main(reg_7, reg_8, clk, finish, ret);
   input [0:0] reg_7;
   input [0:0] reg_8;
   input [0:0] clk;
   output reg [0:0] finish;
   output reg [31:0] ret;

   always @(posedge clk)
     if (reg_8 == 1'd1)
       state <= 4'd11;
     else
       case (state)
	 4'd8: state <= 3'd7;
	 3'd4: state <= 3'd7;
	 2'd2: state <= 1'd1;
	 4'd10: state <= 4'd9;
	 3'd6: state <= 3'd5;
	 1'd1: state <= 1'd1;
	 4'd9: state <= 4'd8;
	 3'd5: state <= 3'd4;
	 2'd3: state <= 1'd1;
	 4'd11: state <= 4'd10;
	 // replaced <= with non-equality check
	 /*4'd7: state <= !(reg_1 = reg_3) ?
			3'd6 : 2'd3;*/
	 3'd7:
	   if (reg_1 == reg_3)
	     state <= 2'd3;
	   else
	     state <= 3'd6;
	 default: ;
       endcase

   always @(posedge clk)
     case (state)
       4'd8: ;
       3'd4: ;
       2'd2: reg_4 <= 32'd0;
       4'd10: reg_2 <= 32'd0;
       3'd6: reg_2 <= reg_2 + (reg_1 + 32'd0);
       1'd1: begin
	  finish <= 1'd1;
	  ret <= reg_4;
       end
       4'd9: reg_1 <= 32'd0;
       3'd5: reg_1 <= reg_1 + 32'd1;
       2'd3: reg_4 <= reg_2 + 32'd2;
       4'd11: reg_3 <= 32'd5;
       3'd7: ;
       default: ;
     endcase

   reg [31:0] reg_4;
   reg [31:0] reg_2;
   reg [31:0] state;
   reg [31:0] reg_1;
   reg [31:0] reg_3;
endmodule
