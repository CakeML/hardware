module comb_array(input logic clk,
                  input logic inp0,
                  input logic inp1,
                  input logic inp2,
                  input logic inp3,
                  output logic[3:0] b);

logic[3:0] a;

always_comb begin
  a[0] = inp0;
  a[1] = inp1;
  a[2] = inp2;
  a[3] = inp3;
  b = a + 4'd1;
end

endmodule
