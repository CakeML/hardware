`timescale 1ns / 1ps

module cache_bram (clk, data_we, data_addr, data_in, data_out, inst_we, inst_addr, inst_in, inst_out);

input clk;

input data_we;
input[9:0] data_addr;
input[531:0] data_in;
output reg[531:0] data_out;

input inst_we;
input[9:0] inst_addr;
input[531:0] inst_in;
output reg[531:0] inst_out;

logic[531:0] ram[2**10 - 1:0];

initial begin
  //$readmemb("rams_init_file.data",ram);
  
  for (integer i = 0; i < 2**10; i = i + 1) begin
    ram[i] = 0;
  end
end

always @(posedge clk)
begin
  if (data_we) begin
     ram[data_addr] <= data_in;
  end

  data_out <= ram[data_addr];
end

always @(posedge clk)
begin
  if (inst_we) begin
     ram[inst_addr] <= inst_in;
  end

  inst_out <= ram[inst_addr];
end

endmodule