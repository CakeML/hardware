`timescale 1ns / 1ps

module processor_wrapper(
  input clk,
  input [1:0] data_in,
  output [31:0] inst_addr,
  output [9:0] data_out,
  output [1:0] command,
  output [31:0] data_addr,
  output [31:0] data_wdata,
  output [3:0] data_wstrb,
  input mem_start_ready,
  input [31:0] mem_start,
  input interrupt_ack,
  input [1:0] error,
  input ready,
  input [31:0] data_rdata,
  input [31:0] inst_rdata);

wire[31:0] PC;
wire[31:0] data_addr_wire;

processor processor(.clk(clk),
          .data_in(data_in),
          .PC(PC),
          .data_out(data_out),
          .command(command),
          .data_addr(data_addr_wire),
          .data_wdata(data_wdata),
          .data_wstrb(data_wstrb),
          .mem_start_ready(mem_start_ready),
          .mem_start_input(mem_start),
          .interrupt_ack(interrupt_ack),
          .error(error),
          .ready(ready),
          .data_rdata(data_rdata),
          .inst_rdata(inst_rdata));

// Part of is_mem in formalization
assign inst_addr = {PC[31:2], 2'b0};
assign data_addr = {data_addr_wire[31:2], 2'b0};

endmodule
