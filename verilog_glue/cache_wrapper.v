`timescale 1ns / 1ps

module cache_wrapper(
    input clk,
    
    input[2:0] command,
    output ready,
    
    input[31:0] data_addr,
    input[31:0] inst_addr,
    
    input[31:0] data_wdata,
    input[3:0] data_wstrb,
    
    output[31:0] data_rdata,
    output[31:0] inst_rdata,
    
    output[1:0] error,
    
    //
    // AXI memory (data port)
    //
    (* X_INTERFACE_PARAMETER = "PROTOCOL AXI3" *)
    output mem_d_awvalid,
    input mem_d_awready,
    output[31:0] mem_d_awaddr,
    output[7:0] mem_d_awlen,
    output[2:0] mem_d_awsize,
    output[1:0] mem_d_awburst,
    
    output mem_d_wvalid,
    input mem_d_wready,
    output[63:0] mem_d_wdata,
    output[7:0] mem_d_wstrb,
    output mem_d_wlast,
    
    input[1:0] mem_d_bresp,
    input mem_d_bvalid,
    output mem_d_bready,
    
    output mem_d_arvalid,
    input mem_d_arready,
    output[31:0] mem_d_araddr,
    output[7:0] mem_d_arlen,
    output[2:0] mem_d_arsize,
    output[1:0] mem_d_arburst,
    
    input[63:0] mem_d_rdata,
    input[1:0] mem_d_rresp,
    input mem_d_rlast,
    input mem_d_rvalid,
    output mem_d_rready,
    
    //
    // AXI memory (instruction port)
    //
    (* X_INTERFACE_PARAMETER = "PROTOCOL AXI3" *)
    output mem_i_awvalid,
    input mem_i_awready,
    output[31:0] mem_i_awaddr,
    output[7:0] mem_i_awlen,
    output[2:0] mem_i_awsize,
    output[1:0] mem_i_awburst,
    
    output mem_i_wvalid,
    input mem_i_wready,
    output[63:0] mem_i_wdata,
    output[7:0] mem_i_wstrb,
    output mem_i_wlast,
    
    input[1:0] mem_i_bresp,
    input mem_i_bvalid,
    output mem_i_bready,
    
    output mem_i_arvalid,
    input mem_i_arready,
    output[31:0] mem_i_araddr,
    output[7:0] mem_i_arlen,
    output[2:0] mem_i_arsize,
    output[1:0] mem_i_arburst,
    
    input[63:0] mem_i_rdata,
    input[1:0] mem_i_rresp,
    input mem_i_rlast,
    input mem_i_rvalid,
    output mem_i_rready);

/*
wire[31:0] connection_mem_d_awaddr;
wire[31:0] connection_mem_d_araddr;
wire[31:0] connection_mem_i_awaddr;
wire[31:0] connection_mem_i_araddr;
*/

cache cache(
    .clk(clk),
    .command(command),
    .ready(ready),
    
    .data_addr(data_addr),
    .inst_addr(inst_addr),
    
    .data_wdata(data_wdata),
    .data_wstrb(data_wstrb),
    
    .data_rdata(data_rdata),
    .inst_rdata(inst_rdata),
    
    .error(error),
    
    .mem_d_awvalid(mem_d_awvalid),
    .mem_d_awready(mem_d_awready),
    .mem_d_awaddr(mem_d_awaddr),
    .mem_d_awlen(mem_d_awlen),
    .mem_d_awsize(mem_d_awsize),
    .mem_d_awburst(mem_d_awburst),
    
    .mem_d_wvalid(mem_d_wvalid),
    .mem_d_wready(mem_d_wready),
    .mem_d_wdata(mem_d_wdata),
    .mem_d_wstrb(mem_d_wstrb),
    .mem_d_wlast(mem_d_wlast),
    
    .mem_d_bresp(mem_d_bresp),
    .mem_d_bvalid(mem_d_bvalid),
    .mem_d_bready(mem_d_bready),
    
    .mem_d_arvalid(mem_d_arvalid),
    .mem_d_arready(mem_d_arready),
    .mem_d_araddr(mem_d_araddr),
    .mem_d_arlen(mem_d_arlen),
    .mem_d_arsize(mem_d_arsize),
    .mem_d_arburst(mem_d_arburst),
    
    .mem_d_rdata(mem_d_rdata),
    .mem_d_rresp(mem_d_rresp),
    .mem_d_rlast(mem_d_rlast),
    .mem_d_rvalid(mem_d_rvalid),
    .mem_d_rready(mem_d_rready),
    
    .mem_i_awvalid(mem_i_awvalid),
    .mem_i_awready(mem_i_awready),
    .mem_i_awaddr(mem_i_awaddr),
    .mem_i_awlen(mem_i_awlen),
    .mem_i_awsize(mem_i_awsize),
    .mem_i_awburst(mem_i_awburst),
    
    .mem_i_wvalid(mem_i_wvalid),
    .mem_i_wready(mem_i_wready),
    .mem_i_wdata(mem_i_wdata),
    .mem_i_wstrb(mem_i_wstrb),
    .mem_i_wlast(mem_i_wlast),
    
    .mem_i_bresp(mem_i_bresp),
    .mem_i_bvalid(mem_i_bvalid),
    .mem_i_bready(mem_i_bready),
    
    .mem_i_arvalid(mem_i_arvalid),
    .mem_i_arready(mem_i_arready),
    .mem_i_araddr(mem_i_araddr),
    .mem_i_arlen(mem_i_arlen),
    .mem_i_arsize(mem_i_arsize),
    .mem_i_arburst(mem_i_arburst),
    
    .mem_i_rdata(mem_i_rdata),
    .mem_i_rresp(mem_i_rresp),
    .mem_i_rlast(mem_i_rlast),
    .mem_i_rvalid(mem_i_rvalid),
    .mem_i_rready(mem_i_rready));

/*
assign mem_d_awaddr = {32'd0, connection_mem_d_awaddr};
assign mem_d_araddr = {32'd0, connection_mem_d_araddr};
assign mem_i_awaddr = {32'd0, connection_mem_i_awaddr};
assign mem_i_araddr = {32'd0, connection_mem_i_araddr};
*/

endmodule
