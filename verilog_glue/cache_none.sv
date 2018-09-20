`timescale 1ns / 1ps

module cache_none(
    input clk,

    //
    // Processor interface
    //
    
    // 000 = nothing,
    // 001 = read instruction,
    // 010 = read instruction + read data,
    // 011 = read instruction + write data
    // 100 = clear cache (based on data addr)
    input[2:0] command,
    // ready in AXI-sense, command != 00 && ready => start new transaction
    output ready,
    
    // data and instruction addr input
    input[31:0] data_addr,
    input[31:0] inst_addr,
    
    // (data) write input
    input[31:0] data_wdata,
    input[3:0] data_wstrb, // mask for byte writes
    
    // data and instruction read output
    output logic[31:0] data_rdata,
    output logic[31:0] inst_rdata,
    
    // error reporting, 00 = no error, 01 = AXI error, 10 = internal cache error
    output[1:0] error,
    
    //
    // AXI memory (data port)
    //
    output reg mem_d_awvalid = 0,
    input wire mem_d_awready,
    output reg[31:0] mem_d_awaddr,
    output reg[7:0] mem_d_awlen = 0,
    output reg[2:0] mem_d_awsize = 'b010,
    output reg[1:0] mem_d_awburst = 0,
    
    output reg mem_d_wvalid = 0,
    input wire mem_d_wready,
    output reg[31:0] mem_d_wdata,
    output reg[3:0] mem_d_wstrb,
    output reg mem_d_wlast = 1,
    
    input wire[1:0] mem_d_bresp,
    input wire mem_d_bvalid,
    output reg mem_d_bready = 1,
    
    output reg mem_d_arvalid = 0,
    input wire mem_d_arready,
    output reg[31:0] mem_d_araddr,
    output reg[7:0] mem_d_arlen = 0,
    output reg[2:0] mem_d_arsize = 'b010,
    output reg[1:0] mem_d_arburst = 0,
    
    input wire[31:0] mem_d_rdata,
    input wire[1:0] mem_d_rresp,
    input wire mem_d_rlast,
    input wire mem_d_rvalid,
    output reg mem_d_rready = 1,
    
    //
    // AXI memory (instruction port)
    //
    output reg mem_i_awvalid = 0,
    input wire mem_i_awready,
    output reg[31:0] mem_i_awaddr,
    output reg[7:0] mem_i_awlen = 0,
    output reg[2:0] mem_i_awsize = 'b010,
    output reg[1:0] mem_i_awburst = 0,
    
    output reg mem_i_wvalid = 0,
    input wire mem_i_wready,
    output reg[31:0] mem_i_wdata,
    output reg[3:0] mem_i_wstrb,
    output reg mem_i_wlast = 1,
    
    input wire[1:0] mem_i_bresp,
    input wire mem_i_bvalid,
    output reg mem_i_bready = 1,
    
    output reg mem_i_arvalid = 0,
    input wire mem_i_arready,
    output reg[31:0] mem_i_araddr,
    output reg[7:0] mem_i_arlen = 0,
    output reg[2:0] mem_i_arsize = 'b010,
    output reg[1:0] mem_i_arburst = 0,
    
    input wire[31:0] mem_i_rdata,
    input wire[1:0] mem_i_rresp,
    input wire mem_i_rlast,
    input wire mem_i_rvalid,
    output reg mem_i_rready = 1
    );

typedef enum { INIT, WAITING, ERROR_CACHE, ERROR_AXI } statet;
statet state = INIT;

assign ready = (state == INIT);

logic inst_cycle_ready = 1;
logic data_cycle_ready = 1;

logic wait_error = 0;

logic[1:0] data_write_check = 0;

function logic[1:0] error_func(input statet s);
    case (s)
    ERROR_CACHE: error_func = 2;
    ERROR_AXI:   error_func = 1;
    default:     error_func = 0;
    endcase
endfunction

assign error = error_func(state);

always_ff @ (posedge clk) begin
    case (state)
    INIT: begin
        // Inst read
        if (command == 1 || command == 2 || command == 3 || command == 4) begin
            state <= WAITING;
            
            mem_i_arvalid <= 1;
            mem_i_araddr <= inst_addr;
            
            inst_cycle_ready = 0;
        end
        
        // Data read
        if (command == 2) begin
            // Simplify implementation
            if (inst_addr == data_addr) begin
                state <= ERROR_CACHE;
                mem_i_arvalid <= 0;
            end else begin
                mem_d_arvalid <= 1;
                mem_d_araddr <= data_addr;
                
                data_cycle_ready = 0;
            end
        end
        
        // Data write
        if (command == 3) begin
            // Simplify implementation
            if (inst_addr == data_addr) begin
                state <= ERROR_CACHE;
                mem_i_arvalid <= 0;
            end else begin
                mem_d_awvalid <= 1;
                mem_d_awaddr <= data_addr;
            
                mem_d_wvalid <= 1;
                mem_d_wdata <= data_wdata;
                mem_d_wstrb <= data_wstrb;
    
                data_cycle_ready = 0;
                data_write_check = 0;
            end
        end
    end
    
    WAITING: begin
        // Inst read
        if (mem_i_arvalid && mem_i_arready)
            mem_i_arvalid <= 0;
        
        if (mem_i_rvalid && mem_i_rready) begin
            inst_rdata <= mem_i_rdata;
            inst_cycle_ready = 1;
            
            if (mem_i_rresp != 0 || mem_i_rlast != 1) begin
                wait_error = 1;    
            end
        end
        
        // Data read
        if (mem_d_arvalid && mem_d_arready)
            mem_d_arvalid <= 0;
        
        if (mem_d_rvalid && mem_d_rready) begin
            data_rdata <= mem_d_rdata;
            data_cycle_ready = 1;
            
            if (mem_d_rresp != 0 || mem_d_rlast != 1) begin
                wait_error = 1;    
            end
        end
        
        // Data write
        if (mem_d_awvalid && mem_d_awready) begin
            mem_d_awvalid <= 0;
            data_write_check += 1; 
        end
            
        if (mem_d_wvalid && mem_d_wready) begin
            mem_d_wvalid <= 0;
            data_write_check += 1; 
        end
        
        if (mem_d_bvalid && mem_d_bready) begin
            data_cycle_ready = 1;
            
            if (mem_d_bresp != 0 || data_write_check != 2)
                wait_error = 1;
        end
        
        // Done?
        if (inst_cycle_ready == 1 && data_cycle_ready == 1) begin
            if (wait_error == 0)
                state <= INIT;
            else
                state <= ERROR_AXI;
        end
        
    end
        
    endcase
end

endmodule

