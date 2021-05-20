`timescale 1ns / 1ps

// Inefficient, at least space-wise, but simple...
// Two lowest bits in addresses are assumed to be 0...

module cache(
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
    output reg[1:0] error = 0,
    
    //
    // AXI memory (data port)
    //
    output reg mem_d_awvalid = 0,
    input wire mem_d_awready,
    output reg[31:0] mem_d_awaddr,
    output reg[7:0] mem_d_awlen = 7,
    output reg[2:0] mem_d_awsize = 'b011,
    output reg[1:0] mem_d_awburst = 1,
    
    output reg mem_d_wvalid = 0,
    input wire mem_d_wready,
    output reg[63:0] mem_d_wdata,
    output reg[7:0] mem_d_wstrb = 'b1111_1111,
    output reg mem_d_wlast = 0,
    
    input wire[1:0] mem_d_bresp,
    input wire mem_d_bvalid,
    output reg mem_d_bready = 1,
    
    output reg mem_d_arvalid = 0,
    input wire mem_d_arready,
    output reg[31:0] mem_d_araddr,
    output reg[7:0] mem_d_arlen = 7,
    output reg[2:0] mem_d_arsize = 'b011,
    output reg[1:0] mem_d_arburst = 1,
    
    input wire[63:0] mem_d_rdata,
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
    output reg[7:0] mem_i_awlen = 7,
    output reg[2:0] mem_i_awsize = 'b011,
    output reg[1:0] mem_i_awburst = 1,
    
    output reg mem_i_wvalid = 0,
    input wire mem_i_wready,
    output reg[63:0] mem_i_wdata,
    output reg[7:0] mem_i_wstrb = 'b1111_1111,
    output reg mem_i_wlast = 0,
    
    input wire[1:0] mem_i_bresp,
    input wire mem_i_bvalid,
    output reg mem_i_bready = 1,
    
    output reg mem_i_arvalid = 0,
    input wire mem_i_arready,
    output reg[31:0] mem_i_araddr,
    output reg[7:0] mem_i_arlen = 7,
    output reg[2:0] mem_i_arsize = 'b011,
    output reg[1:0] mem_i_arburst = 1,
    
    input wire[63:0] mem_i_rdata,
    input wire[1:0] mem_i_rresp,
    input wire mem_i_rlast,
    input wire mem_i_rvalid,
    output reg mem_i_rready = 1
    );

// Sizes
//
// 2^28 bytes in megabytes = 268.4 megabytes
// Blocks are 64 bytes, i.e. 2^6
// Number of blocks are 1024, i.e. 2^10

// Address structure
// NOTE: tag bits are the ms-bits here
typedef struct packed {
  logic[17:0] tag;
  logic[9:0] index;
  logic[3:0] block_offset;
} address;

// BRAM structure
typedef struct packed {
  logic dirty;
  logic active;
  logic[17:0] tag;
  logic[511:0] data;
} cache_block;

// Data BRAM

logic data_dbram_we = 0;
logic[9:0] data_dbram_addr;
cache_block data_dbram_in;
cache_block data_dbram_out;

logic[511:0] data_buffer;

logic[9:0] inst_dbram_addr;
cache_block inst_dbram_out;

cache_bram dbram(.clk(clk), .data_we(data_dbram_we), .data_addr(data_dbram_addr), .data_in(data_dbram_in), .data_out(data_dbram_out),
                 .inst_we(0), .inst_addr(inst_dbram_addr), .inst_in('Z), .inst_out(inst_dbram_out));

// Instruction BRAM

logic data_ibram_we = 0;
logic[9:0] data_ibram_addr;
cache_block data_ibram_in;
cache_block data_ibram_out;

logic[511:0] inst_buffer;

logic inst_ibram_we = 0;
logic[9:0] inst_ibram_addr;
cache_block inst_ibram_in;
cache_block inst_ibram_out;
                 
cache_bram ibram(.clk(clk), .data_we(data_ibram_we), .data_addr(data_ibram_addr), .data_in(data_ibram_in), .data_out(data_ibram_out),
                 .inst_we(inst_ibram_we), .inst_addr(inst_ibram_addr), .inst_in(inst_ibram_in), .inst_out(inst_ibram_out));

// Internal state

enum { INIT, BRAM_WAIT, BRAM_RESP, DRAM_WAIT, ERROR } state = INIT;

typedef enum { BLOCK_NONE, BLOCK_HIT, BLOCK_WRITEBACK, BLOCK_OVERWRITE, BLOCK_IN_DATA_CACHE,
               BLOCK_FLUSH_HIT, BLOCK_FLUSH_MISS, BLOCK_ERROR } block_state;
block_state data_block_state = BLOCK_NONE;
block_state inst_block_state = BLOCK_NONE;

logic[3:0] data_block_written;
logic[3:0] data_block_read;
logic[3:0] inst_block_read;

logic data_block_write_done = 1;
logic data_block_read_done = 1;
logic inst_block_read_done = 1;

assign ready = (state == INIT);

logic[2:0] later_command;

address later_data_addr;
address later_inst_addr;

logic[31:0] later_data_wdata;
logic[3:0] later_data_wstrb;

function block_state data_block_action;
    input[2:0] command;
    input cache_block old_block;
    input address addr;
begin
    if (command == 1)
        data_block_action = BLOCK_HIT; // Might not be a hit, but block never used
    else if (old_block.active) begin
        if (old_block.tag == addr.tag) begin
            if (command == 4)
                data_block_action = BLOCK_FLUSH_HIT;
            else
                data_block_action = BLOCK_HIT;
        end else if (command == 4)
            data_block_action = BLOCK_FLUSH_MISS;
        else if (old_block.dirty)
            data_block_action = BLOCK_WRITEBACK;
        else
            data_block_action = BLOCK_OVERWRITE;
    end else if (command == 4)
        data_block_action = BLOCK_FLUSH_MISS;
    else
        data_block_action = BLOCK_OVERWRITE;
end
endfunction

function block_state inst_block_action;
    input cache_block old_inst_block;
    input cache_block old_data_block;
    input address addr;
begin
    if (old_inst_block.active && old_inst_block.tag == addr.tag)
        inst_block_action = BLOCK_HIT;
    else if (old_data_block.active && old_data_block.tag == addr.tag)
        inst_block_action = BLOCK_IN_DATA_CACHE;
    else
        inst_block_action = BLOCK_OVERWRITE;
end
endfunction

//logic[15:0][31:0] inst_buffer_slice; <-- debug

always_ff @ (posedge clk) begin
    case (state)
    INIT: begin
        data_dbram_we <= 0;
        data_ibram_we <= 0;
        inst_ibram_we <= 0;
        
        if (command != 0) begin
            later_command = command;
            later_data_addr = data_addr;
            later_inst_addr = inst_addr;
            later_data_wdata = data_wdata;
            later_data_wstrb = data_wstrb;
            
            data_dbram_addr <= later_data_addr.index;
            inst_dbram_addr <= later_inst_addr.index;
            
            data_ibram_addr <= later_data_addr.index;
            inst_ibram_addr <= later_inst_addr.index;
            
            // Simplifies implementation for now, know that the CakeML compiler
            // will not generate self-modifying code like this:
            if (later_data_addr.index == later_inst_addr.index
                && later_data_addr.tag == later_inst_addr.tag) begin
                error <= 2;
                state <= ERROR;
            end else
                state <= BRAM_WAIT;
        end
    end
        
    BRAM_WAIT:
        state <= BRAM_RESP;
        
    BRAM_RESP: begin
        data_block_state = data_block_action(later_command, data_dbram_out, later_data_addr);
        inst_block_state = inst_block_action(inst_ibram_out, inst_dbram_out, later_inst_addr);
        
        //
        // Data
        //
        
        // Note that we never reset the dirty bit for cache flushes, because we know that
        // the block will always be dirty in all practical cases in the next flush.
        // (However, we might be cache collisions...)
        
        if (data_block_state == BLOCK_WRITEBACK || data_block_state == BLOCK_FLUSH_HIT) begin
            mem_d_awvalid <= 1;
            mem_d_awaddr <= {data_dbram_out.tag, later_data_addr.index, later_data_addr.block_offset};
        
            mem_d_wvalid <= 1;
            data_block_written = 0;
            mem_d_wdata <= data_dbram_out.data[data_block_written +: 64];
            mem_d_wlast <= 0;
            
            data_block_write_done = 0;
        end
        
        if (data_block_state == BLOCK_WRITEBACK || data_block_state == BLOCK_OVERWRITE) begin
            mem_d_arvalid <= 1;
            mem_d_araddr <= later_data_addr;
            data_block_read = 0;
            
            data_block_read_done = 0;
        end else
            // I.e., correct block present (if command relevant at least)
            data_buffer = data_dbram_out.data;
        
        //
        // Inst
        //
        
        case (inst_block_state)
        BLOCK_HIT:
            inst_buffer = inst_ibram_out.data;
            
        BLOCK_IN_DATA_CACHE: begin
            inst_block_state = BLOCK_HIT;
            inst_buffer = inst_dbram_out.data;
            
            inst_ibram_we <= 1;
            // Dirty tag does not matter
            inst_ibram_in <= {1'b0, 1'b1, later_inst_addr.tag, inst_buffer};
        end
        
        BLOCK_OVERWRITE: begin
            mem_i_arvalid <= 1;
            mem_i_araddr <= later_inst_addr;
            inst_block_read = 0;
        
            inst_block_read_done = 0;
        end
        
        endcase
        
        //
        // State
        //
        
        if ((data_block_state == BLOCK_HIT || data_block_state == BLOCK_FLUSH_MISS) && inst_block_state == BLOCK_HIT)
            state <= INIT;
        else
            state <= DRAM_WAIT;
    end
    
    DRAM_WAIT: begin
        //
        // Data
        //
    
        // Write address
        if (mem_d_awvalid && mem_d_awready)
            mem_d_awvalid <= 0;
        
        // Write transfer
        if (mem_d_wvalid && mem_d_wready) begin
            data_block_written++;
            
            if (data_block_written == 7)
                mem_d_wlast <= 1;
                
            if (data_block_written == 8) begin
                mem_d_wlast <= 0;
                mem_d_wvalid <= 0;
            end else
                mem_d_wdata <= data_dbram_out.data[64*data_block_written +: 64];
        end
        
        // Write response
        if (mem_d_bvalid && mem_d_bready) begin
            data_block_write_done = 1;
            
            if (mem_d_bresp != 0)
                data_block_state = BLOCK_ERROR;
        end
    
        // Read address
        if (mem_d_arvalid && mem_d_arready)
            mem_d_arvalid <= 0;
    
        // Read response
        if (mem_d_rvalid && mem_d_rready) begin
            if (mem_d_rlast)
                data_block_read_done = 1;
                        
            if (mem_d_rresp == 0) begin
                data_buffer[9'd64*data_block_read +: 64] = mem_d_rdata;
                data_block_read++;
            end else
                data_block_state = BLOCK_ERROR;
        end
        
        //
        // Inst
        //
        
        inst_ibram_we <= 0; // In case we had BLOCK_IN_DATA_CACHE in previous state
        
        // Read address
        if (mem_i_arvalid && mem_i_arready)
            mem_i_arvalid <= 0;
    
        // Read response
        if (mem_i_rvalid && mem_i_rready) begin
            if (mem_i_rlast)
                inst_block_read_done = 1;
                        
            if (mem_i_rresp == 0) begin
                inst_buffer[9'd64*inst_block_read +: 64] = mem_i_rdata;
                inst_block_read++;
            end else
                inst_block_state = BLOCK_ERROR;
        end
        
        //
        // Final action...
        //
        
        // Write and read ready?
        if (data_block_write_done && data_block_read_done && inst_block_read_done) begin
            if (data_block_state == BLOCK_ERROR || inst_block_state == BLOCK_ERROR) begin
                error <= 1;
                state <= ERROR;
            end else begin
                //
                // Data
                //
                
                // Write DRAM data to d-cache
                if (data_block_state == BLOCK_WRITEBACK || data_block_state == BLOCK_OVERWRITE) begin             
                    data_dbram_we <= 1;
                    data_dbram_in <= {1'b0, 1'b1, later_data_addr.tag, data_buffer};   
                end
                
                data_block_state = BLOCK_HIT;
                
                //
                // Inst
                //
                if (inst_block_state == BLOCK_OVERWRITE) begin
                    inst_block_state = BLOCK_HIT;
                    
                    inst_ibram_we <= 1;
                    // Dirty tag does not matter for i-cache...
                    inst_ibram_in <= {1'b0, 1'b1, later_inst_addr.tag, inst_buffer};
                end
            end
        end
    end
        
    endcase
    
    if (data_block_state == BLOCK_HIT && inst_block_state == BLOCK_HIT) begin
        //
        // Data
        //
        
        // Is data read?
        if (later_command == 2)
            data_rdata <= data_buffer[9'd8*later_data_addr.block_offset +: 32];
            
        // Is data write?
        if (later_command == 3) begin
            for (logic[2:0] i = 0; i < 4; i = i + 1) begin
                if (later_data_wstrb[i]) begin
                    data_buffer[9'd8*(later_data_addr.block_offset + i) +: 8] = later_data_wdata[i*8 +: 8];
                end
            end
            
            data_dbram_we <= 1;
            data_dbram_in <= {1'b1, 1'b1, later_data_addr.tag, data_buffer};
        
            // Copy d-cache block to i-cache?
            if (data_ibram_out.active && data_ibram_out.tag == later_data_addr.tag) begin
                data_ibram_we <= 1;
                // Dirty tag not relevant for i-cache
                data_ibram_in <= {1'b0, 1'b1, later_data_addr.tag, data_buffer};
            end   
        end
        
        // Is cache flush? <-- Don't need to do anything here...
        //if (later_command == 4) begin
        //    
        //end
        
        //
        // Inst
        //
        //inst_buffer_slice = inst_buffer; <-- debug
        
        // Always update inst_rdata...    
        inst_rdata <= inst_buffer[9'd8*later_inst_addr.block_offset +: 32];    
    
        data_block_state = BLOCK_NONE;
        inst_block_state = BLOCK_NONE;
        state <= INIT;
    end
end

endmodule
