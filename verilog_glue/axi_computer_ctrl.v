`timescale 1ns / 1ps

// NOTE: Not SystemVerilog because not supported by block design tool...

module axi_computer_ctrl
        #(parameter [31:0] BASE_ADDR = 32'h4000_0000) (
        input clk,

        output reg mem_start_ready = 0,
        output reg [31:0] mem_start,

        output reg interrupt_ack = 0,

        //
        // AXI interface
        //
        (* X_INTERFACE_PARAMETER = "PROTOCOL AXI3" *)
        input[11:0] awid,
        input awvalid,
        output reg awready = 1,
        input[31:0] awaddr,
        input[7:0] awlen,
        input[2:0] awsize,
        input[1:0] awburst, // does not matter

        input[11:0] wid,
        input wvalid,
        output reg wready = 0,
        input[31:0] wdata,
        input[3:0] wstrb,
        input wlast,

        output reg [11:0] bid,
        output reg [1:0] bresp,
        output reg bvalid = 0,
        input bready);

reg error = 0;
reg reg_addr;

localparam [31:0] REG_MEM_START_ADDR = BASE_ADDR;
localparam [31:0] REG_INTERRUPT_ACK_ADDR = BASE_ADDR + 4;

always @ (posedge clk) begin
    // Always reset interrupt
    interrupt_ack <= 0;

    // Stage 1
    if (awvalid && awready) begin
        awready <= 0;
        bid <= awid;

        if (awlen == 0 && awsize == 'b010)
            case (awaddr)
            REG_MEM_START_ADDR: begin
                wready <= 1;
                reg_addr = 0;
            end

            REG_INTERRUPT_ACK_ADDR: begin
                wready <= 1;
                reg_addr = 1;
            end

            default:
                error = 1;

            endcase
        else
            error = 1;
    end

    // Stage 2
    if (wvalid && wready) begin
        wready <= 0;

        if (wstrb == 'b1111 && wlast && wid == bid)
            if (reg_addr) begin
                // Ignore actual data...
                interrupt_ack <= 1;
            end else begin
                mem_start <= wdata;
                mem_start_ready <= 1;
            end
        else
            error = 1;

        bvalid <= 1;
        if (error == 0)
            bresp <= 0;
        else
            bresp <= 2;
    end

    // Stage 3
    if (bvalid && bready) begin
        bvalid <= 0;
        
        // Get ready for new round...
        awready <= 1;
        error = 0;
    end
end

endmodule
