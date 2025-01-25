module FIFO(
    input logic clk, rst, wr, rd,
    input logic [7:0] din, 
    output logic [7:0] dout,
    output logic empty, full
);
    logic [3:0] wptr = 0, rptr = 0, cnt = 0;
    logic [7:0] mem[15:0];
    always_ff @(posedge clk) begin
       if(rst = 1'b1) begin
            cnt <= 0;
            wptr <= 0;
            rptr <= 0;
       end
       else if(wr && !full) begin
            if(cnt < 15) begin
                mem[wptr] <= din;
                wptr <= wptr + 1;
                count <= count + 1;
            end
       end
       else if(rd && !empty) begin
            if(cnt > 0) begin
                dout <= mem[rptr];
                rptr <= rptr + 1;
                count <= count - 1;
            end
        end

        if(wptr == 15) wptr <= 0;
        if(rptr == 15) rptr <= 0;
    end

    assign full = (cnt == 15) ? 1'b1: 1'b0;
    assign empty = (cnt == 0) ? 1'b1: 1'b0;
endmodule