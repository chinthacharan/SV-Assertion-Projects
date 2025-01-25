module top(
    input logic clk,
    input logic rst,
    input logic din,
    output logic dout
);

    enum bit [2:0] {
        idle = 3'b001,
        s0 = 3'b010,
        s1 = 3'b100
    } state = idle, next_state = idle;

    always_ff begin
        if(rst) state <= IDLE;
        else state <= next_state;
    end

    always_comb begin
        dout = 1'b0;
        next_state = idle;
        case(state)
            idle: begin
                dout = 1'b0;
                next_state = s0;
            end

            s0: begin
                if(din == 1'b1) begin
                    next_state = s1;
                    dout = 1'b0;
                end
                else begin
                    next_state = s0;
                    dout = 1'b0;
                end
            end

            s1: begin
                if(din == 1'b1) begin
                    next_state = s0;
                    dout = 1'b1;
                end
                else begin
                    next_state = s1;
                    dout = 0;
                end
            end

            default: begin
                next_state = idle;
                dout = 0;
            end
        endcase
    end
endmodule