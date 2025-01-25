module counter(
    input logic clk,
    input logic rst,
    input logic up,
    output reg [3:0] dout
);

    always_ff @(posedge clk, posedge rst) begin
        if(rst == 1'b1)
            dout <= 4'b0;
        else  begin
            if(up) dout <= dout + 1;
            else dout <= dout - 1;
        end
    end
endmodule