module add(
    input logic [7:0] a, b, 
    input logic clk,
    output logic [8:0] sum
);
    always_ff @(posedge clk) begin
        sum <= a + b;
    end
endmodule

interface add_intf();
    logic clk;
    logic [7:0] a;
    logic [7:0] b;
    logic [8:0] sum;
endinterface