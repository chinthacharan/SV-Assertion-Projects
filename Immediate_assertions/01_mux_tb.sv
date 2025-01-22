module test(
    input logic y,
    input logic clk,
    output logic [1:0] sel,
    output logic a, b, c, d
);
 
    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars;
    end

    initial begin
        repeat(5) begin
            @(posedge clk);
            void'(std::randomize(a));
            void'(std::randomize(b));
            void'(std::randomize(c));
            void'(std::randomize(d));
            //no need of task check_results as assertions are present
        end
        @(posedge clk) $finish;
    end


endmodule

module top;
    logic clk;
    logic y;
    logic a, b, c, d;
    logic [1:0] sel;

    test test1 (.*);
    mux dut (.*);

    initial begin
        clk <= 0;
    end
    always clk <= ~clk;
endmodule