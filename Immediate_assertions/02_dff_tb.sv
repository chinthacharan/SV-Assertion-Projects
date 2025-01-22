module test(
    input logic clk,
    input logic y, ybar,
    output logic d,
    output logic rstn
);

    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars;
    end

    initial begin
        repeat(5) begin
            @(posedge clk);
            void'(std::randomize(d));
            void'(std::randomize(rstn));
        end
        @(posedge clk) $finish;
    end

endmodule

module top;
    logic clk;
    logic rstn;
    logic d;
    logic y, ybar;

    test test1 (.*);
    dff dut (.*);

    initial begin
        clk <= 0;
    end
    always #10 clk <= ~clk;
    
endmodule