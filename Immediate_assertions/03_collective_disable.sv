module tb;
    logic a;

    initial begin
        $assertoff();
        a = 0;
        #50;
        $asserton();
        a = 1;
        #100;
        $finish;
    end

    always@(*) begin
        A1: assert (a == 1) $info("Success at %0t", $time); else $error("Failure at %0t", $time);
    end

    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars;
    end
endmodule