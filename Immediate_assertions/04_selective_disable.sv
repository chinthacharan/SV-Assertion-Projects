///SIA do not support selective assertion
///ODIA + FDIA supoport disable

module tb;
    logic a;
    logic rst;

    initial begin
        rst = 1;
        #50;
        rst = 0;
    end

    initial begin
        a = 0;
        #50;
        a = 1;
    end

    //observed deferred immediate assertion
    always@(*) begin
        A1: assert final (a == 1) $info("Success at %0t", $time); else $error("Failure at %0t", $time);
        if(rst == 1'b1)
         disable A1;
    end

    //implementing in SIA
    always@(*) begin
        if(rst == 1'b0) begin
            A1: assert (a == 1) $info("Success at %0t", $time); else $error("Failure at %0t", $time);
        end
    end

    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars;
    end
endmodule