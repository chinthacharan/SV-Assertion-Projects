module tb;
    reg am = 0;
    reg bm = 0;

    wire a, b;

    assign a = am;
    assign b = bm;
    //In Immediate assertion it won't wait for b to update it automatically runs when a value is assigned causing error

    initial begin
        am = 1;
        bm = 1;
        #10;
        am = 0;
        bm = 1;
        #10;
        am = 1;
        bm = 0;
        #10;
    end

    always_comb begin
        A1 : assert (a == b) $info("a and b are equal at %0t", $time); //this will throw an error as it is SIA
        //A2: assert #0 (a==b) $info("a and b are equal at %0t", $time); //this is observed Deferred Immediate and shows correct response
        //A3: assert final (a == b) $info("a and b are equal at %0t", $time); //this is final deferred Immediate (gives correct response) 
        else begin
            $error("Assertion failed at %0t" $time);
        end
    end
endmodule
