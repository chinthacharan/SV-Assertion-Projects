module sum_assert (
    input logic [7:0] a, b,
    input logic clk,
    input logic [8:0] sum
);

    SUM_CHECK: assert property (@(posedge clk) $changed(sum) |-> (sum == (a + b)));

    SUM_VALID: assert property (@(posedge clk) !isunknown(sum));
    assert property (@(posedge clk) !isunknown(a))
    assert property (@(posedge clk) !isunknown(a))
endmodule

class transaction;
    randc bit [7:0] a;
    randc bit [7:0] b;
    bit [8:0] sum;
endclass

class generator;

    mailbox mbx; //to communicate between generator and driver
    event done;
    transaction t;

    function new(mailbox mbx);
        this.mbx = mbx;
    endfunction

    task main();
        t = new();
        for(int i = 0; i < 25; i++) begin
           t.randomize();
           mbx.put(t);
           $display("a: %0b, b: %0b", t.a, t.b);
           @(done); 
        end
    endtask
endclass

class driver;
    mailbox mbx;
    transaction t;
    event done;
    virtual add_intf vif;

    function new(mailbox mbx);
        this.mbx = mbx;
    endfunction

    task main();
        t = new();
        forever begin
            mbx.get(t);
            vif.a <= t.a;
            vif.b <= t.b;
            $display("a: %0b, b: %0b", t.a, t.b);
            repeat(2) @(posedge vif.clk); //waiting for 2 clock ticks to settle down the data
            -> done;
        end
    endtask
endclass

class monitor;
    mailbox mbx;
    transaction t;
    virtual add_intf vif;

    function new(mailbox mbx);
        this.mbx = mbx;
    endfunction

    task main();
        t = new();
        forever begin
            repeat(2) @(posedge vif.clk);
            t.a = vif.a;
            t.b = vif.b;
            t.sum = vif.sum;
            mbx.put(t);
            $display("a: %0b, b: %0b", vif.a, vif.b);
        end
    endtask
endclass

class scoreboard;
    mailbox mbx;
    transaction t;
    
    function new(mailbox mbx);
        this.mbx = mbx;
    endfunction

    task main();
        t = new();
        forever begin
            mbx.get(t);
            if(t.sum == t.a + t.b) $display("[SCO]: Test Passed");
            else $display("[SCO]: Test Failed");
        end
    endtask
endclass

class environment;
    generator g;
    driver d;
    monitor m;
    scoreboard s;

    mailbox gdmbx, msmbx;

    virtual add_intf vif;
    event gddone;

    function new(mailbox gdmbx, mailbox msmbx);
        this.gdmbx = gdmbx;
        this.msmbx = msmbx;
        g = new(gdmbx);
        d = new(gdmbx);
        m = new(msmbx);
        s = new(msmbx);
    endfunction

    task main();
        d.vif = vif;
        m.vif = vif;

        g.done = gddone;
        d.done = gddone;

        fork
            g.main();
            d.main();
            m.main();
            s.main();
        join
    endtask
endclass


module tb;
    environment e;
    mailbox gdmbx, msmbx;

    add_intf vif();
    add dut (vif.a, vif.b, vif.sum);

    bind add sum_assert dut2 (vif.a, vif.b, vif.sum);

    initial begin
        gdmbx = new();
        msmbx = new();
        e = new(gdmbx, msmbx);
        e.vif = vif;
        @(posedge vif.clk);
        e.main();
    end

    initial begin
        vif.clk = 0;
    end
    always #5 vif.clk = ~vif.clk;

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
        #500;
        $finish;
    end
endmodule