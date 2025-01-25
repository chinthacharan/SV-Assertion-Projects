module assert_fifo(
    input logic clk, rst, wr, rd,
    input logic [7:0] din, 
    input logic [7:0] dout,
    input logic empty, full
);

     // (1) status of full and empty when rst asserted
  
  ////check on edge
    RST_1: assert property (@(posedge clk) $rose(rst) |-> (full == 1'b0 && empty == 1'b1));

    //check on level
    RST_2: assert property (@(posedge clk) rst |-> (full = 1'b0 && empty == 1'b1));

     //  (2) operation of full and empty flag

    FULL_1: assert property (@(posedge clk) disable iff(rst) $rose(full) |=> (FIFO.wptr == 0)[*1:$] ##1 !full);

    FULL_2: assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 15) |-> full);

    EMPTY_1: assert property (@(posedge clk) disable iff(rst) $rose(empty) |=> (FIFO.rptr == 0)[*1:$] ##1 !empty);

    EMPTY_2: assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 0) |-> empty);

    /// (3) read while empty
    READ_EMPTY: assert property (@(posedge clk) disable iff(rst) empty |-> !rd);

    WRITE_FULL: assert property (@(posedge clk) disable iff(rst) full |-> !wr);


      ////////////// (5) Write+Read pointer behavior with rd and wr signal
 
      
      //////if wr high and full is low, wptr must incr
    WPTR1: assert property (@(posedge clk) (!rst && wr && !full) |=> $changed(FIFO.wptr));

    WPTR2: assert property (@(posedge clk) (!rst && wr!) |=> $stable(FIFO.wptr));

    WPTR3: assert property (@(posedge clk) (!rst && rd) |=> $stable(FIFO.wptr));

    RPTR1: assert property (@(posedge clk) (!rst && rd && !empty) |=> $changed(FIFO.rptr));
    RPTR2: assert property (@(posedge clk) (!rst && !rd) |=> $stable(FIFO.rptr));
    RPTR3: assert property (@(posedge clk) (!rst && wr) |=> $stable(FIFO.rptr));

    always@(posedge clk) begin
        assert(!isunknown(dout));
        assert(!isunknown(rst));
        assert(!isunknown(wr));
        assert(!isunknown(rd));
        assert(!isunknown(din));
    end

    ///(7) Data must match
    //we are checking whether the pointer in read and write are same location

    property p1;
        integer waddr;
        logic [7:0] data;

        (wr, waddr = tb.i, data = din) |-> ##[1:30] rd ##0 (waddr == tb.i - 1)
    endproperty

    assert property (@(posedge clk) disable iff(rst) p1);
endmodule

module tb;
    logic clk = 0, rst = 0, wr = 0, rd = 0;
    logic [7:0] din = 0;
    logic [7:0] dout;
    logic empty, full;
    logic start = 0;

    initial begin
        #2;
        start = 1;
        #10;
        start = 0;
      end
      
      
      reg temp = 0;
      initial begin
        #292;
        temp = 1;
        #10;
        temp = 0;
      end

      FIFO dut (.*);
      bind FIFO assert_fifo (.*);

      always #5 clk = ~clk;

      task write();
        for(int i = 0; i < 15; i++) begin
            din = $urandom();
            wr = 1'b1;
            rd = 1'b0;
            @(posedge clk);
        end
      endtask

      task read();
        for(int i = 0; i < 15; i++) begin
            wr = 1'b0;
            rd = 1'b1;
            @(posedge clk);
        end
    endtask

    initial begin
        @(posedge clk) {rst,wr,rd} = 3'b100;
        @(posedge clk) {rst,wr,rd} = 3'b101;
        @(posedge clk) {rst,wr,rd} = 3'b110;
        @(posedge clk) {rst,wr,rd} = 3'b111;
        @(posedge clk) {rst,wr,rd} = 3'b000; 
        
        write();

        @(posedge clk) {rst,wr,rd} = 3'b010;
        @(posedge clk){rst,wr,rd} = 3'b001;
        
        read();
        
      end

      initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
        $assertvacuousoff(0);
        #500;
        $finish();
      end
    endmodule