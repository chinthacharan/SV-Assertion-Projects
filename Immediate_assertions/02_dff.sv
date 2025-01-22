module dff(
    input logic d,
    input logic rstn,
    input logic clk,
    output logic y, ybar
);

    logic temp_y = 0;
    logic temp_ybar = 1;

    always_ff @(posedge clk) begin
        if(rstn) begin
            temp_y <= 1'b0;
            temp_ybar <= 1'b1; 
        end
        else begin
            temp_y <= d;
            temp_ybar <= ~d;
        end
    end

    always @(posedge clk) begin
        A1: assert(temp_y == ~temp_ybar) $info("Success at %0t", $time);
        else $error("Error at %0t", $time);
    end

    assign y = temp_y;
    assign ybar = temp_ybar;
endmodule