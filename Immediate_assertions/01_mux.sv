module mux(
    input logic a, b, c, d,
    input logic [1:0] sel,
    output logic y
);
 
 always_comb begin
    case(sel):
        2'b00: y = a;
        2'b01: y = b;
        2'b10: y = c;
        2'b11: y = d;
    endcase
 end
 
 //adding assert checks (simple immediate assert)
 always@(*) begin
    case(sel):
        2'b00: y_equal_a : assert(y==a) $info(" y is equal to a") else $error(" Y is not equal to a at %0t", $time);
        2'b01: y_equal_b : assert(y==b) $info("y is equal to b") else $error("Y is not equal to b at %0t", $time);
        2'b10: y_equal_c : assert(y == c) $info(" y is equal to c") else $error(" y is not equal to c at %0t", $time);
        2'b11: y_equal_d : assert(y == d) $info(" y is equal to d") else $error(" y is not equal to d at %0t", $time);
    endcase
 end
endmodule