/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    wire [31:0] dividends[0:32];
    wire [31:0] remainders[0:32];
    wire [31:0] quotients[0:32];

    assign dividends[0] = i_dividend;
    assign remainders[0] = 0; 
    assign quotients[0] = 0;  

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : divu_chain
            divu_1iter divu_iter(
                .i_dividend(dividends[i]),
                .i_divisor(i_divisor), 
                .i_remainder(remainders[i]),
                .i_quotient(quotients[i]),
                .o_dividend(dividends[i + 1]), 
                .o_remainder(remainders[i + 1]), 
                .o_quotient(quotients[i + 1])   
            );
        end
    endgenerate

    assign o_remainder = remainders[32];
    assign o_quotient = quotients[32];

endmodule



module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here
    wire [31:0] tmp_remainder = {i_remainder[30:0], i_dividend[31]};
    wire sub_or_not = tmp_remainder >= i_divisor;

    assign o_dividend = i_dividend << 1;
    assign o_remainder = sub_or_not ? tmp_remainder - i_divisor : tmp_remainder;
    assign o_quotient = {i_quotient[30:0], sub_or_not ? 1'b1 : 1'b0};

endmodule
