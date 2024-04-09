/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    logic [31:0] o_dividend_stage1, o_remainder_stage1, o_quotient_stage1;
    logic [31:0] i_dividend_stage2, i_remainder_stage2, i_quotient_stage2, i_divisor_stage2;
    logic [31:0] ignore;

    divider_16iter divider_stage1 (
        .i_dividend(i_dividend),
        .i_divisor(i_divisor),
        .i_remainder(0),
        .i_quotient(0),
        .o_dividend(o_dividend_stage1),
        .o_remainder(o_remainder_stage1),
        .o_quotient(o_quotient_stage1)
    );

    always @(posedge clk) begin
        if(rst)    begin
            i_dividend_stage2 <= 0;
            i_remainder_stage2 <= 0;
            i_quotient_stage2 <= 0;
            i_divisor_stage2 <= 0;
        end

        else    begin
            i_dividend_stage2 <= o_dividend_stage1;
            i_remainder_stage2 <= o_remainder_stage1;
            i_quotient_stage2 <= o_quotient_stage1;
            i_divisor_stage2 <= i_divisor;
        end
    end

    divider_16iter divider_stage2 (
        .i_dividend(i_dividend_stage2),
        .i_divisor(i_divisor_stage2),
        .i_remainder(i_remainder_stage2),
        .i_quotient(i_quotient_stage2),
        .o_dividend(ignore),
        .o_remainder(o_remainder),
        .o_quotient(o_quotient)
    );

endmodule

module divider_16iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    wire [31:0] dividends[0:16];
    wire [31:0] remainders[0:16];
    wire [31:0] quotients[0:16];

    assign dividends[0] = i_dividend;
    assign remainders[0] = i_remainder; 
    assign quotients[0] = i_quotient;  

    genvar i;
    generate
        for (i = 0; i < 16; i = i + 1) begin : divu_chain
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

    assign o_dividend = dividends[16];
    assign o_remainder = remainders[16];
    assign o_quotient = quotients[16];

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

    // TODO: copy your code from HW2A here
    wire [31:0] tmp_remainder;
    assign tmp_remainder = {i_remainder[30:0], i_dividend[31]};
    wire sub_or_not;
    assign sub_or_not = tmp_remainder >= i_divisor;

    assign o_dividend = i_dividend << 1;
    assign o_remainder = sub_or_not ? tmp_remainder - i_divisor : tmp_remainder;
    assign o_quotient = {i_quotient[30:0], sub_or_not ? 1'b1 : 1'b0};

endmodule
