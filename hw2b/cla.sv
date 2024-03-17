`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   assign pout = &pin;
   assign gout = gin[3] | (pin[3] & gin[2]) | (pin[3] & pin[2] & gin[1]) | (pin[3] & pin[2] & pin[1] & gin[0]);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (pin[1] & pin[0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (pin[2] & pin[1] & gin[0]) | (pin[2] & pin[1] & pin[0] & cin);

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   wire [1:0] gout_tmp;
   wire [1:0] pout_tmp;
   wire [6:0] cout_tmp;
   wire cout_inter;
   wire cin_tmp;

   assign cin_tmp = 1'b0;

   gp4 gp4_lower(
      .gin(gin[3:0]),
      .pin(pin[3:0]),
      .cin(cin_tmp),
      .gout(gout_tmp[0]),
      .pout(pout_tmp[0]),
      .cout(cout_tmp[2:0])
   );

   gp4 gp4_upper(
      .gin(gin[7:4]),
      .pin(pin[7:4]),
      .cin(cin_tmp),
      .gout(gout_tmp[1]),
      .pout(pout_tmp[1]),
      .cout(cout_tmp[6:4])
   );

   assign pout = &pout_tmp;
   assign gout = gout_tmp[1] | (pout_tmp[1] & gout_tmp[0]);
   assign cout_tmp[3] = gout_tmp[0] | (pout_tmp[0] & cin);

   genvar i, j;
   for(j = 0; j < 2; j++)begin
      for(i = 0; i < 3; i++)begin
         assign cout[j*4+i] = cout_tmp[j*4+i] | ((&pin[j*4+i:j*4]) & ((j == 0) ? cin : cout_tmp[(j-1)*4 + 3]));
      end
   end

   assign cout[3] = cout_tmp[3];

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] gin, pin;
   wire [3:0] gout, pout; 
   wire [30:0] cout, cout_tmp;

   wire cin_tmp;
   assign cin_tmp = 1'b0;

   genvar i, j;
   for(i = 0; i < 32; i++) begin : gp
      gp1 _gp1(.a(a[i]), .b(b[i]), .g(gin[i]), .p(pin[i]));
   end

   for(i = 0; i < 4; i++)begin : gp8_block
      gp8 _gp8(
         .gin(gin[i*8+7:i*8]),
         .pin(pin[i*8+7:i*8]),
         .cin(cin_tmp),
         .gout(gout[i]),
         .pout(pout[i]),
         .cout(cout_tmp[i*8+6:i*8])
         );
   end

   assign cout_tmp[7] = gout[0] | pout[0] & cin;
   assign cout_tmp[15] = (gout[1] | pout[1] & gout[0]) | (&pout[1:0] & cin);
   assign cout_tmp[23] = (gout[2] | pout[2] & gout[1] | &pout[2:1] & gout[0]) | (&pout[2:0] & cin);

   for(i = 0; i < 4; i++)begin
      for(j = 0; j < 7; j++)begin
         assign cout[i*8+j] = cout_tmp[i*8+j] | (&pin[i*8+j : i*8] & ((i == 0) ? cin : cout_tmp[i*8-1]));
      end
   end

   assign cout[7] = cout_tmp[7];
   assign cout[15] = cout_tmp[15];
   assign cout[23] = cout_tmp[23];

   genvar k;
   assign sum[0] = a[0] ^ b[0] ^ cin;
   for(k = 1; k < 32; k++) begin
      assign sum[k] = a[k] ^ b[k] ^ cout[k-1];
   end

endmodule
