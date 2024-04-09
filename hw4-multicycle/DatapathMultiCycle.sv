/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "divider_unsigned_pipelined.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);

  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // wire up the output port with the corresponding register
  assign regs[0] = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  // flip-flops
  always_ff @(posedge clk or posedge rst)  begin
    // in reset condition, set all regs to 0
    if(rst)  begin
      for(int i = 1; i < 32; i++) begin
        regs[i] <= 32'd0;
      end
    end

    // in write enable mode, write the corresponding reg with data
    else if(we)  begin
      if(rd != 5'b0)  begin
        regs[rd] <= rd_data;
      end
    end
  end

endmodule

module DatapathMultiCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on HW3B)
  logic [31:0] new_store_data_to_dmem;
  logic [3:0]  new_store_we_to_dmem;
  logic [31:0] new_addr_to_dmem;

  assign store_data_to_dmem = new_store_data_to_dmem;
  assign store_we_to_dmem = new_store_we_to_dmem;
  assign addr_to_dmem = new_addr_to_dmem;

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  // U - utype intermediate for LUI instructions
  wire [19:0] imm_u; // U-type immediate for LUI instruction
  assign imm_u = insn_from_imem[31:12];

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // Instantiate RegFile and its corresponding signals
  logic [4:0] regfile_rd;
  logic [`REG_SIZE] regfile_rd_data;
  logic [4:0] regfile_rs1, regfile_rs2;
  logic [`REG_SIZE] regfile_rs1_data, regfile_rs2_data;
  logic regfile_we; // Write enable for the RegFile

  // Instantiate the RegFile module and name it 'rf' as expected by the testbench
  RegFile rf (
    .rd(regfile_rd),
    .rd_data(regfile_rd_data),
    .rs1(regfile_rs1),
    .rs1_data(regfile_rs1_data),
    .rs2(regfile_rs2),
    .rs2_data(regfile_rs2_data),
    .clk(clk),
    .we(regfile_we),
    .rst(rst)
  );

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  // `include "RvDisassembler.sv"
  string disasm_string;

  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  logic div_stall_next, div_stall_curr;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
      div_stall_curr <= 1'b0;
    end else begin
      pcCurrent <= pcNext;
      div_stall_curr <= div_stall_next;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  logic illegal_insn;

  // parsing the signal for I-type command 
  wire [11:0] reg_imm12;
  wire [31:0] reg_imm32;

  assign reg_imm12 = insn_from_imem[31:20];
  assign reg_imm32 = {{20{reg_imm12[11]}}, reg_imm12};

  // parsing signal for S-type command
  wire [`REG_SIZE] st_imm32;

  assign st_imm32 = {{20{insn_from_imem[31]}}, insn_from_imem[31:25], insn_from_imem[11:7]};

// parsing immediate for beq
  wire [31:0] branch_imm;
  assign branch_imm = {{20{insn_from_imem[31]}}, insn_from_imem[7], insn_from_imem[30:25], insn_from_imem[11:8], 1'b0};

// parsing immediate for jal
  wire [31:0] jal_imm;
  assign jal_imm = {{12{insn_from_imem[31]}}, insn_from_imem[19:12], insn_from_imem[20], insn_from_imem[30:21], 1'b0};

  // instantiate cla to support sum related insns
  logic [`REG_SIZE] cla_a;
  logic [`REG_SIZE] cla_b;
  logic cla_cin;
  logic [`REG_SIZE] cla_sum;

  // store temporary product
  logic [63:0]  mul_temp;
  logic [63:0]  mul_abs;
  logic [`REG_SIZE] rs1_abs;

  // offset to handle mem addr misalignment
  logic [`REG_SIZE] mem_addr_raw;
  logic [1:0] mem_addr_offset;

  cla _cla(
    .a(cla_a),
    .b(cla_b),
    .cin(cla_cin),
    .sum(cla_sum)
  );

  // instantiate dividor to support divide related insns
  logic [`REG_SIZE] div_dividend;
  logic [`REG_SIZE] div_dividor;
  logic [`REG_SIZE] div_remainder;
  logic [`REG_SIZE] div_quotient;

  logic pos_neg;

  divider_unsigned_pipelined _div(
    .clk(clk),
    .rst(rst),
    .i_dividend(div_dividend),
    .i_divisor(div_dividor),
    .o_remainder(div_remainder),
    .o_quotient(div_quotient)
  );

  always_comb begin
    illegal_insn = 1'b0;

    // init signals for regs
    regfile_rd = insn_rd;
    regfile_rs1 = insn_rs1;
    regfile_rs2 = insn_rs2;
    regfile_rd_data = 32'd0;
    regfile_we = 1'b0;

    // init signals for mem
    new_store_we_to_dmem = 4'b0000;
    new_addr_to_dmem = 32'd0;
    mem_addr_offset = 2'b00;
    mem_addr_raw = 32'd0;

    // init signals for cla
    cla_a = 32'd0;
    cla_b = 32'd0;
    cla_cin = 1'b0;

    // init signals for mult
    mul_temp = 64'd0;
    mul_abs = 64'd0;
    rs1_abs = 32'b0;

    // init signals for div
    div_dividend = 32'b0;
    div_dividor = 32'b0;

    div_stall_next = 1'b0;

    halt = 1'b0;

    if(insn_from_imem[6:0] == 7'h33 && insn_funct3[2] == 1'b1 && insn_funct7 == 7'h1)  begin
      if(div_stall_curr == 1'b0)  begin
        div_stall_next = 1'b1;
        pcNext = pcCurrent;
      end

      else  begin
        div_stall_next = 1'b0;
        pcNext = pcCurrent + 4;
      end
    end
    else  begin
      pcNext = pcCurrent + 4;
    end

    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        regfile_we = 1'b1;
        regfile_rd_data = {imm_u, 12'b0};
      end

      OpAuipc: begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + {imm_u, 12'b0};
      end

      OpJal:  begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + 4;
        pcNext = pcCurrent + jal_imm;
      end

      OpJalr: begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + 4;
        pcNext = (regfile_rs1_data + reg_imm32) & ~32'h1;
      end

      // block for implementing all kinds of I-type instructions
      OpRegImm: begin
        regfile_we = 1'b1;
        // implement addi
        if(insn_funct3 == 3'b000) begin
          cla_a = regfile_rs1_data;
          cla_b = reg_imm32;

          regfile_rd_data = cla_sum;
        end

        // implement slti
        else if(insn_funct3 == 3'b010) begin
          regfile_rd_data = ($signed(regfile_rs1_data) < $signed(reg_imm32)) ? 32'd1 : 32'd0;
        end

        // implement sltiu
        else if(insn_funct3 == 3'b011) begin
          regfile_rd_data = ($unsigned(regfile_rs1_data) < $unsigned(reg_imm32)) ? 32'd1 : 32'd0;
        end

        // implement xori
        else if(insn_funct3 == 3'b100)  begin
          regfile_rd_data = regfile_rs1_data ^ reg_imm32;
        end

        // implement ori
        else if(insn_funct3 == 3'b110)  begin
          regfile_rd_data = regfile_rs1_data | reg_imm32;
        end

        // implement andi
        else if(insn_funct3 == 3'b111)  begin
          regfile_rd_data = regfile_rs1_data & reg_imm32;
        end

        // implement slli
        else if(insn_funct3 == 3'b001 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data << reg_imm12[4:0];
        end

        // implement srli
        else if(insn_funct3 == 3'b101 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data >> reg_imm12[4:0];
        end

        // implement srai
        else if(insn_funct3 == 3'b101 && insn_funct7 == 7'b0100000)  begin
          regfile_rd_data = $signed(regfile_rs1_data) >>> reg_imm12[4:0];
        end

        else  begin
          illegal_insn = 1'b1;
        end
      end

      // block for implementing all kinds of R-type instructions
      OpRegReg: begin
        regfile_we = 1'b1;
        // implement add
        if(insn_funct3 == 3'b000 && insn_funct7 == 7'd0) begin
          // read src from regs
          // calculate sum using cla
          cla_a = regfile_rs1_data;
          cla_b = regfile_rs2_data;

          // write sum into dst
          regfile_rd_data = cla_sum;
        end

        // implement sub
        else if(insn_funct3 == 3'b000 && insn_funct7 == 7'b0100000) begin
          cla_a = regfile_rs1_data;
          cla_b = ~regfile_rs2_data + 32'b1;

          regfile_rd_data = cla_sum;
        end

        // implement sll
        else if(insn_funct3 == 3'b001 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data << regfile_rs2_data[4:0];
        end

        // implement slt
        else if(insn_funct3 == 3'b010 && insn_funct7 == 7'd0) begin
          regfile_rd_data = ($signed(regfile_rs1_data) < $signed(regfile_rs2_data)) ? 32'd1 : 32'd0;
        end

        //implement sltu
        else if(insn_funct3 == 3'b011 && insn_funct7 == 7'd0) begin
          regfile_rd_data = ($unsigned(regfile_rs1_data) < $unsigned(regfile_rs2_data)) ? 32'd1 : 32'd0;
        end

        //implement xor
        else if(insn_funct3 == 3'b100 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data ^ regfile_rs2_data;
        end

        // implement srl
        else if(insn_funct3 == 3'b101 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data >>> regfile_rs2_data[4:0];
        end

        // implement sra 
        else if(insn_funct3 == 3'b101 && insn_funct7 == 7'b0100000) begin
          regfile_rd_data = $signed(regfile_rs1_data) >>> regfile_rs2_data[4:0];
        end

        // implement or
        else if(insn_funct3 == 3'b110 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data | regfile_rs2_data;
        end

        // implement and
        else if(insn_funct3 == 3'b111 && insn_funct7 == 7'd0) begin
          regfile_rd_data = regfile_rs1_data & regfile_rs2_data;
        end

        // mul
        else if(insn_funct3 == 3'b000 && insn_funct7 == 7'd1) begin
          mul_temp = regfile_rs1_data * regfile_rs2_data;
          regfile_rd_data = mul_temp[31:0];
        end

        // mulh
        else if(insn_funct3 == 3'b001 && insn_funct7 == 7'd1) begin
          mul_temp = $signed(regfile_rs1_data) * $signed(regfile_rs2_data);
          regfile_rd_data = mul_temp[63:32];
        end

        // mulhsu
        else if (insn_funct3 == 3'b010 && insn_funct7 == 7'd1) begin
            regfile_we = 1'b1;
            rs1_abs = regfile_rs1_data[31] ? (~regfile_rs1_data + 1) : regfile_rs1_data;
            mul_abs = rs1_abs * $unsigned(regfile_rs2_data);
            mul_temp = ~mul_abs + 1;  
            regfile_rd_data = regfile_rs1_data[31] ? mul_temp[63:32] : mul_abs[63:32]; 
        end

        // mulhu
        else if(insn_funct3 == 3'b011 && insn_funct7 == 7'd1) begin
          mul_temp = $unsigned(regfile_rs1_data) * $unsigned(regfile_rs2_data);
          regfile_rd_data = mul_temp[63:32];
        end

        // div
        else if(insn_funct3 == 3'b100 && insn_funct7 == 7'd1) begin
          if(div_stall_curr == 1'b1)  begin
            regfile_we = 1'b1;
          end
          else  begin
            regfile_we = 1'b0;
          end

          pos_neg = regfile_rs1_data[31] ^ regfile_rs2_data[31];

          div_dividend = regfile_rs1_data[31] ? (~regfile_rs1_data + 1) : regfile_rs1_data;
          div_dividor = regfile_rs2_data[31] ? (~regfile_rs2_data + 1) : regfile_rs2_data;

          if(regfile_rs2_data == 32'd0) begin
            regfile_rd_data = div_quotient;
          end

          else  begin
            regfile_rd_data = pos_neg ? (~div_quotient + 1) : div_quotient;
          end
        end

        // divu
        else if(insn_funct3 == 3'b101 && insn_funct7 == 7'd1) begin
            div_dividend = regfile_rs1_data;
            div_dividor = regfile_rs2_data;

            if(div_stall_curr == 1'b1)  begin
              regfile_we = 1'b1;
            end
            else  begin
              regfile_we = 1'b0;
            end

            if(regfile_rs2_data == 32'd0) begin
              regfile_rd_data = 32'hFFFFFFFF; 
            end

            else begin
              regfile_rd_data = div_quotient; 
            end
        end

        // rem
        else if(insn_funct3 == 3'b110 && insn_funct7 == 7'd1) begin
          if(div_stall_curr == 1'b1)  begin
            regfile_we = 1'b1;
          end
          else  begin
            regfile_we = 1'b0;
          end

          div_dividend = regfile_rs1_data[31] ? (~regfile_rs1_data + 1) : regfile_rs1_data;
          div_dividor = regfile_rs2_data[31] ? (~regfile_rs2_data + 1) : regfile_rs2_data;

          if (regfile_rs2_data == 32'd0) begin
            regfile_rd_data = regfile_rs1_data;
          end 
          else begin
            regfile_rd_data = regfile_rs1_data[31] ? (~div_remainder + 1) : div_remainder;
          end
        end

        // remu 
        else if(insn_funct3 == 3'b111 && insn_funct7 == 7'd1) begin
          if(div_stall_curr == 1'b1)  begin
            regfile_we = 1'b1;
          end
          else  begin
            regfile_we = 1'b0;
          end

          div_dividend = regfile_rs1_data;
          div_dividor = regfile_rs2_data;

          if (regfile_rs2_data == 32'd0) begin
            regfile_rd_data = regfile_rs1_data;
          end else begin
            regfile_rd_data = div_remainder;
          end
        end

        else  begin
          illegal_insn = 1'b1;
        end
      end

      OpBranch: begin
        // implement beq insn
        regfile_we = 1'b0;
        if(insn_funct3 == 3'b000) begin
          if(regfile_rs1_data == regfile_rs2_data)  begin
            cla_a = pcCurrent;
            cla_b = branch_imm;

            pcNext = cla_sum;
          end
          else  begin
          end
        end

        // implement bne insn
        else if(insn_funct3 == 3'b001)  begin
          if(regfile_rs1_data != regfile_rs2_data)  begin
            cla_a = pcCurrent;
            cla_b = branch_imm;

            pcNext = cla_sum;
          end
          else  begin
          end
        end

        // implement blt insn
        else if(insn_funct3 == 3'b100)  begin
          if($signed(regfile_rs1_data) < $signed(regfile_rs2_data)) begin
            cla_a = pcCurrent;
            cla_b = branch_imm;

            pcNext = cla_sum;
          end

          else  begin
          end
        end

        // implement bge insn
        else if(insn_funct3 == 3'b101)  begin
          if($signed(regfile_rs1_data) >= $signed(regfile_rs2_data)) begin
            cla_a = pcCurrent;
            cla_b = branch_imm;

            pcNext = cla_sum;
          end
          
          else  begin
          end
        end

        // implement bltu insn
        else if(insn_funct3 == 3'b110)  begin
          if($unsigned(regfile_rs1_data) < $unsigned(regfile_rs2_data)) begin
            cla_a = pcCurrent;
            cla_b = branch_imm; 

            pcNext = cla_sum;
          end
          
          else  begin
          end
        end

        // implement bgeu insn
        else if(insn_funct3 == 3'b111)  begin
          if($unsigned(regfile_rs1_data) >= $unsigned(regfile_rs2_data)) begin
            cla_a = pcCurrent;
            cla_b = branch_imm;

            pcNext = cla_sum;
          end
          
          else  begin
          end
        end

        else  begin
          illegal_insn = 1'b1;
        end
      end

      // ecall
      OpEnviron: begin
        if(insn_from_imem[31:7] == 25'd0) begin
          halt = 1'b1;
        end
        else  begin
          illegal_insn = 1'b1;
        end
      end

      // implement load insns
      OpLoad: begin
        case(insn_funct3)
          // implement lb
          3'b000: begin
            regfile_we = 1'b1;

            cla_a = regfile_rs1_data;
            cla_b = reg_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];
            
            case(mem_addr_offset)
              2'b00: regfile_rd_data = {{24{load_data_from_dmem[7]}}, {load_data_from_dmem[7:0]}};
              2'b01: regfile_rd_data = {{24{load_data_from_dmem[15]}}, {load_data_from_dmem[15:8]}};
              2'b10: regfile_rd_data = {{24{load_data_from_dmem[23]}}, {load_data_from_dmem[23:16]}};
              2'b11: regfile_rd_data = {{24{load_data_from_dmem[31]}}, {load_data_from_dmem[31:24]}};
            endcase
          end

          // implement lbu
          3'b100: begin
            regfile_we = 1'b1;

            cla_a = regfile_rs1_data;
            cla_b = reg_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];
            
            case(mem_addr_offset)
              2'b00: regfile_rd_data = {{24'b0}, {load_data_from_dmem[7:0]}};
              2'b01: regfile_rd_data = {{24'b0}, {load_data_from_dmem[15:8]}};
              2'b10: regfile_rd_data = {{24'b0}, {load_data_from_dmem[23:16]}};
              2'b11: regfile_rd_data = {{24'b0}, {load_data_from_dmem[31:24]}};
            endcase
          end

          // implement lh
          3'b001: begin
            regfile_we = 1'b1;

            cla_a = regfile_rs1_data;
            cla_b = reg_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];
            
            case(mem_addr_offset)
              2'b00: regfile_rd_data = {{16{load_data_from_dmem[15]}}, {load_data_from_dmem[15:0]}};
              2'b10: regfile_rd_data = {{16{load_data_from_dmem[31]}}, {load_data_from_dmem[31:16]}};
              default: illegal_insn = 1'b1;
            endcase
          end

          // implement lhu
          3'b101: begin
            regfile_we = 1'b1;

            cla_a = regfile_rs1_data;
            cla_b = reg_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];
            
            case(mem_addr_offset)
              2'b00: regfile_rd_data = {{16'b0}, {load_data_from_dmem[15:0]}};
              2'b10: regfile_rd_data = {{16'b0}, {load_data_from_dmem[31:16]}};
              default: illegal_insn = 1'b1;
            endcase
          end

          // implement lw
          3'b010: begin
            regfile_we = 1'b1;

            cla_a = regfile_rs1_data;
            cla_b = reg_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];
            
            case(mem_addr_offset)
              2'b00: regfile_rd_data = load_data_from_dmem;
              default: illegal_insn = 1'b1;
            endcase
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      // implement store insns
      OpStore:  begin
        case(insn_funct3)
          // sb
          3'b000: begin
            regfile_we = 1'b0;

            cla_a = regfile_rs1_data;
            cla_b = st_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];

            new_store_data_to_dmem = 32'd0;

            case(mem_addr_offset)
              2'b00:  begin
                new_store_we_to_dmem = 4'b0001;
                new_store_data_to_dmem[7:0] = regfile_rs2_data[7:0];
              end

              2'b01:  begin
                new_store_we_to_dmem = 4'b0010;
                new_store_data_to_dmem[15:8] = regfile_rs2_data[7:0];
              end

              2'b10: begin
                new_store_we_to_dmem = 4'b0100;
                new_store_data_to_dmem[23:16] = regfile_rs2_data[7:0];
              end

              2'b11:  begin
                new_store_we_to_dmem = 4'b1000;
                new_store_data_to_dmem[31:24] = regfile_rs2_data[7:0];               
              end
            endcase
          end

          // sh
          3'b001: begin
            regfile_we = 1'b0;

            cla_a = regfile_rs1_data;
            cla_b = st_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];

            new_store_data_to_dmem = 32'd0;

            case(mem_addr_offset)
              2'b00:  begin
                new_store_we_to_dmem = 4'b0011;
                new_store_data_to_dmem[15:0] = regfile_rs2_data[15:0];
              end

              2'b10: begin
                new_store_we_to_dmem = 4'b1100;
                new_store_data_to_dmem[31:16] = regfile_rs2_data[15:0];
              end

              default:  illegal_insn = 1'b1;
            endcase
          end

          // sw
          3'b010: begin
            regfile_we = 1'b0;

            cla_a = regfile_rs1_data;
            cla_b = st_imm32;

            mem_addr_raw = cla_sum;
            new_addr_to_dmem = mem_addr_raw & 32'hFFFFFFFC;
            mem_addr_offset = mem_addr_raw[1:0];

            new_store_data_to_dmem = 32'd0;

            case(mem_addr_offset)
              2'b00:  begin
                new_store_we_to_dmem = 4'b1111;
                new_store_data_to_dmem = regfile_rs2_data;
              end

              default: illegal_insn = 1'b1;
            endcase
          end

          default:
            illegal_insn = 1'b1;
        endcase
      end

      default: begin
        regfile_we = 1'b0;
        illegal_insn = 1'b1;
      end
    endcase
  end


endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathMultiCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
