`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

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
  // genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  // wire up the output port with the corresponding register
  assign regs[0] = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  // flip-flops
  always_ff @(posedge clk)  begin
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

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  // localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // Instantiate RegFile and its corresponding signals
  wire [4:0] regfile_rd;
  wire [`REG_SIZE] regfile_rd_data;
  wire [4:0] regfile_rs1, regfile_rs2;
  wire [`REG_SIZE] regfile_rs1_data, regfile_rs2_data;
  wire regfile_we; // Write enable for the RegFile

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

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  always_comb begin
    if(rst) begin
      f_cycle_status = CYCLE_RESET;
    end
    else  begin
      f_cycle_status = flush ? CYCLE_TAKEN_BRANCH : CYCLE_NO_STALL;
    end
  end

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      // f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      // f_cycle_status <= flush ? CYCLE_TAKEN_BRANCH : CYCLE_NO_STALL;
      f_pc_current <= jump_to_pc;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = flush ? 32'h0 : insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        decode_state <= '{
          pc: flush ? 32'h0 : f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs1;
  wire [4:0] insn_rs2;
  wire [31:0] data_rs1;
  wire [31:0] data_rs2;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = decode_state.insn;
  assign regfile_rs1 = insn_rs1;
  assign regfile_rs2 = insn_rs2;

  /****************/
  /* EXECUTE STAGE */
  /****************/

  typedef struct packed {
    logic [`REG_SIZE] pc;
    logic [`INSN_SIZE] insn;
    logic [6:0] insn_opcode;
    logic [4:0] insn_rd;
    logic [2:0] insn_funct3;
    logic [4:0] insn_rs1;
    logic [4:0] insn_rs2;
    logic [31:0] data_rs1;
    logic [31:0] data_rs2;
    logic [6:0] insn_funct7;
    cycle_status_e cycle_status;
  } stage_execute_t;

  stage_execute_t execute_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        insn_opcode: 0,
        insn_rd: 0,
        insn_funct3: 0,
        insn_rs1: 0,
        insn_rs2: 0,
        data_rs1: 0,
        data_rs2: 0,
        insn_funct7: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        execute_state <= '{
          pc: flush ? 32'h0 : decode_state.pc,
          insn: flush ? 32'h0 : decode_state.insn,
          insn_opcode: flush ? 7'h0 : insn_opcode,
          insn_rd: flush ? 5'h0 : insn_rd,
          insn_funct3: flush ? 3'h0 : insn_funct3,
          insn_rs1: flush ? 5'h0 : insn_rs1,
          insn_rs2: flush ? 5'h0 : insn_rs2,
          data_rs1: (wd_bypass_rs1) ? writeback_state.data_rd : regfile_rs1_data,
          data_rs2: (wd_bypass_rs2) ? writeback_state.data_rd : regfile_rs2_data,
          insn_funct7: flush ? 7'h0 : insn_funct7,
          cycle_status: flush ? CYCLE_TAKEN_BRANCH : decode_state.cycle_status
        };
      end
    end
  end

  logic [`REG_SIZE] cla_a;
  logic [`REG_SIZE] cla_b;
  logic cla_cin;
  logic [`REG_SIZE] cla_sum;

  cla _cla(
    .a(cla_a),
    .b(cla_b),
    .cin(cla_cin),
    .sum(cla_sum)
  );

  logic [31:0] res_alu;
  wire [11:0] reg_imm12;
  wire [31:0] reg_imm32;
  wire [31:0] branch_imm;
  assign reg_imm12 = (execute_state.insn_opcode == OpcodeStore) ? {{execute_state.insn[31:25]}, {execute_state.insn[11:7]}} : execute_state.insn[31:20];
  assign reg_imm32 = {{20{reg_imm12[11]}}, reg_imm12};
  assign branch_imm = {{20{execute_state.insn[31]}}, execute_state.insn[7], execute_state.insn[30:25], execute_state.insn[11:8], 1'b0};

  logic illegal_insn;

  logic [31:0] alu_data_rs1;
  logic [31:0] alu_data_rs2;

  // handle flush caused by branch insns
  logic flush;
  logic [`REG_SIZE] jump_to_pc;

  //handle mem offset
  logic [31:0] mem_addr_raw;
  logic [31:0] mem_addr_base;
  logic [1:0] mem_addr_offset;

  always_comb begin
    if(mx_bypass_rs1) begin
      alu_data_rs1 = (memory_state.insn_opcode == OpcodeLoad) ? m_data_to_reg : memory_state.data_rd;
    end
    else if(wx_bypass_rs1)  begin
      alu_data_rs1 = writeback_state.data_rd;
    end
    else  begin
      alu_data_rs1 = execute_state.data_rs1;
    end
  end

  always_comb begin
    if(mx_bypass_rs2) begin
      alu_data_rs2 = (memory_state.insn_opcode == OpcodeLoad) ? m_data_to_reg : memory_state.data_rd;
    end
    else if(wx_bypass_rs2)  begin
      alu_data_rs2 = writeback_state.data_rd;
    end
    else  begin
      alu_data_rs2 = execute_state.data_rs2;
    end
  end

  always_comb begin
    illegal_insn = 1'b0;
    flush = 1'b0;
    jump_to_pc = f_pc_current + 4;
    res_alu = 32'h0;
    cla_a = 32'h0;
    cla_b = 32'h0;
    cla_cin = 1'b0;

    mem_addr_raw = 32'h0;
    mem_addr_base = 32'h0;
    mem_addr_offset = 2'h0;
    case (execute_state.insn_opcode)
      OpcodeLui: begin
        res_alu = {execute_state.insn[31:12], 12'b0};                
      end

      OpcodeRegImm: begin
        case  (execute_state.insn_funct3)
          // addi
          3'b000: begin
            cla_a = alu_data_rs1;
            cla_b = reg_imm32;
            cla_cin = 1'b0;
            res_alu = cla_sum;
          end

          3'b001: begin
            // slli
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = alu_data_rs1 << reg_imm12[4:0];
            end
            else begin
            end
          end

          3'b010: begin
            // slti
            res_alu = ($signed(alu_data_rs1) < $signed(reg_imm32)) ? 32'd1 : 32'd0;
          end

          3'b011: begin
            // sltiu
            res_alu = ($unsigned(alu_data_rs1) < $unsigned(reg_imm32)) ? 32'd1 : 32'd0;
          end

          3'b100: begin
            // xori
            res_alu = alu_data_rs1 ^ reg_imm32;
          end

          3'b101: begin
            //srai
            if(execute_state.insn_funct7 == 7'h20)  begin
              res_alu = $signed(alu_data_rs1) >>> reg_imm12[4:0];
            end
            //srli
            else if(execute_state.insn_funct7 == 7'h0)  begin
              res_alu = alu_data_rs1 >> reg_imm12[4:0];
            end
            else  begin
            end
          end

          // ori
          3'b110: begin
            res_alu = alu_data_rs1 | reg_imm32;
          end 

          3'b111: begin
            // andi
            res_alu = alu_data_rs1 & reg_imm32;
          end

          default:  begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      OpcodeRegReg: begin
        case (execute_state.insn_funct3)
          3'b000: begin
            // add 
            if(execute_state.insn_funct7 == 7'h0) begin
              cla_a = alu_data_rs1;
              cla_b = alu_data_rs2;
              cla_cin = 1'b0;
              res_alu = cla_sum;
            end
            // sub
            else if(execute_state.insn_funct7 == 7'h20) begin
              cla_a = alu_data_rs1;
              cla_b = ~alu_data_rs2 + 32'b1;
              cla_cin = 1'b0;
              res_alu = cla_sum;
            end
            else  begin
              illegal_insn = 1'b1;
            end
          end

          3'b001: begin
            //sll
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = alu_data_rs1 << alu_data_rs2[4:0];
            end

            else  begin
              illegal_insn = 1'b1;
            end
          end

          3'b010: begin
            //slt
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = ($signed(alu_data_rs1) < $signed(alu_data_rs2)) ? 32'd1 : 32'd0;
            end

            else  begin
            end
          end

          3'b011: begin
            //sltu
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu  = ($unsigned(alu_data_rs1) < $unsigned(alu_data_rs2)) ? 32'd1 : 32'd0;
            end

            else  begin
            end
          end

          3'b100: begin
            //xor
            res_alu = alu_data_rs1 ^ alu_data_rs2;
          end

          3'b101: begin
            //srl
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = alu_data_rs1 >>> alu_data_rs2[4:0];
            end
            //sra
            else if(execute_state.insn_funct7 == 7'h20) begin
              res_alu = $signed(alu_data_rs1) >>> alu_data_rs2[4:0];
            end
            else  begin
              illegal_insn = 1'b1;
            end
          end         

          3'b110: begin
            //or
            res_alu = alu_data_rs1 | alu_data_rs2;
          end

          3'b111: begin
            //and
            res_alu = alu_data_rs1 & alu_data_rs2;
          end

          default:  begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      OpcodeBranch: begin
        case(execute_state.insn_funct3)
          // beq
          3'b000: begin
            if(alu_data_rs1 == alu_data_rs2)  begin
              flush = 1'b1;
              cla_a = execute_state.pc;
              cla_b = branch_imm;
              jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
            end else  begin
              jump_to_pc = f_pc_current + 4;
            end
          end
          // bne
          3'b001: begin
            if(alu_data_rs1 != alu_data_rs2)  begin
              flush = 1'b1;
              cla_a = execute_state.pc;
              cla_b = branch_imm;
              jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
            end else  begin
              jump_to_pc = f_pc_current + 4;
            end
          end
          // blt
          3'b100: begin
            if($signed(alu_data_rs1) < $signed(alu_data_rs2)) begin
              flush = 1'b1;
              cla_a = execute_state.pc;
              cla_b = branch_imm;
              jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
            end
            else  begin
              jump_to_pc = f_pc_current + 4;
            end
          end
          // bge
          3'b101: begin
            if($signed(alu_data_rs1) >= $signed(alu_data_rs2)) begin
              flush = 1'b1;
              cla_a = execute_state.pc;
              cla_b = branch_imm;
              jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
            end
            else  begin
              jump_to_pc = f_pc_current + 4;
            end
          end
          // bltu
          3'b110: begin
          if($unsigned(alu_data_rs1) < $unsigned(alu_data_rs2)) begin
            flush = 1'b1;
            cla_a = execute_state.pc;
            cla_b = branch_imm; 
            jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
          end
          else  begin
            jump_to_pc = f_pc_current + 4;
          end
          end
          // bgeu
          3'b111: begin
            if($unsigned(alu_data_rs1) >= $unsigned(alu_data_rs2)) begin
              flush = 1'b1;
              cla_a = execute_state.pc;
              cla_b = branch_imm;
              jump_to_pc = (execute_state.cycle_status == CYCLE_TAKEN_BRANCH) ? f_pc_current + 4 : cla_sum;
            end
            else  begin
              jump_to_pc = f_pc_current + 4;
            end
          end
          default:  begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      OpcodeLoad: begin
        cla_a = alu_data_rs1;
        cla_b = reg_imm32;
        cla_cin = 1'b0;
        mem_addr_raw = cla_sum;
        mem_addr_base = mem_addr_raw & 32'hFFFFFFFC;
        mem_addr_offset = mem_addr_raw[1:0];
      end

      OpcodeStore: begin
        cla_a = alu_data_rs1;
        cla_b = reg_imm32;
        cla_cin = 1'b0;
        mem_addr_raw = cla_sum;
        mem_addr_base = mem_addr_raw & 32'hFFFFFFFC;
        mem_addr_offset = mem_addr_raw[1:0];
      end

      default:  begin
        res_alu = 32'd0;
        cla_a = 32'd0;
        cla_b = 32'd0;
        cla_cin = 1'b0;
        illegal_insn = 1'b1;
      end
    endcase
  end

  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

  /****************/
  /* MEMORY STAGE */
  /****************/

  typedef struct packed {
    logic [`REG_SIZE] pc;
    logic [`INSN_SIZE] insn;
    logic [6:0] insn_opcode;
    logic [2:0] insn_funct3;
    logic [4:0] insn_rd;
    logic [31:0] data_rd;
    logic [31:0] mem_addr_base;
    logic [1:0] mem_addr_offset;
    logic [4:0] reg_addr_to_st;
    logic [31:0] data_to_dmem;
    logic illegal_insn;
    cycle_status_e cycle_status;
  } stage_memory_t;
  
  stage_memory_t memory_state;

  always_ff @(posedge clk)  begin
    if(rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        insn_opcode: 0,
        insn_funct3: 0,
        insn_rd: 0,
        data_rd: 0,
        mem_addr_base: 0,
        mem_addr_offset: 0,
        reg_addr_to_st: 0,
        data_to_dmem: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET
      };
    end
    else  begin
      memory_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        insn_opcode: execute_state.insn_opcode,
        insn_funct3: execute_state.insn_funct3,
        insn_rd: execute_state.insn_rd,
        data_rd: res_alu,
        mem_addr_base: mem_addr_base,
        mem_addr_offset: mem_addr_offset,
        reg_addr_to_st: execute_state.insn_rs2,
        data_to_dmem: alu_data_rs2,
        illegal_insn: illegal_insn,
        cycle_status: execute_state.cycle_status
      };
    end
  end

  assign addr_to_dmem = memory_state.mem_addr_base;

  logic [31:0] m_data_to_reg;
  logic [31:0] m_data_to_dmem;
  logic [3:0] m_st_we_to_dmem;
  logic m_illegal_insn;

  assign store_data_to_dmem = m_data_to_dmem;
  assign store_we_to_dmem = m_st_we_to_dmem;
  
  always_comb begin
    m_illegal_insn = 1'b0;
    m_data_to_dmem = 32'h0;
    m_st_we_to_dmem = 4'h0;
    case(memory_state.insn_opcode)
      OpcodeLoad: begin
        case(memory_state.insn_funct3)
          //lb
          3'b000: begin
            case(memory_state.mem_addr_offset)
              2'b00:  m_data_to_reg = {{24{load_data_from_dmem[7]}}, {load_data_from_dmem[7:0]}};
              2'b01:  m_data_to_reg = {{24{load_data_from_dmem[15]}}, {load_data_from_dmem[15:8]}};
              2'b10:  m_data_to_reg = {{24{load_data_from_dmem[23]}}, {load_data_from_dmem[23:16]}};
              2'b11:  m_data_to_reg = {{24{load_data_from_dmem[31]}}, {load_data_from_dmem[31:24]}};
            endcase
          end

          // lh
          3'b001: begin
            case(memory_state.mem_addr_offset)
              2'b00: m_data_to_reg = {{16{load_data_from_dmem[15]}}, {load_data_from_dmem[15:0]}};
              2'b10: m_data_to_reg = {{16{load_data_from_dmem[31]}}, {load_data_from_dmem[31:16]}};
              default: m_illegal_insn = 1'b1;
            endcase
          end

          // lbu
          3'b100: begin
            case(memory_state.mem_addr_offset)
              2'b00:  m_data_to_reg = {{24'b0}, {load_data_from_dmem[7:0]}};
              2'b01:  m_data_to_reg = {{24'b0}, {load_data_from_dmem[15:8]}};
              2'b10:  m_data_to_reg = {{24'b0}, {load_data_from_dmem[23:16]}};
              2'b11:  m_data_to_reg = {{24'b0}, {load_data_from_dmem[31:24]}};
            endcase
          end

          // lhu
          3'b101: begin
            case(memory_state.mem_addr_offset)
              2'b00: m_data_to_reg = {{16'b0}, {load_data_from_dmem[15:0]}};
              2'b10: m_data_to_reg = {{16'b0}, {load_data_from_dmem[31:16]}};
              default: m_illegal_insn = 1'b1;
            endcase
          end

          //lw
          3'b010: begin
            case(memory_state.mem_addr_offset)
              2'b00: m_data_to_reg = load_data_from_dmem;
              default: m_illegal_insn = 1'b1;
            endcase
          end

          default:  begin
            m_illegal_insn = 1'b1;
          end
        endcase
      end

      OpcodeStore:  begin
        case(memory_state.insn_funct3)
          // sb
          3'b000: begin
            case(memory_state.mem_addr_offset)
              2'b00: begin
                m_st_we_to_dmem = 4'b0001;
                m_data_to_dmem[7:0] = (wm_bypass_data) ? writeback_state.data_rd[7:0] : memory_state.data_to_dmem[7:0];
              end

              2'b01:  begin
                m_st_we_to_dmem = 4'b0010;
                m_data_to_dmem[15:8] = (wm_bypass_data) ? writeback_state.data_rd[7:0] : memory_state.data_to_dmem[7:0];
              end

              2'b10: begin
                m_st_we_to_dmem = 4'b0100;
                m_data_to_dmem[23:16] = (wm_bypass_data) ? writeback_state.data_rd[7:0] : memory_state.data_to_dmem[7:0];
              end

              2'b11:  begin
                m_st_we_to_dmem = 4'b1000;
                m_data_to_dmem[31:24] = (wm_bypass_data) ? writeback_state.data_rd[7:0] : memory_state.data_to_dmem[7:0];               
              end
            endcase
          end

          // sh
          3'b001: begin
            case(memory_state.mem_addr_offset)
              2'b00:  begin
                m_st_we_to_dmem = 4'b0011;
                m_data_to_dmem[15:0] = (wm_bypass_data) ? writeback_state.data_rd[15:0] : memory_state.data_to_dmem[15:0];
              end

              2'b10: begin
                m_st_we_to_dmem = 4'b1100;
                m_data_to_dmem[31:16] = (wm_bypass_data) ? writeback_state.data_rd[15:0] : memory_state.data_to_dmem[15:0];
              end

              default:  m_illegal_insn = 1'b1;
            endcase
          end

          // sw
          3'b010: begin
            case(memory_state.mem_addr_offset)
              2'b00:  begin
                m_st_we_to_dmem = 4'b1111;
                m_data_to_dmem = (wm_bypass_data) ? writeback_state.data_rd : memory_state.data_to_dmem;
              end

              default: m_illegal_insn = 1'b1;
            endcase
          end

          default:  begin
            m_illegal_insn = 1'b1;
          end
        endcase
      end

      default:  begin
        m_data_to_reg = 32'h0;
      end
    endcase
  end

  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

  /********************/
  /* WRITE_BACK STAGE */
  /********************/

  typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [6:0] insn_opcode;
  logic [4:0] insn_rd;
  logic [31:0] data_rd;
  logic illegal_insn;
  cycle_status_e cycle_status;
  } stage_writeback_t;

  stage_writeback_t writeback_state;

  always_ff @(posedge clk)  begin
    if(rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        insn_opcode: 0,
        insn_rd: 0,
        data_rd: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET
      };
    end
    else  begin
      writeback_state <= '{
        pc: memory_state.pc,
        insn: memory_state.insn,
        insn_opcode: memory_state.insn_opcode,
        insn_rd: memory_state.insn_rd,
        data_rd: (memory_state.insn_opcode == OpcodeLoad) ? m_data_to_reg : memory_state.data_rd,
        illegal_insn: (m_illegal_insn) ? m_illegal_insn : memory_state.illegal_insn,
        cycle_status: memory_state.cycle_status
      };
    end
  end

  assign regfile_we = (writeback_state.insn == 32'h0 || writeback_state.insn_opcode == 7'h63 || writeback_state.cycle_status == CYCLE_TAKEN_BRANCH) ? 1'b0 : 1'b1;
  assign regfile_rd = writeback_state.insn_rd;
  assign regfile_rd_data = writeback_state.data_rd;

  always_comb begin
    case(writeback_state.insn_opcode)  
      OpcodeEnviron:  begin
        if(writeback_state.insn[31:7] == 25'd0) begin
          halt = 1'b1;
        end
        else  begin
          halt = 1'b0;
        end
      end
      default:  begin
        halt = 1'b0;
      end
    endcase
  end

  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

  /*****************/
  /* BYPASS HANDLE */
  /*****************/
  wire mx_bypass_rs1;
  wire mx_bypass_rs2;
  wire wx_bypass_rs1;
  wire wx_bypass_rs2;
  wire wd_bypass_rs1;
  wire wd_bypass_rs2;
  wire wm_bypass_data;
  // wire wm_bypass_addr;
  wire m_rd_make_sense;
  wire m_rs2_make_sense;
  wire w_rd_make_sense;
  wire x_rs1_make_sense;
  wire x_rs2_make_sense;
  wire d_rs1_make_sense;
  wire d_rs2_make_sense;
  assign m_rd_make_sense = memory_state.insn_opcode == OpcodeLui || memory_state.insn_opcode == OpcodeAuipc || memory_state.insn_opcode == OpcodeRegImm || memory_state.insn_opcode == OpcodeRegReg || memory_state.insn_opcode == OpcodeLoad || memory_state.insn_opcode == OpcodeJal || memory_state.insn_opcode == OpcodeJalr;
  assign m_rs2_make_sense = memory_state.insn_opcode == OpcodeStore;
  assign w_rd_make_sense = writeback_state.insn_opcode == OpcodeLui || writeback_state.insn_opcode == OpcodeAuipc || writeback_state.insn_opcode == OpcodeRegImm || writeback_state.insn_opcode == OpcodeRegReg || writeback_state.insn_opcode == OpcodeLoad || writeback_state.insn_opcode == OpcodeJal || writeback_state.insn_opcode == OpcodeJalr;
  assign x_rs1_make_sense = execute_state.insn_opcode == OpcodeRegImm || execute_state.insn_opcode == OpcodeRegReg || execute_state.insn_opcode == OpcodeBranch || execute_state.insn_opcode == OpcodeLoad || execute_state.insn_opcode == OpcodeStore || execute_state.insn_opcode == OpcodeJalr;
  assign x_rs2_make_sense = execute_state.insn_opcode == OpcodeRegReg || execute_state.insn_opcode == OpcodeStore || execute_state.insn_opcode == OpcodeBranch;
  assign d_rs1_make_sense = insn_opcode == OpcodeRegImm || insn_opcode == OpcodeRegReg || insn_opcode == OpcodeBranch || insn_opcode == OpcodeLoad || insn_opcode == OpcodeStore || insn_opcode == OpcodeJalr;
  assign d_rs2_make_sense = insn_opcode == OpcodeRegReg || insn_opcode == OpcodeStore || insn_opcode == OpcodeBranch;
  assign mx_bypass_rs1 = (execute_state.insn_rs1 == memory_state.insn_rd && illegal_insn == 1'b0 && memory_state.illegal_insn == 1'b0 && memory_state.insn_rd != 5'd0 && m_rd_make_sense && x_rs1_make_sense);
  assign mx_bypass_rs2 = (execute_state.insn_rs2 == memory_state.insn_rd && illegal_insn == 1'b0 && memory_state.illegal_insn == 1'b0 && memory_state.insn_rd != 5'd0 && m_rd_make_sense && x_rs2_make_sense);
  assign wx_bypass_rs1 = (execute_state.insn_rs1 == writeback_state.insn_rd && illegal_insn == 1'b0 && writeback_state.illegal_insn == 1'b0 && writeback_state.insn_rd != 5'd0 && w_rd_make_sense && x_rs1_make_sense);
  assign wx_bypass_rs2 = (execute_state.insn_rs2 == writeback_state.insn_rd && illegal_insn == 1'b0 && writeback_state.illegal_insn == 1'b0 && writeback_state.insn_rd != 5'd0 && w_rd_make_sense && x_rs2_make_sense);
  assign wd_bypass_rs1 = (insn_rs1 == writeback_state.insn_rd && writeback_state.insn_rd != 5'd0 && w_rd_make_sense && d_rs1_make_sense);
  assign wd_bypass_rs2 = (insn_rs2 == writeback_state.insn_rd && writeback_state.insn_rd != 5'd0 && w_rd_make_sense && d_rs2_make_sense);
  assign wm_bypass_data = (writeback_state.insn_rd == memory_state.reg_addr_to_st && w_rd_make_sense && m_rs2_make_sense);
  // assign wm_bypass_addr = ();

  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
