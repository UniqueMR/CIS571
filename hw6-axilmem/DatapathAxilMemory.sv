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
  // TODO: copy your RegFile code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

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

/***************************/
/* FROM PIPELINED DATAPATH */
/***************************/

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


/***************************/
/* END PIPELINED DATAPATH */
/***************************/


/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    // parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  // TODO: changes will be needed throughout this module

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
      // start out ready to accept incoming reads
      insn.ARREADY <= 1;
      data.ARREADY <= 1;
      // start out ready to accept an incoming write
      data.AWREADY <= 1;
      data.WREADY <= 1;
    end else begin
      
      if(insn.WVALID && insn.AWVALID) begin
        mem_array[insn.AWADDR[AddrMsb:AddrLsb]] <= insn.WDATA;
        insn.BVALID <= 1'b1;
        insn.BRESP <= ResponseOkay;
      end
      else  begin
        insn.BVALID <= 1'b0;
        insn.BRESP <= ResponseSubordinateError;
      end

      if(insn.ARVALID && insn.RREADY) begin
        insn.RDATA <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
        insn.RVALID <= 1'b1;
      end
      else  begin
        insn.RVALID <= 1'b0;
      end
      

      if(data.WVALID && data.AWVALID) begin
        mem_array[data.AWADDR[AddrMsb:AddrLsb]] <= data.WDATA;
        data.BVALID <= 1'b1;
        data.BRESP <= ResponseOkay;
      end
      else  begin
        data.BVALID <= 1'b0;
        data.BRESP <= ResponseSubordinateError;
      end

      if(data.ARVALID && data.RREADY) begin
        data.RDATA <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
        data.RVALID <= 1'b1;
      end
      else  begin
        data.RVALID <= 1'b0;
      end

    end
  end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
endmodule

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    // output logic [`REG_SIZE] pc_to_imem,
    // input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,
    // // ...with this AXIL one
    // axi_if.manager dmem,

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
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
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

  logic f_insn_addr_read_valid;
  logic f_insn_read_ready;

  always_comb begin
    if(rst) begin
      f_cycle_status = CYCLE_RESET;
      f_insn_addr_read_valid = 1'b0;
      f_insn_read_ready = 1'b0;
    end
    else if(flush)  begin
      f_cycle_status = CYCLE_TAKEN_BRANCH;
      f_insn_addr_read_valid = 1'b0;
      f_insn_read_ready = 1'b0;
    end
    else  begin
      f_cycle_status = CYCLE_NO_STALL;
      f_insn_addr_read_valid = 1'b1;
      f_insn_read_ready = 1'b1;
    end
  end

  // program counter
  logic div_stall_next, div_stall_curr;
  logic load_stall_next, load_stall_curr;
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      // f_cycle_status <= CYCLE_NO_STALL;
      div_stall_curr <= 1'b0;
      load_stall_curr <= 1'b0;
    end
    else if(fence || div_stall_next || load_stall_next)  begin
      f_pc_current <= f_pc_current;
      div_stall_curr <= div_stall_next;
      load_stall_curr <= load_stall_next;
    end
    else begin
      // f_cycle_status <= flush ? CYCLE_TAKEN_BRANCH : CYCLE_NO_STALL;
      f_pc_current <= jump_to_pc;
      div_stall_curr <= div_stall_next;
      load_stall_curr <= load_stall_next;
    end
  end
  // send PC to imem
  assign imem.ARADDR = f_pc_current;
  assign f_insn = flush ? 32'h0 : imem.RDATA;
  assign imem.ARVALID = f_insn_addr_read_valid;
  assign imem.RREADY = f_insn_read_ready;

  logic fence;

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
  // always_ff @(posedge clk) begin
  //   if (rst) begin
  //     decode_state <= '{
  //       pc: 0,
  //       insn: 0,
  //       cycle_status: CYCLE_RESET
  //     };
  //   end
  //   else if(div_stall_next || load_stall_next || fence) begin
  //     decode_state <= '{
  //       pc: decode_state.pc,
  //       insn: decode_state.insn,
  //       cycle_status: decode_state.cycle_status
  //     };
  //   end
  //   else begin
  //     decode_state <= '{
  //       pc: flush ? 32'h0 : f_pc_current,
  //       insn: f_insn,
  //       cycle_status: f_cycle_status
  //     };
  //   end
  // end

  always_comb begin
    if (rst) begin
      decode_state = '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end
    else begin
      decode_state = '{
        pc: f_pc_current,
        insn: f_insn,
        cycle_status: f_cycle_status
      };
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

  always_comb begin
    if(insn_opcode == OpcodeMiscMem)  begin
      if(execute_state.insn_opcode == OpcodeStore || memory_state.insn_opcode == OpcodeStore) begin
        fence = 1'b1;
      end
      else  begin
        fence = 1'b0;
      end
    end
    else  begin
      fence = 1'b0;
    end
  end

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
    if (rst || fence) begin
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
        cycle_status: (rst) ? CYCLE_RESET : CYCLE_FENCEI
      };
    end 
    else if(div_stall_next || load_stall_next) begin
      execute_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        insn_opcode: execute_state.insn_opcode,
        insn_rd: execute_state.insn_rd,
        insn_funct3: execute_state.insn_funct3,
        insn_rs1: execute_state.insn_rs1,
        insn_rs2: execute_state.insn_rs2,
        data_rs1: alu_data_rs1,
        data_rs2: alu_data_rs2,
        insn_funct7: execute_state.insn_funct7,
        cycle_status: execute_state.cycle_status
      };
    end

    else begin
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
      alu_data_rs1 = memory_state.data_rd;
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
      alu_data_rs2 = memory_state.data_rd;
    end
    else if(wx_bypass_rs2)  begin
      alu_data_rs2 = writeback_state.data_rd;
    end
    else  begin
      alu_data_rs2 = execute_state.data_rs2;
    end
  end

  wire [31:0] jal_imm;
  assign jal_imm = {{12{execute_state.insn[31]}}, execute_state.insn[19:12], execute_state.insn[20], execute_state.insn[30:21], 1'b0};

  logic [63:0]  mul_temp;
  logic [31:0]  rs1_abs;
  logic [63:0]  mul_abs;

  always_comb begin
    illegal_insn = 1'b0;
    flush = 1'b0;
    res_alu = 32'h0;
    cla_a = 32'h0;
    cla_b = 32'h0;
    cla_cin = 1'b0;

    // init signals for div
    div_dividend = 32'b0;
    div_dividor = 32'b0;
    pos_neg = 1'b0;

    mul_temp = 64'h0;
    rs1_abs = 32'h0;
    mul_abs = 64'h0;

    if(execute_state.insn_opcode == OpcodeRegReg && execute_state.insn_funct3[2] == 1'b1 && execute_state.insn_funct7 == 7'h1)  begin
      if(div_stall_curr == 1'b0)  begin
        div_stall_next = 1'b1;
      end
      else  begin
        div_stall_next = 1'b0;
      end
    end
    else  begin
      div_stall_next = 1'b0;
    end

    jump_to_pc = f_pc_current + 4;

    mem_addr_raw = 32'h0;
    mem_addr_base = 32'h0;
    mem_addr_offset = 2'h0;
    case (execute_state.insn_opcode)
      OpcodeLui: begin
        res_alu = {execute_state.insn[31:12], 12'b0};                
      end

      OpcodeAuipc:  begin
        res_alu = execute_state.pc + {execute_state.insn[31:12], 12'b0};
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
            // mul
            else if(execute_state.insn_funct7 == 7'h1)  begin
              mul_temp = alu_data_rs1 * alu_data_rs2;
              res_alu = mul_temp[31:0];
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
            //mulh
            else if(execute_state.insn_funct7 == 7'h1)  begin
              mul_temp = $signed(alu_data_rs1) * $signed(alu_data_rs2);
              res_alu = mul_temp[63:32];
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
            // mulhsu
            else if(execute_state.insn_funct7 == 7'h1)  begin
              rs1_abs = alu_data_rs1[31] ? (~alu_data_rs1 + 1) : alu_data_rs1;
              mul_abs = rs1_abs * $unsigned(alu_data_rs2);
              mul_temp = ~mul_abs + 1;  
              res_alu = alu_data_rs1[31] ? mul_temp[63:32] : mul_abs[63:32]; 
            end
            else  begin
            end
          end

          3'b011: begin
            //sltu
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu  = ($unsigned(alu_data_rs1) < $unsigned(alu_data_rs2)) ? 32'd1 : 32'd0;
            end
            // mulhu
            else if(execute_state.insn_funct7 == 7'h1)  begin
              mul_temp = $unsigned(alu_data_rs1) * $unsigned(alu_data_rs2);
              res_alu = mul_temp[63:32]; 
            end
            else  begin
            end
          end

          3'b100: begin
            //xor
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = alu_data_rs1 ^ alu_data_rs2;
            end
            // div
            else if(execute_state.insn_funct7 == 7'h1)  begin
              pos_neg = alu_data_rs1[31] ^ alu_data_rs2[31];
              div_dividend = alu_data_rs1[31] ? (~alu_data_rs1 + 1) : alu_data_rs1;
              div_dividor = alu_data_rs2[31] ? (~alu_data_rs2 + 1) : alu_data_rs2;
              if(alu_data_rs2 == 32'd0) begin
                res_alu = div_quotient;
              end
              else  begin
                res_alu = pos_neg ? (~div_quotient + 1) : div_quotient;
              end
            end
            else  begin
            end
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
            //divu
            else if(execute_state.insn_funct7 == 7'd1)  begin
              div_dividend = alu_data_rs1;
              div_dividor = alu_data_rs2;

              if(alu_data_rs2 == 32'h0) begin
                res_alu = 32'hFFFFFFFF; 
              end
              else  begin
                res_alu = div_quotient;
              end
            end
            else  begin
              illegal_insn = 1'b1;
            end
          end         

          3'b110: begin
            //or
            if(execute_state.insn_funct7 == 7'h0) begin
              res_alu = alu_data_rs1 | alu_data_rs2;
            end

            //rem
            else if(execute_state.insn_funct7 == 7'd1)  begin
              div_dividend = alu_data_rs1[31] ? (~alu_data_rs1 + 1) : alu_data_rs1;
              div_dividor = alu_data_rs2[31] ? (~alu_data_rs2 + 1) : alu_data_rs2;

              if(alu_data_rs2 == 32'd0) begin
                res_alu = alu_data_rs1;
              end
              else  begin
                res_alu = alu_data_rs1[31] ? (~div_remainder + 1) : div_remainder;
              end
            end

            else  begin
              illegal_insn = 1'b1;
            end
          end

          3'b111: begin
            //and
            if(execute_state.insn_funct7 == 7'd0) begin
              res_alu = alu_data_rs1 & alu_data_rs2;
            end

            //remu
            else if(execute_state.insn_funct7 == 7'd1)  begin
              div_dividend = alu_data_rs1;
              div_dividor = alu_data_rs2;

              if (alu_data_rs2 == 32'd0) begin
                res_alu = alu_data_rs1;
              end else begin
                res_alu = div_remainder;
              end
            end

            else  begin
              illegal_insn = 1'b1;
            end
          end

          default:  begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      OpcodeJal:  begin
        flush = 1'b1;
        res_alu = execute_state.pc + 4;
        jump_to_pc = execute_state.pc + jal_imm;
      end

      OpcodeJalr: begin
        flush = 1'b1;
        res_alu = execute_state.pc + 4;
        jump_to_pc = (alu_data_rs1 + reg_imm32) & ~32'h1;
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
    else if(div_stall_curr || div_stall_next || load_stall_next)  begin
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
        cycle_status: (load_stall_next) ? CYCLE_LOAD2USE : CYCLE_DIV2USE
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

    if(memory_state.insn_opcode == OpcodeLoad)  begin
      if(execute_state.insn_opcode != OpcodeStore)  begin
        if(memory_state.insn_rd == execute_state.insn_rs1 && x_rs1_make_sense)  begin
          load_stall_next = (load_stall_curr == 1'b0) ? 1'b1 : 1'b0;
        end
        else if(memory_state.insn_rd == execute_state.insn_rs2 && x_rs2_make_sense) begin
          load_stall_next = (load_stall_curr == 1'b0) ? 1'b1 : 1'b0;
        end
        else begin
          load_stall_next = 1'b0;
        end
      end
      else  begin
        if(memory_state.insn_rd == execute_state.insn_rs1 && x_rs1_make_sense)  begin
          load_stall_next = (load_stall_curr == 1'b0) ? 1'b1 : 1'b0;
        end
        else  begin
          load_stall_next = 1'b0;
        end
      end
    end
    else  begin
      load_stall_next = 1'b0;
    end

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
    else if(div_stall_curr) begin
      writeback_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        insn_opcode: execute_state.insn_opcode,
        insn_rd: execute_state.insn_rd,
        data_rd: res_alu,
        illegal_insn: illegal_insn,
        cycle_status: execute_state.cycle_status
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

  assign regfile_we = (writeback_state.insn == 32'h0 || writeback_state.insn_opcode == 7'h63 || writeback_state.cycle_status == CYCLE_TAKEN_BRANCH || writeback_state.insn_opcode == OpcodeStore || writeback_state.insn_opcode == OpcodeBranch || writeback_state.insn_opcode == OpcodeMiscMem || writeback_state.insn_opcode == OpcodeEnviron) ? 1'b0 : 1'b1;
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




  // TODO: your code here

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

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
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // remove imem
      // // imem is read-only
      // .pc_to_imem         (pc_to_imem),
      // .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  // HW6 memory interface
  axi_clkrst_if axi_cr (.ACLK(clk), .ARESETn(~rst));
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(.NUM_WORDS(8192)) mem (
    .axi(axi_cr),
    .insn(axi_insn.subord),
    .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      // .dmem(axi_data.manager),

      // change these interfaces to .dmem once alu and branches are implemented
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we),
      //

      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
