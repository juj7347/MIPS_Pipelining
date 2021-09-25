`timescale 1ns/1ps
`define mydelay 1

//--------------------------------------------------------------
// mips.v
// David_Harris@hmc.edu and Sarah_Harris@hmc.edu 23 October 2005
// Single-cycle MIPS processor
//--------------------------------------------------------------

// single-cycle MIPS processor
//
module mips(input         clk, reset,
            output [31:0] pc,
            input  [31:0] instr,
            output        memwrite,
            output [31:0] memaddr,
            output [31:0] memwritedata,
            input  [31:0] memreaddata);

  wire        signext, shiftl16, memtoreg;
  wire        pcsrc, zero;
  wire		  re_add;
  wire        alusrc, regdst, regwrite, jump;
  wire [3:0]  alucontrol;

  // Instantiate Controller
  controller c(
    .op         (instr[31:26]), 
		.funct      (instr[5:0]), 
		.zero       (zero),
		.signext    (signext),
		.shiftl16   (shiftl16),
		.memtoreg   (memtoreg),
		.memwrite   (memwrite),
		.pcsrc      (pcsrc),
		.alusrc     (alusrc),
		.regdst     (regdst),
		.regwrite   (regwrite),
		.re_add	   (re_add),
		.jump       (jump),
		.alucontrol (alucontrol));

  // Instantiate Datapath
  datapath dp(
    .clk        (clk),
    .reset      (reset),
    .signext    (signext),
    .shiftl16   (shiftl16),
    .memtoreg   (memtoreg),
    .pcsrc      (pcsrc),
    .alusrc     (alusrc),
    .regdst     (regdst),
    .regwrite   (regwrite),
    .jump       (jump),
    .alucontrol (alucontrol),
    .zero       (zero),
	 .re_add	    (re_add),
    .pc         (pc),
    .instr      (instr),
    .aluout     (memaddr), 
    .writedata  (memwritedata),
    .readdata   (memreaddata));

endmodule

module controller(input  [5:0] op, funct,
                  input        zero,
                  output       signext,
                  output       shiftl16,
                  output       memtoreg, memwrite,
                  output       pcsrc, alusrc,
                  output       regdst, regwrite,
						output       re_add,
                  output       jump,
                  output [3:0] alucontrol);

  wire [1:0]  aluop;
  wire        branch;

  maindec md(
    .op       (op),
    .signext  (signext),
    .shiftl16 (shiftl16),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
	 .bne      (bne),
    .alusrc   (alusrc),
    .regdst   (regdst),
    .regwrite (regwrite),
	 .re_add   (re_add),
    .jump     (jump),
    .aluop    (aluop));

  aludec ad( 
    .funct      (funct),
	 .op         (op),
    .aluop      (aluop), 
    .alucontrol (alucontrol));

  assign pcsrc = bne&~zero | branch&zero;
	

endmodule


module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite,
               output       branch,
					output       bne,
					output       alusrc,
               output       regdst, regwrite,
               output       jump,
					output 		 re_add,
               output [1:0] aluop);

  reg [12:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, bne, branch, memwrite,
          memtoreg, jump, re_add, aluop} = controls;

  always @(*)
    case(op) // add 2 bits to controls signal for bne and jal. 
      6'b000000: controls <= #`mydelay 13'b0011000000011; // Rtype
      6'b100011: controls <= #`mydelay 13'b1010100010000; // LW
      6'b101011: controls <= #`mydelay 13'b1000100100000; // SW
      6'b000100: controls <= #`mydelay 13'b1000001000001; // BEQ
		6'b000101: controls <= #`mydelay 13'b1000010000001; // BNE 
      6'b001000, 
      6'b001001: controls <= #`mydelay 13'b1010100000000; // ADDI, ADDIU: only difference is exception
      6'b001101: controls <= #`mydelay 13'b0010100000010; // ORI
      6'b001111: controls <= #`mydelay 13'b0110100000000; // LUI
		6'b000011: controls <= #`mydelay 13'b0010000001100; // JAL
      6'b000010: controls <= #`mydelay 13'b0000000001000; // J
		6'b001010: controls <= #`mydelay 13'b1010100000011;// slti
      default:   controls <= #`mydelay 13'bxxxxxxxxxxxxx; // ???
    endcase

endmodule

module aludec(input      [5:0] funct,
              input      [1:0] aluop,
				  input      [5:0] op,
              output reg [3:0] alucontrol);// add 1 bit for jr and sltu

  always @(*)
    case(aluop)
      2'b00: alucontrol <= #`mydelay 4'b0010;  // add
      2'b01: alucontrol <= #`mydelay 4'b0110;  // sub
      2'b10: alucontrol <= #`mydelay 4'b0001;  // or
		default: case(op)  
			6'b001010: alucontrol <= #`mydelay 4'b0111;
      default: case(funct)          // RTYPE
		    6'b000000: alucontrol <= #`mydelay 4'b0010; // nop
          6'b100000,
          6'b100001: alucontrol <= #`mydelay 4'b0010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 4'b0110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 4'b0000; // AND
          6'b100101: alucontrol <= #`mydelay 4'b0001; // OR
			 //6'b000101, // slti
          6'b101010: alucontrol <= #`mydelay 4'b0111; // SLT
			 6'b101011: alucontrol <= #`mydelay 4'b1111; // SLTU
			 6'b001000: alucontrol <= #`mydelay 4'b1010; // JR
          default:   alucontrol <= #`mydelay 4'bxxxx; // ???
        endcase
    endcase
	 endcase
    
endmodule

module datapath(input         clk, reset,
                input         signext, re_add,
                input         shiftl16,
                input         memtoreg, pcsrc,
                input         alusrc, regdst,
                input         regwrite, jump,
                input  [3:0]  alucontrol,
                output        zero,
                output [31:0] pc,
                input  [31:0] instr,
                output [31:0] aluout, writedata,
                input  [31:0] readdata);

  wire [4:0]  writereg, writereg_ra; 
  wire [31:0] pcnext, pcnextbr, pcplus4, pcbranch, pcnextjr;
  wire [31:0] signimm, signimmsh, shiftedimm;
  wire [31:0] srca, srcb;
  wire [31:0] result, result_ra;
  wire        shift, jr;

  // next PC logic
  flopr #(32) pcreg(
    .clk   (clk),
    .reset (reset),
    .d     (pcnext),
    .q     (pc));

  adder pcadd1(
    .a (pc),
    .b (32'b100),
    .y (pcplus4));

  sl2 immsh(
    .a (signimm),
    .y (signimmsh));
				 
  adder pcadd2(
    .a (pcplus4),
    .b (signimmsh),
    .y (pcbranch));

  mux2 #(32) pcbrmux(
    .d0  (pcplus4),
    .d1  (pcbranch),
    .s   (pcsrc),
    .y   (pcnextbr));

  mux2 #(32) pcmux(
    .d0   (pcnextbr),
    .d1   ({pcplus4[31:28], instr[25:0], 2'b00}),
    .s    (jump),
    .y    (pcnextjr));
	 

  // register file logic
  regfile rf(
    .clk     (clk),
    .we      (regwrite),
    .ra1     (instr[25:21]),
    .ra2     (instr[20:16]),
    .wa      (writereg),
    .wd      (result),
    .rd1     (srca),
    .rd2     (writedata));

  mux2 #(5) wrmux(
    .d0  (instr[20:16]),
    .d1  (instr[15:11]),
    .s   (regdst),
    .y   (writereg_ra));
	 
  mux2 #(5) jalmux_1(   // mux for jal
    .d0  (writereg_ra),
	 .d1  (5'b11111),
	 .s   (re_add),
	 .y   (writereg));
	 
  mux2 #(32) resmux(
    .d0 (aluout),
    .d1 (readdata),
    .s  (memtoreg),
    .y  (result_ra));
  mux2 #(32) jalmux_2(  // another mux for jal
	 .d0 (result_ra),
	 .d1 (pcplus4),
	 .s  (re_add),
	 .y  (result));

  sign_zero_ext sze(
    .a       (instr[15:0]),
    .signext (signext),
    .y       (signimm[31:0]));

  shift_left_16 sl16(
    .a         (signimm[31:0]),
    .shiftl16  (shiftl16),
    .y         (shiftedimm[31:0]));

  // ALU logic
  mux2 #(32) srcbmux(
    .d0 (writedata),
    .d1 (shiftedimm[31:0]),
    .s  (alusrc),
    .y  (srcb));
	 
  mux2 #(32) jrmux( // mux for jr
	 .d0 (pcnextjr),
	 .d1 (aluout),
	 .s  (jr),
	 .y  (pcnext));
             
  alu alu(
    .a       (srca),
    .b       (srcb),
    .alucont (alucontrol),
    .result  (aluout),
    .zero    (zero),
	 .jr 		 (jr));
    
endmodule
