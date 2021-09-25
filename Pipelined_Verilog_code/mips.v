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
  wire		  re_add;
  wire        alusrc, regdst, regwrite, jump;
  wire        branch, bne;
  wire [1:0]  aluop;
  wire [31:0] new_instr;
  wire        if_memwrite;
  
  wire        signext_out, shiftl16_out, memtoreg_out;
  wire		  re_add_out;
  wire        alusrc_out, regdst_out, regwrite_out, jump_out;
  wire        branch_out, bne_out;
  wire [1:0]  aluop_out;
  wire        if_memwrite_out;
  wire [5:0]  funct_out;


  // Instantiate Controller

  controller c(
    .op         (new_instr[31:26]),
		.signext     (signext),
		.shiftl16    (shiftl16),
		.memtoreg    (memtoreg),
		.if_memwrite (if_memwrite),
		.alusrc      (alusrc),
		.regdst      (regdst),
		.regwrite    (regwrite),
		.re_add	    (re_add),
		.jump        (jump),
		.branch      (branch),
		.bne         (bne),
		.aluop       (aluop));

  // Instantiate Datapath
  datapath dp(
    .clk        (clk),
    .reset      (reset),
    .signext    (signext_out),
    .shiftl16   (shiftl16_out),
    .memtoreg   (memtoreg_out),
    .alusrc     (alusrc_out),
    .regdst     (regdst_out),
    .regwrite   (regwrite_out),
    .jump       (jump_out),
	 .re_add	    (re_add_out),
	 .instr      (instr),
    .pc         (pc),
    .aluout (memaddr), 
    .new_writedata  (memwritedata),
    .readdata   (memreaddata),
	 .new_instr  (new_instr),
	 .if_memwrite (if_memwrite_out),
	 .ex_memwrite (memwrite),
	 .aluop       (aluop_out),
	 .branch      (branch_out),
	 .bne         (bne_out),
	 .funct       (funct_out),
	 .stall       (stall));


  controlmux cm(
    .ctrlunitsrc   (stall),
	 .signext       (signext),
	 .shiftl16      (shiftl16),
	 .memtoreg      (memtoreg),
	 .if_memwrite   (if_memwrite),
	 .alusrc        (alusrc),
	 .regdst        (regdst),
	 .regwrite      (regwrite),
	 .re_add        (re_add),
	 .jump          (jump),
	 .branch        (branch),
	 .bne           (bne),
	 .aluop         (aluop),
	 .signext_out       (signext_out),
	 .shiftl16_out      (shiftl16_out),
	 .memtoreg_out      (memtoreg_out),
	 .if_memwrite_out   (if_memwrite_out),
	 .alusrc_out        (alusrc_out),
	 .regdst_out        (regdst_out),
	 .regwrite_out      (regwrite_out),
	 .re_add_out        (re_add_out),
	 .jump_out          (jump_out),
	 .branch_out        (branch_out),
	 .bne_out           (bne_out),
	 .aluop_out         (aluop_out),
	 .funct             (new_instr[5:0]),
	 .funct_out         (funct_out)
  );
  
endmodule

module controlmux(input        ctrlunitsrc,
					   input [5:0]  funct,
                  input        signext,
                  input        shiftl16,
                  input        memtoreg, if_memwrite,
                  input        alusrc,
                  input        regdst, regwrite,
						input        re_add,
                  input        jump, branch, bne,
						input  [1:0] aluop,
						output [5:0] funct_out,
                  output       signext_out,
                  output       shiftl16_out,
                  output       memtoreg_out, if_memwrite_out,
                  output       alusrc_out,
                  output       regdst_out, regwrite_out,
						output       re_add_out,
                  output       jump_out, branch_out, bne_out,
						output [1:0] aluop_out);

						
   reg [18:0] stall;
	
	assign {funct_out, signext_out, shiftl16_out, memtoreg_out, if_memwrite_out, alusrc_out, regdst_out, regwrite_out, re_add_out, jump_out, branch_out, bne_out, aluop_out} = stall;

	always@(*)
   begin
		if(ctrlunitsrc)
			begin
			stall = 19'b0000000000000000011;
			end
		else stall = {funct, signext, shiftl16, memtoreg, if_memwrite, alusrc, regdst, regwrite, re_add, jump, branch, bne, aluop};
		end		
		
endmodule

module controller(input  [5:0] op,
                  output       signext,
                  output       shiftl16,
                  output       memtoreg, if_memwrite,
                  output       alusrc, 
                  output       regdst, regwrite,
						output       re_add,
                  output       jump, branch, bne,
						output [1:0] aluop);

  maindec md(
    .op       (op),
    .signext  (signext),
    .shiftl16 (shiftl16),
    .memtoreg (memtoreg),
    .if_memwrite (if_memwrite),	
    .branch   (branch),
	 .bne      (bne),
    .alusrc   (alusrc),
    .regdst   (regdst),
    .regwrite (regwrite),
	 .re_add   (re_add),
    .jump     (jump),
    .aluop    (aluop));


endmodule

module forwarding_unit(input   [4:0]    dec_rs, dec_rt,
                       input   [4:0]    ex_rd, mem_rd,
							  input   [4:0]    if_rs, if_rt,
							  input            ex_rw, mem_rw,
							  output  [1:0]    forwardA, forwardB,
							  output           forwardWB_rs, forwardWB_rt);
	
	assign forwardA[1] = (dec_rs  == ex_rd)&&(ex_rw);
	assign forwardA[0] = (dec_rs == mem_rd)&&(mem_rw);
	
	assign forwardB[1] = (dec_rt  == ex_rd)&&(ex_rw);
	assign forwardB[0] = (dec_rt == mem_rd)&&(mem_rw);
	
	assign forwardWB_rs = (if_rs == mem_rd)&&(mem_rw);
	assign forwardWB_rt = (if_rt == mem_rd)&&(mem_rw);


endmodule

module hazard_detection_unit(input   [4:0]  dec_rt,
									  input   [4:0]  if_rs, if_rt,
									  input          mtr,
									  input          jump, dec_jump, pcsrc, jr, // receives jump signal to initiate hazard control
									  output         flush, // sends flush signal to ifid flip-flop
									  output         stall);
  assign stall = (mtr)&&((dec_rt==if_rt)||(dec_rt==if_rs));
  assign flush = jump || dec_jump || pcsrc || jr; // flush = 1 upon reveiving jump or branch instruction

endmodule
module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, if_memwrite,
               output       branch,
					output       bne,
					output       alusrc,
               output       regdst, regwrite,
               output       jump,
					output 		 re_add,
               output [1:0] aluop);

  reg [12:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, bne, branch, if_memwrite,
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
				  input      [5:0] op,
              input      [1:0] aluop,
              output reg [3:0] alucontrol);// add 1 bit for jr and sltu

  always @(*)
    case(aluop)
      2'b00: alucontrol <= #`mydelay 4'b0010;  // add
      2'b01: alucontrol <= #`mydelay 4'b0110;  // sub
      2'b10: alucontrol <= #`mydelay 4'b0001;  // or
		default: case(op)
			 6'b001010: alucontrol <= #`mydelay 4'b0111; // SLT
      default: case(funct)          // RTYPE
          6'b100000,
			 6'b001000, //jr
          6'b100001: alucontrol <= #`mydelay 4'b0010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 4'b0110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 4'b0000; // AND
          6'b100101: alucontrol <= #`mydelay 4'b0001; // OR
          6'b101010: alucontrol <= #`mydelay 4'b0111; // SLT
			 6'b101011: alucontrol <= #`mydelay 4'b1111; // SLTU
          default:   alucontrol <= #`mydelay 4'b1010; // ???
        endcase
    endcase
	 endcase
    
endmodule

module datapath(input         clk, reset,
                input         signext, re_add,
                input         shiftl16,
                input         memtoreg,
                input         alusrc, regdst,
                input         regwrite, jump, branch, bne,
					 input         if_memwrite,
					 output        ex_memwrite,
                output [31:0] pc,
                output [31:0] aluout, new_writedata,
                input  [31:0] readdata,
					 input  [31:0] instr,
					 output [31:0] new_instr,
					 input [1:0]  aluop,
					 input [5:0]  funct,
					 output       stall);
					 
	
 
  wire [4:0]  writereg, writereg_ra; 
  wire [31:0] pcnext, pcnextbr, pcnextjr, pcbranch;
  wire [31:0] pcplus4; //
  wire [31:0] signimm, signimmsh, shiftedimm;
  wire [31:0] srca, srcb;
  wire [31:0] result, result_ra;
  wire        shift, jr;	
  wire [31:0] se_b;
  wire [31:0] rf_b;
  wire [31:0] new_a;
  wire [31:0] alures;
  wire [31:0] if_pc;
  wire [31:0] dec_pc;
  wire [31:0] ex_ja;
  wire [31:0] dec_ja;
  wire [31:0] reg_b;
  wire [31:0] mem_aluout;
  wire [31:0] mem_readdata;
  wire [31:0] dec_instr;
  wire [4:0]  ex_writereg;
  wire [4:0]  mem_writereg;
  wire [31:0] ex_pc;
  wire [31:0] mem_pc;
  wire [3:0] alucontrol;
  wire [1:0]  dec_aluop;
  wire [31:0] forwarded_srca;
  wire [31:0] forwarded_srcb;
  wire [1:0]  forwardA;
  wire [1:0]  forwardB;
  wire pcsrc;
  wire [5:0]  dec_funct;
  wire        dec_br, dec_br_not;
  assign jr = (dec_instr[31:26] == 6'b000000)&&(se_b[5:0]==6'b001000);
  wire [31:0] wb_rs, wb_rt;
	
  
  aludec ad( 
    .funct      (dec_funct[5:0]),
	 .op         (dec_instr[31:26]),
    .aluop      (dec_aluop), 
    .alucontrol (alucontrol)); 
 
	fetch_ff ifid(   //
	  .instr     (instr),
	  .pcplus4   (pcplus4),
	  .clk       (clk),
	  .reset		 (reset),
	  .new_instr (new_instr),
	  .flush     (flush), // receivese flush signal
	  .if_pc     (if_pc),
	  .stall     (stall)); 
 
   decode_ff idex(   //
	  .clk         (clk),
	  .reset	  	   (reset),
	  .srca        (srca),
	  .reg_b       (reg_b),
	  .rf_b        (rf_b),
	  .shiftedimm  (shiftedimm),
	  .se_b        (se_b),
	  .new_a       (new_a),
	  .memtoreg    (memtoreg),
	  .mtr         (mtr),
	  .alusrc      (alusrc),
	  .alusource   (alusource),
	  .regwrite    (regwrite),
	  .dec_rw      (dec_rw),
	  .if_pc       (if_pc),
	  .dec_pc      (dec_pc),
	  .new_instr   (new_instr),
	  .dec_instr   (dec_instr),
	  .dec_ja      (dec_ja),
	  .re_add      (re_add),
	  .dec_readd   (dec_readd),
	  .regdst      (regdst),
	  .dec_regdst  (dec_regdst),
	  .jump        (jump),
	  .dec_jump    (dec_jump),
	  .if_memwrite (if_memwrite),
	  .dec_memwrite (dec_memwrite),
	  .aluop       (aluop),
	  .funct       (funct),
	  .dec_funct   (dec_funct),
	  .dec_aluop   (dec_aluop),
	  .bne         (bne),
	  .dec_br_not  (dec_br_not),
	  .branch      (branch),
	  .dec_br      (dec_br)
	  //.pcsrc       (pcsrc),
	  //.dec_pcsrc   (dec_pcsrc)
	  );

  assign pcsrc = dec_br_not&~(forwarded_srca==forwarded_srcb) | dec_br&(forwarded_srca==forwarded_srcb);	   
  execution_ff exmem(   //
	  .clk          (clk),
	  .reset	  	    (reset),
	  .alures       (alures),
	  .aluout       (aluout),
	  .rf_b         (forwarded_srcb),
	  .new_writedata(new_writedata),
	  .dec_rw       (dec_rw),
	  .ex_rw        (ex_rw),
	  .mtr          (mtr),
	  .mtrsig       (mtrsig),
	  .dec_readd    (dec_readd),
	  .ex_readd     (ex_readd),
	  .writereg     (writereg),
	  .ex_writereg  (ex_writereg),
	  /*.jr           (jr),
	  .ex_jr        (ex_jr),*/
	  .dec_memwrite (dec_memwrite),
	  .ex_memwrite  (ex_memwrite),
	  .dec_pc       (dec_pc),
	  .ex_pc        (ex_pc));
	  
  memory_ff memwb(
     .clk          (clk),
	  .reset        (reset),
	  .readdata     (readdata),
	  .aluout       (aluout),
	  .mem_readdata (mem_readdata),
	  .mem_aluout   (mem_aluout),
	  .mtrsig       (mtrsig),
	  .memtoregsig  (memtoregsig),
	  .ex_readd     (ex_readd),
	  .mem_readd    (mem_readd),
	  .ex_rw        (ex_rw),
	  .mem_rw       (mem_rw),
	  .ex_writereg  (ex_writereg),
	  .mem_writereg (mem_writereg),
	  .ex_pc        (ex_pc),
	  .mem_pc       (mem_pc));
  // next PC logic

  forwarding_unit fu(
    .if_rs         (new_instr[25:21]),
	 .if_rt         (new_instr[20:16]),
    .dec_rs        (dec_instr[25:21]),
	 .dec_rt        (dec_instr[20:16]),
	 .ex_rd         (ex_writereg),
	 .mem_rd        (mem_writereg),
	 .ex_rw         (ex_rw),
	 .mem_rw        (mem_rw),
	 .forwardA      (forwardA),
	 .forwardB      (forwardB),
	 .forwardWB_rs  (forwardWB_rs),
	 .forwardWB_rt  (forwardWB_rt));
	 
  hazard_detection_unit hdu(
    .dec_rt        (dec_instr[20:16]),
	 .if_rs         (new_instr[25:21]),
	 .if_rt         (new_instr[20:16]),
	 .mtr           (mtr),
    .stall         (stall),
	 .jump          (jump),
	 .jr            (jr),
	 .pcsrc         (pcsrc),
	 .dec_jump      (dec_jump),
	 .flush         (flush));
  
  flopenr #(32) pcreg(
    .clk   (clk),
    .reset (reset),
	 .en    (~stall),
    .d     (pcnext),
    .q     (pc));
	 

  mux2 #(32) rd1_wbmux(
    .d0    (wb_rs),
	 .d1    (result),
	 .s     (forwardWB_rs),
	 .y     (srca));
	 
  mux2 #(32) rd2_wbmux(
    .d0    (wb_rt),
	 .d1    (result),
	 .s     (forwardWB_rt),
	 .y     (reg_b));


  adder pcadd1(
    .a (pc),
    .b (32'b100),
    .y (pcplus4));

  sl2 immsh(
    .a (se_b),
    .y (signimmsh));
				 
  adder pcadd2(
    .a (dec_pc), // 
    .b (signimmsh),
    .y (pcbranch));

  mux2 #(32) pcbrmux(
    .d0  (pcplus4),
    .d1  (pcbranch),
    .s   (pcsrc),
    .y   (pcnextbr));

  mux2 #(32) pcmux(
    .d0   (pcnextbr),
	 .d1   (dec_ja),
    .s    (dec_jump),
    .y    (pcnextjr));
	 

  // register file logic
  regfile rf(
    .clk     (clk),
	 .we      (mem_rw),
    .ra1     (new_instr[25:21]),
    .ra2     (new_instr[20:16]),
    .wa      (mem_writereg),
    .wd      (result),
    .rd1     (wb_rs),
    .rd2     (wb_rt));
	 

  mux2 #(5) wrmux(
    .d0  (dec_instr[20:16]),
    .d1  (dec_instr[15:11]),
    .s   (dec_regdst),
    .y   (writereg_ra));
	 
  mux2 #(5) jalmux_1(   // mux for jal
    .d0  (writereg_ra),
	 .d1  (5'b11111),
	 .s   (dec_readd),
	 .y   (writereg));
	 
  mux2 #(32) resmux(
	 .d0 (mem_aluout),
	 .d1 (mem_readdata),
    .s  (memtoregsig),
    .y  (result_ra));
  mux2 #(32) jalmux_2(  // another mux for jal
	 .d0 (result_ra),
	 .d1 (mem_pc), //
	 .s  (mem_readd),
	 .y  (result));

  sign_zero_ext sze(
    .a       (new_instr[15:0]),
    .signext (signext),
    .y       (signimm[31:0]));

  shift_left_16 sl16(
    .a         (signimm[31:0]),
    .shiftl16  (shiftl16),
    .y         (shiftedimm[31:0]));

  // ALU logic
  mux2 #(32) srcbmux(
    .d0 (forwarded_srcb),
    .d1 (se_b),
    .s  (alusource),
    .y  (srcb));
	 
  mux2 #(32) jrmux( // mux for jr
	 .d0 (pcnextjr),
	 .d1 (alures),
	 .s  (jr),
	 .y  (pcnext));
             
  alu alu(
    .a       (forwarded_srca),
    .b       (srcb),
    .alucont (alucontrol),
    .result  (alures));
	 
  mux3 #(32) rsmux(
    .d0      (new_a),
	 .d1      (result),
	 .d2      (aluout),
	 .s       (forwardA),
	 .y       (forwarded_srca));
  
  mux3 #(32) rtmux(
    .d0      (rf_b),
	 .d1      (result),
	 .d2      (aluout),
	 .s       (forwardB),
	 .y       (forwarded_srcb));

endmodule

module fetch_ff (input  [31:0]   instr,  //
					  input  [31:0]   pcplus4,
					  input           clk, reset,
					  input           stall, flush, // receives flush
					  output [31:0]   new_instr,
					  output [31:0]   if_pc);
					  
					  
  flopr_flush #(32) if_ff (   // if flush = 1 inst = 0
    .clk   (clk),
	 .reset (reset),
	 .en    (~stall),
	 .flush (flush),
	 .d     (instr[31:0]),
	 .q     (new_instr));

  flopenr #(32) pc_ff (   // pc is unchanged
    .clk   (clk),
	 .reset (reset),
	 .en    (~stall),
	 .d     (pcplus4),
	 .q     (if_pc));
	
endmodule

module decode_ff (input  [31:0]  srca,  // this is execution stage where all the jump or branch instructions are executed
				      input  [31:0]  reg_b,
						input  [31:0]  shiftedimm,
						input          clk, reset,
						

                  input       memtoreg,
                  input       alusrc,
                  input       regwrite,
						

                  output       mtr,
                  output       alusource,
                  output       dec_rw,
						
						output [31:0]  new_a,
						output [31:0]  se_b,
						output [31:0]  rf_b,
						
						input  [31:0]  if_pc,
						output [31:0]  dec_pc,
						input          re_add,
						output         dec_readd,
						input  [31:0]  new_instr,
						output [31:0]  dec_instr,
						output [31:0]  dec_ja,
						input          regdst,
						output         dec_regdst,
						input          jump,
						output         dec_jump,
						input          if_memwrite,
						output         dec_memwrite,
						input  [1:0]   aluop,
						output [1:0]   dec_aluop,
						input  [5:0]        funct,
						output [5:0]        dec_funct,
						input          bne, branch,
						output         dec_br_not, dec_br);
						/*input          pcsrc,
						output         dec_pcsrc*/
						
	 
flopr #(32) dec_a (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (srca),
	 .q     (new_a));
	 
  flopr #(32) dec_rf_b (//
    .clk   (clk),
	 .reset (reset),
	 .d     (reg_b),
	 .q     (rf_b));
	 
  flopr #(32) dec_se_b (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (shiftedimm),
	 .q     (se_b));

flopr #(1) dec_memtoreg (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (memtoreg),
	 .q     (mtr));

flopr #(1) dec_alusrc (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (alusrc),
	 .q     (alusource));
/*
flopr #(1) dec_branchsource (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (pcsrc),
	 .q     (dec_pcsrc));
	 
*/
flopr #(1) dec_bn (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (bne),
	 .q     (dec_br_not));
	 
flopr #(1) dec_branch (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (branch),
	 .q     (dec_br));
	 
flopr #(1) dec_regwrite (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (regwrite),
	 .q     (dec_rw));


flopr #(32) dec_programcounter (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (if_pc),
	 .q     (dec_pc));
	 
flopr #(1) dec_readdress (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (re_add),
	 .q     (dec_readd));
	 
flopr #(32) dec_jumpadd (   //
    .clk   (clk),
	 .reset (reset),
	 .d     ({if_pc[31:28],new_instr[25:0],2'b00}),
	 .q     (dec_ja));
	 
flopr #(32) dec_instruction (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (new_instr),
	 .q     (dec_instr));
 
 flopr #(1) dec_regdestination (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (regdst),
	 .q     (dec_regdst));

 flopr #(1) dec_j (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (jump),
	 .q     (dec_jump));

 flopr #(1) dec_mw (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (if_memwrite),
	 .q     (dec_memwrite));
	
 flopr #(6) dec_function (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (funct),
	 .q     (dec_funct));
	 
 flopr #(2) dec_aluopcode (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (aluop),
	 .q     (dec_aluop));

endmodule

module execution_ff (input  [31:0]  alures,
							input          clk, reset,
						   input  [31:0]  rf_b,
							output [31:0]  aluout,
							output [31:0]  new_writedata,
							input          mtr,
							output         mtrsig,
							input          dec_readd,
							output         ex_readd,
							input          dec_rw,
							output         ex_rw,
							input  [4:0]   writereg,
							output [4:0]   ex_writereg,
							/*input          jr,
							output         ex_jr,*/
							input          dec_memwrite,
						   output         ex_memwrite,
							input  [31:0]  dec_pc,
							output [31:0]  ex_pc);
							
							
flopr #(32) ex_res (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (alures),
	 .q     (aluout));

flopr #(1) ex_mtrsignal (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (mtr),
	 .q     (mtrsig));
	 
flopr #(1) ex_readdress (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (dec_readd),
	 .q     (ex_readd));
	 
flopr #(32) ex_writedata (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (rf_b),
	 .q     (new_writedata));
	 

flopr #(1) ex_regwrite (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (dec_rw),
	 .q     (ex_rw));	 

flopr #(5) ex_wr (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (writereg),
	 .q     (ex_writereg));	 
	 /*
flopr #(1) ex_jumpreturn (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (jr),
	 .q     (ex_jr));	
*/
flopr #(1) ex_mw (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (dec_memwrite),
	 .q     (ex_memwrite));		
	
flopr #(32) ex_programcounter (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (dec_pc),
	 .q     (ex_pc));
	
endmodule

module memory_ff(input    [31:0]  readdata,
                 input    [31:0]  aluout,
					  input            clk, reset,
					  output   [31:0]  mem_readdata,
					  output   [31:0]  mem_aluout,
					  input            mtrsig,
					  output           memtoregsig,
					  input            ex_readd,
					  output           mem_readd,
					  input            ex_rw,
					  output           mem_rw,
					  input    [4:0]   ex_writereg,
					  output   [4:0]   mem_writereg,
					  input    [31:0]  ex_pc,
					  output   [31:0]  mem_pc);
					  
flopr #(32) mem_read (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (readdata),
	 .q     (mem_readdata));

flopr #(32) mem_res (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (aluout),
	 .q     (mem_aluout));
	 
flopr #(1) mem_mtr (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (mtrsig),
	 .q     (memtoregsig));
	 
flopr #(1) mem_readdress (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (ex_readd),
	 .q     (mem_readd));
 
flopr #(1) mem_regwrite (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (ex_rw),
	 .q     (mem_rw));
	
flopr #(5) mem_wr (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (ex_writereg),
	 .q     (mem_writereg));

flopr #(32) mem_programcounter (   //
    .clk   (clk),
	 .reset (reset),
	 .d     (ex_pc),
	 .q     (mem_pc));

endmodule
