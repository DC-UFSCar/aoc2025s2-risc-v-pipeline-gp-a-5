module riscvpipeline (
    input        clk,
    input        reset,
    output [31:0] PC,
    input  [31:0] Instr,
    output [31:0] Address,
    output [31:0] WriteData,
    output        MemWrite,
    input  [31:0] ReadData
);

   /* The 10 "recognizers" for the 10 codeops */
   function isALUreg; input [31:0] I; isALUreg=(I[6:0]==7'b0110011); endfunction
   function isALUimm; input [31:0] I; isALUimm=(I[6:0]==7'b0010011); endfunction
   function isBranch; input [31:0] I; isBranch=(I[6:0]==7'b1100011); endfunction
   function isJALR;   input [31:0] I; isJALR  =(I[6:0]==7'b1100111); endfunction
   function isJAL;    input [31:0] I; isJAL   =(I[6:0]==7'b1101111); endfunction
   function isAUIPC;  input [31:0] I; isAUIPC =(I[6:0]==7'b0010111); endfunction
   function isLUI;    input [31:0] I; isLUI   =(I[6:0]==7'b0110111); endfunction
   function isLoad;   input [31:0] I; isLoad  =(I[6:0]==7'b0000011); endfunction
   function isStore;  input [31:0] I; isStore =(I[6:0]==7'b0100011); endfunction
   function isSYSTEM; input [31:0] I; isSYSTEM=(I[6:0]==7'b1110011); endfunction

   /* Register indices */
   function [4:0] rs1Id; input [31:0] I; rs1Id = I[19:15];      endfunction
   function [4:0] rs2Id; input [31:0] I; rs2Id = I[24:20];      endfunction
   function [4:0] shamt; input [31:0] I; shamt = I[24:20];      endfunction
   function [4:0] rdId;  input [31:0] I; rdId  = I[11:7];       endfunction
   function [1:0] csrId; input [31:0] I; csrId = {I[27],I[21]}; endfunction

   /* funct3 and funct7 */
   function [2:0] funct3; input [31:0] I; funct3 = I[14:12]; endfunction
   function [6:0] funct7; input [31:0] I; funct7 = I[31:25]; endfunction

   /* EBREAK and CSRRS instruction "recognizers" */
   function isEBREAK; input [31:0] I; isEBREAK = (isSYSTEM(I) && funct3(I) == 3'b000); endfunction

   /* The 5 immediate formats */
   function [31:0] Uimm; input [31:0] I; Uimm={I[31:12],{12{1'b0}}}; endfunction
   function [31:0] Iimm; input [31:0] I; Iimm={{21{I[31]}},I[30:20]}; endfunction
   function [31:0] Simm; input [31:0] I; Simm={{21{I[31]}},I[30:25],I[11:7]}; endfunction
   function [31:0] Bimm; input [31:0] I; Bimm = {{20{I[31]}},I[7],I[30:25],I[11:8],1'b0}; endfunction
   function [31:0] Jimm; input [31:0] I; Jimm = {{12{I[31]}},I[19:12],I[20],I[30:21],1'b0}; endfunction

   /* Read/Write tests */
   function writesRd; input [31:0] I; writesRd = !isStore(I) && !isBranch(I); endfunction
   function readsRs1; input [31:0] I; readsRs1 = !(isJAL(I) || isAUIPC(I) || isLUI(I)); endfunction
   function readsRs2; input [31:0] I; readsRs2 = isALUreg(I) || isBranch(I) || isStore(I); endfunction

/**********************  F: Instruction fetch *********************************/
   localparam NOP = 32'b0000000_00000_00000_000_00000_0110011;

   reg [31:0] F_PC;
   reg [31:0] FD_PC;
   reg [31:0] FD_instr;
   reg        FD_nop;

   assign PC = F_PC;

   /** These two signals come from the Execute stage **/
   wire [31:0] jumpOrBranchAddress;
   wire        jumpOrBranch;

   // Hazard sinal usado em F e calculado em D
   wire loadUseHazard;

   always @(posedge clk) begin
      if (reset) begin
         F_PC     <= 32'b0;
         FD_PC    <= 32'b0;
         FD_instr <= NOP;
         FD_nop   <= 1'b1;
      end else begin
         if (jumpOrBranch) begin
            // Flush em desvio/salto tomado
            F_PC     <= jumpOrBranchAddress;
            FD_PC    <= 32'b0;
            FD_instr <= NOP;
            FD_nop   <= 1'b1;
         end else begin
            FD_nop <= 1'b0;

            // Stall em hazard de load-use: congela F_PC e FD_*
            if (!loadUseHazard) begin
               FD_instr <= Instr;
               FD_PC    <= F_PC;
               F_PC     <= F_PC + 4;
            end
         end
      end
   end

/************************ D: Instruction decode *******************************/
   reg [31:0] DE_PC;
   reg [31:0] DE_instr;
   reg [31:0] DE_rs1;
   reg [31:0] DE_rs2;

   /* These three signals come from the Writeback stage */
   wire        writeBackEn;
   wire [31:0] writeBackData;
   wire [4:0]  wbRdId;

   reg [31:0] RegisterBank [0:31];

   // IDs dos registradores da instrução em FD
   wire [4:0] FD_rs1Id = rs1Id(FD_instr);
   wire [4:0] FD_rs2Id = rs2Id(FD_instr);

   // Bypass do writeback para leitura na mesma borda de clock
   wire [31:0] rs1Val_base = FD_rs1Id ? RegisterBank[FD_rs1Id] : 32'b0;
   wire [31:0] rs2Val_base = FD_rs2Id ? RegisterBank[FD_rs2Id] : 32'b0;

   wire [31:0] rs1Val =
      (writeBackEn && (wbRdId != 0) && (wbRdId == FD_rs1Id)) ? writeBackData
                                                             : rs1Val_base;

   wire [31:0] rs2Val =
      (writeBackEn && (wbRdId != 0) && (wbRdId == FD_rs2Id)) ? writeBackData
                                                             : rs2Val_base;

   // Hazard de load-use: load em DE_instr, consumidor em FD_instr
   assign loadUseHazard =
      isLoad(DE_instr) && (rdId(DE_instr) != 0) && (
        (readsRs1(FD_instr) && (FD_rs1Id == rdId(DE_instr))) ||
        (readsRs2(FD_instr) && (FD_rs2Id == rdId(DE_instr)))
      );

   always @(posedge clk) begin
      if (reset) begin
         DE_PC    <= 32'b0;
         DE_instr <= NOP;
         DE_rs1   <= 32'b0;
         DE_rs2   <= 32'b0;
      end else begin
         DE_PC <= FD_PC;

         if (jumpOrBranch) begin
            // Flush da instrução em D
            DE_instr <= NOP;
            DE_rs1   <= 32'b0;
            DE_rs2   <= 32'b0;
         end else if (loadUseHazard) begin
            // Stall: injeta bolha na etapa E (NOP em DE)
            DE_instr <= NOP;
            DE_rs1   <= 32'b0;
            DE_rs2   <= 32'b0;
         end else begin
            // Caminho normal: decodifica FD_instr
            DE_instr <= FD_nop ? NOP : FD_instr;
            DE_rs1   <= rs1Val;
            DE_rs2   <= rs2Val;
         end

         // Escrita no banco de registradores
         if (writeBackEn)
            RegisterBank[wbRdId] <= writeBackData;
      end
   end

/************************ E: Execute *****************************************/
   reg [31:0] EM_PC;
   reg [31:0] EM_instr;
   reg [31:0] EM_rs2;
   reg [31:0] EM_Eresult;
   reg [31:0] EM_addr;

   // IDs dos registradores da instrução em E
   wire [4:0] E_rs1Id = rs1Id(DE_instr);
   wire [4:0] E_rs2Id = rs2Id(DE_instr);

   // Sinais de escrita em rd nos estágios seguintes
   wire EM_writesRd = writesRd(EM_instr) && (rdId(EM_instr) != 0);
   wire MW_writesRd;

   // Forwarding para rs1 / rs2 na etapa E
   wire [31:0] E_rs1_fwd;
   wire [31:0] E_rs2_fwd;

   // Declarações das coisas de M/W (necessário para usar aqui)
   // Elas serão definidas mais abaixo, mas em Verilog a ordem de assign não importa
   reg [31:0] MW_PC;
   reg [31:0] MW_instr;
   reg [31:0] MW_Eresult;
   reg [31:0] MW_addr;
   reg [31:0] MW_Mdata;
   reg [31:0] MW_IOresult;
   reg [31:0] MW_CSRresult;

   assign MW_writesRd = writesRd(MW_instr) && (rdId(MW_instr) != 0);

   // Caminhos de forwarding:
   assign E_rs1_fwd =
      // EX/MEM (resultado em EM_Eresult), exceto load (load trata via stall)
      (EM_writesRd && !isLoad(EM_instr) && (rdId(EM_instr) == E_rs1Id)) ? EM_Eresult :
      // MEM/WB (resultado que vai para writebackData)
      (MW_writesRd && (rdId(MW_instr) == E_rs1Id)) ? writeBackData :
      DE_rs1;

   assign E_rs2_fwd =
      (EM_writesRd && !isLoad(EM_instr) && (rdId(EM_instr) == E_rs2Id)) ? EM_Eresult :
      (MW_writesRd && (rdId(MW_instr) == E_rs2Id)) ? writeBackData :
      DE_rs2;

   wire [31:0] E_aluIn1 = E_rs1_fwd;
   wire [31:0] E_aluIn2 = isALUreg(DE_instr) | isBranch(DE_instr) ? E_rs2_fwd : Iimm(DE_instr);
   wire [4:0]  E_shamt  = isALUreg(DE_instr) ? E_rs2_fwd[4:0] : shamt(DE_instr);
   wire        E_minus  = DE_instr[30] & isALUreg(DE_instr);
   wire        E_arith_shift = DE_instr[30];

   // The adder is used by both arithmetic instructions and JALR.
   wire [31:0] E_aluPlus = E_aluIn1 + E_aluIn2;

   // Use a single 33 bits subtract to do subtraction and all comparisons
   wire [32:0] E_aluMinus = {1'b1, ~E_aluIn2} + {1'b0,E_aluIn1} + 33'b1;
   wire        E_LT  = (E_aluIn1[31] ^ E_aluIn2[31]) ? E_aluIn1[31] : E_aluMinus[32];
   wire        E_LTU = E_aluMinus[32];
   wire        E_EQ  = (E_aluMinus[31:0] == 0);

   // Flip a 32 bit word. Used by the shifter
   function [31:0] flip32;
      input [31:0] x;
      flip32 = {x[ 0], x[ 1], x[ 2], x[ 3], x[ 4], x[ 5], x[ 6], x[ 7],
                x[ 8], x[ 9], x[10], x[11], x[12], x[13], x[14], x[15],
                x[16], x[17], x[18], x[19], x[20], x[21], x[22], x[23],
                x[24], x[25], x[26], x[27], x[28], x[29], x[30], x[31]};
   endfunction

   wire [31:0] E_shifter_in = funct3(DE_instr) == 3'b001 ? flip32(E_aluIn1) : E_aluIn1;
   wire [31:0] E_shifter    = $signed({E_arith_shift & E_aluIn1[31], E_shifter_in}) >>> E_aluIn2[4:0];
   wire [31:0] E_leftshift  = flip32(E_shifter);

   reg [31:0] E_aluOut;
   always @(*) begin
      case(funct3(DE_instr))
         3'b000: E_aluOut = E_minus ? E_aluMinus[31:0] : E_aluPlus;
         3'b001: E_aluOut = E_leftshift;
         3'b010: E_aluOut = {31'b0, E_LT};
         3'b011: E_aluOut = {31'b0, E_LTU};
         3'b100: E_aluOut = E_aluIn1 ^ E_aluIn2;
         3'b101: E_aluOut = E_shifter;
         3'b110: E_aluOut = E_aluIn1 | E_aluIn2;
         3'b111: E_aluOut = E_aluIn1 & E_aluIn2;
      endcase
   end

   /*********** Branch, JAL, JALR ***********************************/
   reg E_takeBranch;
   always @(*) begin
      case (funct3(DE_instr))
         3'b000: E_takeBranch = E_EQ;
         3'b001: E_takeBranch = !E_EQ;
         3'b100: E_takeBranch = E_LT;
         3'b101: E_takeBranch = !E_LT;
         3'b110: E_takeBranch = E_LTU;
         3'b111: E_takeBranch = !E_LTU;
         default: E_takeBranch = 1'b0;
      endcase
   end

   wire E_JumpOrBranch = (
         isJAL(DE_instr)  ||
         isJALR(DE_instr) ||
         (isBranch(DE_instr) && E_takeBranch)
   );

   wire [31:0] E_JumpOrBranchAddr =
        isBranch(DE_instr) ? DE_PC + Bimm(DE_instr) :
        isJAL(DE_instr)    ? DE_PC + Jimm(DE_instr) :
        /* JALR */           {E_aluPlus[31:1],1'b0} ;

   wire [31:0] E_result =
        (isJAL(DE_instr) | isJALR(DE_instr)) ? DE_PC+4                :
        isLUI(DE_instr)                      ? Uimm(DE_instr)         :
        isAUIPC(DE_instr)                    ? DE_PC + Uimm(DE_instr) :
                                              E_aluOut               ;

   always @(posedge clk) begin
      EM_PC      <= DE_PC;
      EM_instr   <= DE_instr;
      EM_rs2     <= E_rs2_fwd;  // valor já encaminhado para stores
      EM_Eresult <= E_result;
      EM_addr    <= isStore(DE_instr) ? E_rs1_fwd + Simm(DE_instr) :
                                        E_rs1_fwd + Iimm(DE_instr) ;
   end

/************************ M: Memory *******************************************/
   wire [2:0] M_funct3 = funct3(EM_instr);
   wire       M_isB    = (M_funct3[1:0] == 2'b00);
   wire       M_isH    = (M_funct3[1:0] == 2'b01);
   wire       halt;

   assign halt = !reset & isEBREAK(MW_instr);

   /*************** STORE **************************/
   wire [31:0] M_STORE_data = EM_rs2;
   assign Address  = EM_addr;
   assign MemWrite = isStore(EM_instr);
   assign WriteData = EM_rs2;

   always @(posedge clk) begin
      MW_PC        <= EM_PC;
      MW_instr     <= EM_instr;
      MW_Eresult   <= EM_Eresult;
      MW_Mdata     <= ReadData;
      MW_addr      <= EM_addr;
   end

/************************ W: WriteBack ****************************************/
   wire [2:0] W_funct3 = funct3(MW_instr);
   wire       W_isB    = (W_funct3[1:0] == 2'b00);
   wire       W_isH    = (W_funct3[1:0] == 2'b01);
   wire       W_sext   = !W_funct3[2];
   wire       W_isIO   = MW_addr[22];

   /*************** LOAD ****************************/
   assign writeBackData = isLoad(MW_instr) ? MW_Mdata : MW_Eresult;
   assign writeBackEn   = writesRd(MW_instr) && rdId(MW_instr) != 0;
   assign wbRdId        = rdId(MW_instr);

   assign jumpOrBranchAddress = E_JumpOrBranchAddr;
   assign jumpOrBranch        = E_JumpOrBranch;

/******************************************************************************/

   always @(posedge clk) begin
      if (halt) begin
         $writememh("regs.out", RegisterBank);
         $finish();
      end
   end
endmodule
