module top (	input         clk, reset,
		output [31:0] data_to_mem, address_to_mem,
		output        write_enable);

	wire [31:0] pc, instruction, data_from_mem;

	inst_mem  imem(pc[7:2], instruction);
	data_mem  dmem(clk, write_enable, address_to_mem, data_to_mem, data_from_mem);
	processor CPU(clk, reset, pc, instruction, write_enable, address_to_mem, data_to_mem, data_from_mem);
endmodule

//-------------------------------------------------------------------
module data_mem (input clk, we,
		 input  [31:0] address, wd,
		 output [31:0] rd);

	reg [31:0] RAM[63:0];

    wire [31:0]  r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
					 r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32 ;
        assign r0  = RAM [0]  ;
        assign r1  = RAM [1]  ;
        assign r2  = RAM [2]  ;
        assign r3  = RAM [3]  ;
        assign r4  = RAM [4]  ;
        assign r5  = RAM [5]  ;
        assign r6  = RAM [6]  ;
        assign r7  = RAM [7]  ;
        assign r8  = RAM [8]  ;
        assign r9  = RAM [9]  ;
        assign r10 = RAM [10] ;
        assign r11 = RAM [11] ;
        assign r12 = RAM [12] ;
        assign r13 = RAM [13] ;
        assign r14 = RAM [14] ;
        assign r15 = RAM [15] ;
        assign r16 = RAM [16] ;
        assign r17 = RAM [17] ;
        assign r18 = RAM [18] ;
        assign r19 = RAM [19] ;
        assign r20 = RAM [20] ;
        assign r21 = RAM [21] ;
        assign r22 = RAM [22] ;
        assign r23 = RAM [23] ;
        assign r24 = RAM [24] ;
        assign r25 = RAM [25] ;
        assign r26 = RAM [26] ;
        assign r27 = RAM [27] ;
        assign r28 = RAM [28] ;
        assign r29 = RAM [29] ;
        assign r30 = RAM [30] ;
        assign r31 = RAM [31] ;
        assign r32 = RAM [32] ;

	initial begin
		$readmemh ("memfile_data.hex",RAM,0,63);
	end

	assign rd=RAM[address[31:2]]; // word aligned

	always @ (posedge clk)
		if (we)
			RAM[address[31:2]]<=wd;
endmodule

//-------------------------------------------------------------------
module inst_mem (input  [5:0]  address,
		 output [31:0] rd);

	reg [31:0] RAM[63:0];
	initial begin
		$readmemh ("memfile_inst.hex",RAM,0,63);
	end
	assign rd=RAM[address]; // word aligned
endmodule

//----------------------------------------------------------------------------------
//processor
//----------------------------------------------------------------------------------

// CPU
module processor( input         clk, reset,
                  output [31:0] PC,
                  input  [31:0] instruction,
                  output        WE,
                  output [31:0] address_to_mem,
                  output [31:0] data_to_mem,
                  input  [31:0] data_from_mem
                );
                
    // goes inside PC
    reg [31:0] pc_current;
    // pc_plus_4
    wire [31:0] pc_plus_4, pc_new;

    // register file outputs
    wire [31:0] reg_1_data;

    // control unit output wires
    wire [3:0] ALUControl;
    wire reg_write_enable;
    wire ALUSrc, RegDst, MemToReg, branch, jal, jr, jump;

    // ALU output
    wire Zero;

    // sign extended output
    wire [31:0] sign_extended_address;

    // mux_1 input reg = 31
    wire [4:0] mux_1_reg31;
    // mux_1 output
    wire [4:0] mux_1_out;

    // mux_2 output
    wire [31:0] mux_2_out;

    // mux_3 output
    wire [4:0] mux_3_out;

    // mux_4 output
    wire [31:0] mux_4_out;

    // mux_5 output
    wire [31:0] mux_5_out;

    // sign extension unit
    sign_extend SE(instruction[15:0], sign_extended_address);

    // PC
    program_counter program_counter(pc_current, sign_extended_address, reg_1_data,
                       instruction[25:0], clk, reset, branch, Zero,
                       jal, jr, jump, PC, pc_new, pc_plus_4
                      );
    // register file
    register_file RF(instruction[25:21], instruction[20:16],
                     mux_1_out, mux_2_out, clk, reg_write_enable,
                     reg_1_data, data_to_mem
                    );
    // control unit
    control_unit CU(instruction[31:26], instruction[5:0],
                    instruction[10:6], ALUControl,
                    WE, reg_write_enable,
                    ALUSrc, RegDst, MemToReg,
                    branch, jal, jr, jump
                   );
    // ALU
    ALU ALU(reg_1_data, mux_4_out, ALUControl,
            address_to_mem, Zero
           );

    mux_5_bits mux_1(mux_1_reg31, mux_3_out, jal, mux_1_out);
    mux_2_1 mux_2(pc_plus_4, mux_5_out, jal, mux_2_out);
    mux_5_bits mux_3(instruction[15:11], instruction[20:16], RegDst, mux_3_out);
    mux_2_1 mux_4(sign_extended_address, data_to_mem, ALUSrc, mux_4_out);
    mux_2_1 mux_5(data_from_mem, address_to_mem, MemToReg, mux_5_out);

    assign mux_1_reg31 = 5'b11111;

    always@(*) begin
        pc_current = pc_new;
    end
endmodule

// program counter: takes current PC, sign extended address of immediate field
// clock, reset, ctrl_branch and ALUZero are needed for AND gate for branches
module program_counter(input [31:0] pc_current, sign_extended_address, jr,
                       input [25:0] jal,
                       input clk, reset, ctrl_branch, ALUZero,
                       input ctrl_jal, ctrl_jr, ctrl_jump,
                       output reg [31:0] _PC, pc_new, pc_plus_4
                      );
    reg [31:0] PC, pc_branch_address, jal_pc;
    wire [31:0] shifted_address;
    reg ANDResult;
    shift_left_2 shifter(sign_extended_address, shifted_address);
    always@(posedge clk) begin
        if(reset) PC = 0;
        else PC = pc_current;
    end
    always@(*) begin
        pc_plus_4 = PC + 4;
        pc_branch_address = shifted_address + pc_plus_4;
        jal_pc[31:28] = pc_plus_4[31:28];
        jal_pc[27:2] = jal[25:0];
        jal_pc[1:0] = 2'b00;
        ANDResult = ctrl_branch & ALUZero;
        // also works for jump
        if(ctrl_jal || ctrl_jump) pc_new = jal_pc;
        else if(ctrl_jr) pc_new = jr;
        else if(ANDResult) pc_new = pc_branch_address;
        else pc_new = pc_plus_4;
        _PC = PC;
    end
endmodule

// register file
module register_file(input [4:0] reg_1, reg_2, write_reg,
                     input [31:0] write_data,
                     input clk, write_enable,
                     output [31:0] reg_1_data, reg_2_data
                    );

    reg [31:0] registers[31:0];

    // for the first register
    assign reg_1_data = reg_1 ? registers[reg_1] : 0;
    // for the second register
    assign reg_2_data = reg_2 ? registers[reg_2] : 0;

    always@(posedge clk) begin
        // write into the write register if write enable is on
        if(write_enable) registers[write_reg] = write_data;
    end
endmodule

// Control Unit
module control_unit(input [5:0] opcode, funct,
                    input [4:0] shamt,
                    output reg [3:0] ALUControl,
                    output reg mem_write_enable,
                    output reg reg_write_enable,
                    output reg ALUSrc, RegDst,
                    output reg MemToReg,
                    output reg branch,
                    output reg jal, jr, jump
                   );

    wire [3:0] _ALUControl;
    wire [1:0] _ALUOp;
    wire _mem_write_enable, _reg_write_enable, _ALUSrc, _RegDst;
    wire _MemToReg, _branch, _jal, _jr, _jump;

    main_decoder MD(opcode, _ALUOp, _mem_write_enable, _reg_write_enable, 
                    _ALUSrc, _RegDst, _MemToReg, _branch, _jal, _jr, _jump
                   );
    
    ALU_op_decoder AD(_ALUOp, shamt, funct, _ALUControl);

    always@(*) begin
        ALUControl = _ALUControl;
        ALUSrc = _ALUSrc;
        RegDst = _RegDst;
        MemToReg = _MemToReg;
        branch = _branch;
        jump = _jump;
        jr = _jr;
        reg_write_enable = _reg_write_enable;
        mem_write_enable = _mem_write_enable;
        jal = _jal;
    end

endmodule

// Control Unit: Main Decoder
module main_decoder(input [5:0] opcode,
                    output reg [1:0] ALUOp,
                    output reg mem_write_enable,
                    output reg reg_write_enable,
                    output reg ALUSrc, RegDst,
                    output reg MemToReg,
                    output reg branch,
                    output reg jal, jr, jump
                   );

    always@(*) begin
        // lw
        if(opcode == 6'b100011) begin
            ALUOp = 2'b00;
            reg_write_enable = 1'b1;
            ALUSrc = 1'b1;
            MemToReg = 1'b1;
            mem_write_enable = 1'b0;
            branch = 1'b0;
            RegDst = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // sw
        else if(opcode == 6'b101011) begin
            ALUOp = 2'b00;
            mem_write_enable = 1'b1;
            ALUSrc = 1'b1;
            reg_write_enable = 1'b0;
            branch = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // beq
        else if(opcode == 6'b000100) begin
            ALUOp = 2'b01;
            branch = 1'b1;
            mem_write_enable = 1'b0;
            reg_write_enable = 1'b0;
            ALUSrc = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // addi
        else if(opcode == 6'b001000) begin
            ALUOp = 2'b00;
            reg_write_enable = 1'b1;
            ALUSrc = 1'b1;
            mem_write_enable = 1'b0;
            branch = 1'b0;
            RegDst = 1'b0;
            MemToReg = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // jal
        else if(opcode == 6'b000011) begin
            reg_write_enable = 1'b1;
            jal = 1'b1;
            mem_write_enable = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // jr
        else if(opcode == 6'b000111) begin 
            jr = 1'b1;
            reg_write_enable = 1'b0;
            mem_write_enable = 1'b0;
            jal = 1'b0;
            jump = 1'b0;
        end
        // jump
        else if(opcode == 6'b000010) begin
            jump = 1'b1;
            jal = 1'b0;
            jr = 1'b0;
            mem_write_enable = 1'b0;
            reg_write_enable = 1'b0;
        end
        // all R-type instructions
        else if(opcode == 6'b000000) begin
            ALUOp = 2'b10;
            reg_write_enable = 1'b1;
            RegDst = 1'b1;
            mem_write_enable = 1'b0;
            branch = 1'b0;
            ALUSrc = 1'b0;
            MemToReg = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
        // addu[_s].qb
        else if(opcode == 6'b011111) begin
            ALUOp = 2'b11;
            reg_write_enable = 1'b1;
            RegDst = 1'b1;
            ALUSrc = 1'b0;
            branch = 1'b0;
            mem_write_enable = 1'b0;
            MemToReg = 1'b0;
            jal = 1'b0;
            jr = 1'b0;
            jump = 1'b0;
        end
    end
endmodule

// Control Unit: ALU operation decoder
module ALU_op_decoder(input [1:0] ALUOp,
                      input [4:0] shamt,
                      input [5:0] funct,
                      output reg [3:0] ALUControl
                     );

    always@(*) begin
        // lw, sw
        if(ALUOp == 2'b00) ALUControl = 4'b0010;
        // beq
        else if(ALUOp == 2'b01) ALUControl = 4'b0110;
        // R-type
        else if(ALUOp == 2'b10) begin
            case(funct)
                // addition
                6'b100000: ALUControl = 4'b0010;
                // substruction
                6'b100010: ALUControl = 4'b0110;
                // and
                6'b100100: ALUControl = 4'b0000;
                // or
                6'b100101: ALUControl = 4'b0001;
                // slt
                6'b101010: ALUControl = 4'b0111;
                // sllv
                6'b000100: ALUControl = 4'b0100;
                // srlv
                6'b000110: ALUControl = 4'b0011;
                // srav
                6'b000111: ALUControl = 4'b0101;
            endcase
        end
        // addu[_s].qb
        else if(ALUOp == 2'b11) begin
            case(shamt)
                // saturated addition byte by byte
                5'b00100: ALUControl = 4'b1001;
                // addition byte by byte
                5'b00000: ALUControl = 4'b1000;
            endcase            
        end
    end
endmodule

// ALU
module ALU(input [31:0] SrcA, SrcB,
           input [3:0] ALUControl,
           output reg [31:0] ALUResult,
           output reg Zero
          );

    wire [31:0] SatSum;
    saturated_sum SS(SrcA, SrcB, SatSum);

    always@(*) begin
        // add
        if(ALUControl == 4'b0010) ALUResult = SrcA + SrcB;
        // sub
        else if(ALUControl == 4'b0110) ALUResult = SrcA - SrcB;
        // and
        else if(ALUControl == 4'b0000) ALUResult = SrcA & SrcB;
        // or
        else if(ALUControl == 4'b0001) ALUResult = SrcA | SrcB;
        // slt
        else if(ALUControl == 4'b0111) begin
            if(SrcA[31] == SrcB[31]) ALUResult = SrcA < SrcB;
            else if(SrcA[31] == 1'b1) ALUResult = 1'b1;
            else ALUResult = 1'b0;
        end
        // addu
        else if(ALUControl == 4'b1000) begin
            ALUResult[7:0] = SrcA[7:0] + SrcB[7:0];
            ALUResult[15:8] = SrcA[15:8] + SrcB[15:8];
            ALUResult[23:16] = SrcA[23:16] + SrcB[23:16];
            ALUResult[31:24] = SrcA[31:24] + SrcB[31:24];
        end
        // addu_s
        else if(ALUControl == 4'b1001) ALUResult = SatSum;
        // sllv
        else if(ALUControl == 4'b0100) ALUResult = SrcB << SrcA;
        // srlv
        else if(ALUControl == 4'b0011) ALUResult = SrcB[30:0] >> SrcA;
        // srav
        else if(ALUControl == 4'b0101) ALUResult = SrcB >> SrcA;
        else ALUResult = -1;

        // Zero output
        if(ALUResult == 0) Zero = 1;
        else Zero = 0;
    end
endmodule


//----------------------------------------------------------------------------------
// additional modules
//----------------------------------------------------------------------------------

// 2:1 multiplexer
module mux_2_1(input [31:0] a, b, input select, output reg [31:0] out);
    always@(*) begin
        if(select) out = a;
        else out = b;
    end
endmodule

// 2:1 multiplexer
module mux_5_bits(input [4:0] a, b, input select, output reg [4:0] out);
    always@(*) begin
        if(select) out = a;
        else out = b;
    end
endmodule 

// shift left by 2 for branch address shifts
module shift_left_2(input [31:0] address, output [31:0] out);
    assign out[31:2] = address[29:0];
    assign out[1:0] = 2'b00;
endmodule

// sign extension unit from 16 to 32 bits
module sign_extend(input [15:0] in,
                   output reg [31:0] out
                  );

    always@(*) begin
        // if first bit is 1, extend high 16 bits to 1
        if(in[15] == 1'b1) begin
            out[31:16] = 16'b1111111111111111;
            out[15:0] = in[15:0];
        end
        // else, extend high 16 bits to 0
        else begin
            out[31:16] = 16'b0000000000000000;
            out[15:0] = in[15:0];
        end
    end
endmodule

// saturated sum
module saturated_sum(input [31:0] SrcA, SrcB,
                     output reg [31:0] SatSum
                    );

    reg [8:0] byte_sat_sum1, byte_sat_sum2, byte_sat_sum3, byte_sat_sum4;

    always@(*) begin
        // first byte
        byte_sat_sum1 = SrcA[7:0] + SrcB[7:0];
        if(byte_sat_sum1[8] == 1'b1) SatSum[7:0] = 8'b11111111;
        else SatSum[7:0] = byte_sat_sum1[7:0];
        // second byte
        byte_sat_sum2 = SrcA[15:8] + SrcB[15:8];
        if(byte_sat_sum2[8] == 1'b1) SatSum[15:8] = 8'b11111111;
        else SatSum[15:8] = byte_sat_sum2[7:0];
        // third byte
        byte_sat_sum3 = SrcA[23:16] + SrcB[23:16];
        if(byte_sat_sum3[8] == 1'b1) SatSum[23:16] = 8'b11111111;
        else SatSum[23:16] = byte_sat_sum3[7:0];
        // fourth byte
        byte_sat_sum4 = SrcA[31:24] + SrcB[31:24];
        if(byte_sat_sum4[8] == 1'b1) SatSum[31:24] = 8'b11111111;
        else SatSum[31:24] = byte_sat_sum4[7:0];
    end
endmodule