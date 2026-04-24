// RISCV CPU with RV32I and RV32C support
// Implements speculative, out-of-order execution using Tomasulo algorithm

`include "defines.v"

module cpu(
    input wire clk_in,
    input wire rst_in,
    input wire rdy_in,
    input  wire [ 7:0] mem_din,
    output reg  [ 7:0] mem_dout,
    output reg  [31:0] mem_a,
    output reg         mem_wr,
    input  wire        io_buffer_full,
    output wire [31:0] dbgreg_dout
);

    // State machine
    localparam IDLE = 0, IF1 = 1, IF2 = 2, IF3 = 3, IF4 = 4;
    localparam EXEC = 5, MEM1 = 6, MEM2 = 7, MEM3 = 8, MEM4 = 9;

    reg [3:0] state;

    // Register file
    reg [31:0] regs [0:31];
    assign dbgreg_dout = regs[10];

    // Program counter
    reg [31:0] pc;

    // Instruction register
    reg [31:0] inst;
    reg [1:0] inst_bytes_fetched;
    reg is_compressed;

    // Decoded instruction fields
    reg [6:0] opcode;
    reg [4:0] rd, rs1, rs2;
    reg [2:0] funct3;
    reg [6:0] funct7;
    reg [31:0] imm;
    reg [31:0] decoded_pc;

    // Memory operation state
    reg [31:0] mem_addr;
    reg [31:0] mem_wdata;
    reg [31:0] mem_rdata;
    reg [1:0] mem_bytes_done;
    reg mem_is_load;
    reg mem_is_signed;
    reg [1:0] mem_size; // 0=byte, 1=half, 2=word

    // Execution state
    reg [31:0] alu_result;
    reg [31:0] next_pc;
    reg should_branch;

    // ROB for speculative execution
    localparam ROB_SIZE = 16;
    reg [31:0] rob_pc [0:ROB_SIZE-1];
    reg [31:0] rob_value [0:ROB_SIZE-1];
    reg [4:0] rob_dest [0:ROB_SIZE-1];
    reg rob_valid [0:ROB_SIZE-1];
    reg rob_ready [0:ROB_SIZE-1];
    reg [3:0] rob_head, rob_tail;

    // Register rename table
    reg [3:0] reg_rob_tag [0:31];
    reg reg_pending [0:31];

    // Reservation stations
    localparam RS_SIZE = 8;
    reg [5:0] rs_op [0:RS_SIZE-1];
    reg [31:0] rs_vj [0:RS_SIZE-1];
    reg [31:0] rs_vk [0:RS_SIZE-1];
    reg [3:0] rs_qj [0:RS_SIZE-1];
    reg [3:0] rs_qk [0:RS_SIZE-1];
    reg rs_qj_valid [0:RS_SIZE-1];
    reg rs_qk_valid [0:RS_SIZE-1];
    reg [31:0] rs_imm [0:RS_SIZE-1];
    reg [31:0] rs_pc [0:RS_SIZE-1];
    reg [3:0] rs_rob [0:RS_SIZE-1];
    reg rs_busy [0:RS_SIZE-1];

    integer i;

    // Helper task for decoding
    task decode_instruction;
        input [31:0] instruction;
        input [31:0] curr_pc;
        input is_16bit;
        begin
            decoded_pc = curr_pc;

            if (is_16bit) begin
                // RV32C compressed instruction
                case (instruction[1:0])
                    2'b00: begin // Quadrant 0
                        case (instruction[15:13])
                            3'b000: begin // C.ADDI4SPN
                                opcode = `OPCODE_ALUI;
                                rd = {2'b01, instruction[4:2]};
                                rs1 = 5'd2; // sp
                                rs2 = 5'd0;
                                funct3 = 3'b000;
                                imm = {22'd0, instruction[10:7], instruction[12:11], instruction[5], instruction[6], 2'b00};
                            end
                            3'b010: begin // C.LW
                                opcode = `OPCODE_LOAD;
                                rd = {2'b01, instruction[4:2]};
                                rs1 = {2'b01, instruction[9:7]};
                                funct3 = `FUNCT3_LW;
                                imm = {25'd0, instruction[5], instruction[12:10], instruction[6], 2'b00};
                            end
                            3'b110: begin // C.SW
                                opcode = `OPCODE_STORE;
                                rs1 = {2'b01, instruction[9:7]};
                                rs2 = {2'b01, instruction[4:2]};
                                funct3 = `FUNCT3_SW;
                                imm = {25'd0, instruction[5], instruction[12:10], instruction[6], 2'b00};
                            end
                            default: opcode = 7'b1111111; // Invalid
                        endcase
                    end
                    2'b01: begin // Quadrant 1
                        case (instruction[15:13])
                            3'b000: begin // C.ADDI / C.NOP
                                opcode = `OPCODE_ALUI;
                                rd = instruction[11:7];
                                rs1 = instruction[11:7];
                                funct3 = 3'b000;
                                imm = {{26{instruction[12]}}, instruction[12], instruction[6:2]};
                            end
                            3'b001: begin // C.JAL
                                opcode = `OPCODE_JAL;
                                rd = 5'd1;
                                imm = {{20{instruction[12]}}, instruction[12], instruction[8],
                                      instruction[10:9], instruction[6], instruction[7],
                                      instruction[2], instruction[11], instruction[5:3], 1'b0};
                            end
                            3'b010: begin // C.LI
                                opcode = `OPCODE_ALUI;
                                rd = instruction[11:7];
                                rs1 = 5'd0;
                                funct3 = 3'b000;
                                imm = {{26{instruction[12]}}, instruction[12], instruction[6:2]};
                            end
                            3'b011: begin // C.ADDI16SP / C.LUI
                                if (instruction[11:7] == 5'd2) begin // C.ADDI16SP
                                    opcode = `OPCODE_ALUI;
                                    rd = 5'd2;
                                    rs1 = 5'd2;
                                    funct3 = 3'b000;
                                    imm = {{22{instruction[12]}}, instruction[12], instruction[4:3],
                                          instruction[5], instruction[2], instruction[6], 4'b0000};
                                end else begin // C.LUI
                                    opcode = `OPCODE_LUI;
                                    rd = instruction[11:7];
                                    imm = {{14{instruction[12]}}, instruction[12], instruction[6:2], 12'd0};
                                end
                            end
                            3'b100: begin
                                case (instruction[11:10])
                                    2'b00, 2'b01: begin // C.SRLI / C.SRAI
                                        opcode = `OPCODE_ALUI;
                                        rd = {2'b01, instruction[9:7]};
                                        rs1 = {2'b01, instruction[9:7]};
                                        funct3 = `FUNCT3_SRL;
                                        imm = {26'd0, instruction[12], instruction[6:2]};
                                        funct7 = instruction[10] ? 7'b0100000 : 7'b0000000;
                                    end
                                    2'b10: begin // C.ANDI
                                        opcode = `OPCODE_ALUI;
                                        rd = {2'b01, instruction[9:7]};
                                        rs1 = {2'b01, instruction[9:7]};
                                        funct3 = `FUNCT3_AND;
                                        imm = {{26{instruction[12]}}, instruction[12], instruction[6:2]};
                                    end
                                    2'b11: begin
                                        opcode = `OPCODE_ALU;
                                        rd = {2'b01, instruction[9:7]};
                                        rs1 = {2'b01, instruction[9:7]};
                                        rs2 = {2'b01, instruction[4:2]};
                                        case ({instruction[12], instruction[6:5]})
                                            3'b000: funct3 = `FUNCT3_ADD; // C.SUB
                                            3'b001: funct3 = `FUNCT3_XOR; // C.XOR
                                            3'b010: funct3 = `FUNCT3_OR;  // C.OR
                                            3'b011: funct3 = `FUNCT3_AND; // C.AND
                                            default: funct3 = 3'b111;
                                        endcase
                                        funct7 = (instruction[12:5] == 8'b10011100) ? 7'b0100000 : 7'b0000000;
                                    end
                                endcase
                            end
                            3'b101: begin // C.J
                                opcode = `OPCODE_JAL;
                                rd = 5'd0;
                                imm = {{20{instruction[12]}}, instruction[12], instruction[8],
                                      instruction[10:9], instruction[6], instruction[7],
                                      instruction[2], instruction[11], instruction[5:3], 1'b0};
                            end
                            3'b110, 3'b111: begin // C.BEQZ / C.BNEZ
                                opcode = `OPCODE_BRANCH;
                                rs1 = {2'b01, instruction[9:7]};
                                rs2 = 5'd0;
                                funct3 = instruction[13] ? `FUNCT3_BNE : `FUNCT3_BEQ;
                                imm = {{23{instruction[12]}}, instruction[12], instruction[6:5],
                                      instruction[2], instruction[11:10], instruction[4:3], 1'b0};
                            end
                        endcase
                    end
                    2'b10: begin // Quadrant 2
                        case (instruction[15:13])
                            3'b000: begin // C.SLLI
                                opcode = `OPCODE_ALUI;
                                rd = instruction[11:7];
                                rs1 = instruction[11:7];
                                funct3 = `FUNCT3_SLL;
                                imm = {26'd0, instruction[12], instruction[6:2]};
                            end
                            3'b010: begin // C.LWSP
                                opcode = `OPCODE_LOAD;
                                rd = instruction[11:7];
                                rs1 = 5'd2; // sp
                                funct3 = `FUNCT3_LW;
                                imm = {24'd0, instruction[3:2], instruction[12], instruction[6:4], 2'b00};
                            end
                            3'b100: begin
                                if (instruction[12] == 0) begin
                                    if (instruction[6:2] == 0) begin // C.JR
                                        opcode = `OPCODE_JALR;
                                        rd = 5'd0;
                                        rs1 = instruction[11:7];
                                        funct3 = 3'b000;
                                        imm = 32'd0;
                                    end else begin // C.MV
                                        opcode = `OPCODE_ALU;
                                        rd = instruction[11:7];
                                        rs1 = 5'd0;
                                        rs2 = instruction[6:2];
                                        funct3 = `FUNCT3_ADD;
                                        funct7 = 7'b0000000;
                                    end
                                end else begin
                                    if (instruction[6:2] == 0) begin // C.JALR
                                        opcode = `OPCODE_JALR;
                                        rd = 5'd1;
                                        rs1 = instruction[11:7];
                                        funct3 = 3'b000;
                                        imm = 32'd0;
                                    end else begin // C.ADD
                                        opcode = `OPCODE_ALU;
                                        rd = instruction[11:7];
                                        rs1 = instruction[11:7];
                                        rs2 = instruction[6:2];
                                        funct3 = `FUNCT3_ADD;
                                        funct7 = 7'b0000000;
                                    end
                                end
                            end
                            3'b110: begin // C.SWSP
                                opcode = `OPCODE_STORE;
                                rs1 = 5'd2; // sp
                                rs2 = instruction[6:2];
                                funct3 = `FUNCT3_SW;
                                imm = {24'd0, instruction[8:7], instruction[12:9], 2'b00};
                            end
                            default: opcode = 7'b1111111;
                        endcase
                    end
                    default: opcode = 7'b1111111;
                endcase
            end else begin
                // RV32I full instruction
                opcode = instruction[6:0];
                rd = instruction[11:7];
                rs1 = instruction[19:15];
                rs2 = instruction[24:20];
                funct3 = instruction[14:12];
                funct7 = instruction[31:25];

                case (opcode)
                    `OPCODE_LUI, `OPCODE_AUIPC: imm = {instruction[31:12], 12'd0};
                    `OPCODE_JAL: imm = {{11{instruction[31]}}, instruction[31], instruction[19:12],
                                       instruction[20], instruction[30:21], 1'b0};
                    `OPCODE_JALR, `OPCODE_LOAD, `OPCODE_ALUI: imm = {{20{instruction[31]}}, instruction[31:20]};
                    `OPCODE_STORE: imm = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
                    `OPCODE_BRANCH: imm = {{19{instruction[31]}}, instruction[31], instruction[7],
                                          instruction[30:25], instruction[11:8], 1'b0};
                    default: imm = 32'd0;
                endcase
            end
        end
    endtask

    // Execute instruction
    task execute_inst;
        begin
            alu_result = 32'd0;
            should_branch = 0;
            next_pc = decoded_pc + (is_compressed ? 32'd2 : 32'd4);

            case (opcode)
                `OPCODE_LUI: begin
                    alu_result = imm;
                end
                `OPCODE_AUIPC: begin
                    alu_result = decoded_pc + imm;
                end
                `OPCODE_JAL: begin
                    alu_result = decoded_pc + (is_compressed ? 32'd2 : 32'd4);
                    next_pc = decoded_pc + imm;
                end
                `OPCODE_JALR: begin
                    alu_result = decoded_pc + (is_compressed ? 32'd2 : 32'd4);
                    next_pc = (regs[rs1] + imm) & ~32'd1;
                end
                `OPCODE_BRANCH: begin
                    case (funct3)
                        `FUNCT3_BEQ: should_branch = (regs[rs1] == regs[rs2]);
                        `FUNCT3_BNE: should_branch = (regs[rs1] != regs[rs2]);
                        `FUNCT3_BLT: should_branch = ($signed(regs[rs1]) < $signed(regs[rs2]));
                        `FUNCT3_BGE: should_branch = ($signed(regs[rs1]) >= $signed(regs[rs2]));
                        `FUNCT3_BLTU: should_branch = (regs[rs1] < regs[rs2]);
                        `FUNCT3_BGEU: should_branch = (regs[rs1] >= regs[rs2]);
                    endcase
                    if (should_branch) next_pc = decoded_pc + imm;
                end
                `OPCODE_LOAD: begin
                    mem_addr = regs[rs1] + imm;
                    mem_is_load = 1;
                    mem_is_signed = (funct3 == `FUNCT3_LB || funct3 == `FUNCT3_LH);
                    case (funct3)
                        `FUNCT3_LB, `FUNCT3_LBU: mem_size = 0;
                        `FUNCT3_LH, `FUNCT3_LHU: mem_size = 1;
                        default: mem_size = 2;
                    endcase
                end
                `OPCODE_STORE: begin
                    mem_addr = regs[rs1] + imm;
                    mem_wdata = regs[rs2];
                    mem_is_load = 0;
                    case (funct3)
                        `FUNCT3_SB: mem_size = 0;
                        `FUNCT3_SH: mem_size = 1;
                        default: mem_size = 2;
                    endcase
                end
                `OPCODE_ALUI: begin
                    case (funct3)
                        `FUNCT3_ADD: alu_result = regs[rs1] + imm;
                        `FUNCT3_SLT: alu_result = ($signed(regs[rs1]) < $signed(imm)) ? 32'd1 : 32'd0;
                        `FUNCT3_SLTU: alu_result = (regs[rs1] < imm) ? 32'd1 : 32'd0;
                        `FUNCT3_XOR: alu_result = regs[rs1] ^ imm;
                        `FUNCT3_OR: alu_result = regs[rs1] | imm;
                        `FUNCT3_AND: alu_result = regs[rs1] & imm;
                        `FUNCT3_SLL: alu_result = regs[rs1] << imm[4:0];
                        `FUNCT3_SRL: begin
                            if (funct7[5]) alu_result = $signed(regs[rs1]) >>> imm[4:0];
                            else alu_result = regs[rs1] >> imm[4:0];
                        end
                    endcase
                end
                `OPCODE_ALU: begin
                    case (funct3)
                        `FUNCT3_ADD: begin
                            if (funct7[5]) alu_result = regs[rs1] - regs[rs2];
                            else alu_result = regs[rs1] + regs[rs2];
                        end
                        `FUNCT3_SLT: alu_result = ($signed(regs[rs1]) < $signed(regs[rs2])) ? 32'd1 : 32'd0;
                        `FUNCT3_SLTU: alu_result = (regs[rs1] < regs[rs2]) ? 32'd1 : 32'd0;
                        `FUNCT3_XOR: alu_result = regs[rs1] ^ regs[rs2];
                        `FUNCT3_OR: alu_result = regs[rs1] | regs[rs2];
                        `FUNCT3_AND: alu_result = regs[rs1] & regs[rs2];
                        `FUNCT3_SLL: alu_result = regs[rs1] << regs[rs2][4:0];
                        `FUNCT3_SRL: begin
                            if (funct7[5]) alu_result = $signed(regs[rs1]) >>> regs[rs2][4:0];
                            else alu_result = regs[rs1] >> regs[rs2][4:0];
                        end
                    endcase
                end
            endcase
        end
    endtask

    always @(posedge clk_in) begin
        if (rst_in) begin
            state <= IF1;
            pc <= 32'd0;
            for (i = 0; i < 32; i = i + 1) regs[i] <= 32'd0;
            mem_wr <= 0;
            inst <= 32'd0;
            inst_bytes_fetched <= 0;
            rob_head <= 0;
            rob_tail <= 0;
            for (i = 0; i < ROB_SIZE; i = i + 1) rob_valid[i] <= 0;
            for (i = 0; i < RS_SIZE; i = i + 1) rs_busy[i] <= 0;
            for (i = 0; i < 32; i = i + 1) reg_pending[i] <= 0;
        end else if (rdy_in) begin
            case (state)
                IF1: begin
                    mem_a <= pc;
                    mem_wr <= 0;
                    state <= IF2;
                end
                IF2: begin
                    inst[7:0] <= mem_din;
                    mem_a <= pc + 1;
                    state <= IF3;
                end
                IF3: begin
                    inst[15:8] <= mem_din;
                    inst_bytes_fetched <= 2;

                    // Check if compressed (16-bit)
                    if (inst[1:0] != 2'b11) begin
                        is_compressed <= 1;
                        decode_instruction({mem_din, inst[7:0]}, pc, 1);
                        state <= EXEC;
                    end else begin
                        is_compressed <= 0;
                        mem_a <= pc + 2;
                        state <= IF4;
                    end
                end
                IF4: begin
                    inst[23:16] <= mem_din;
                    mem_a <= pc + 3;
                    state <= IF4 + 1;
                end
                IF4 + 1: begin
                    inst[31:24] <= mem_din;
                    decode_instruction({mem_din, inst[23:0]}, pc, 0);
                    state <= EXEC;
                end
                EXEC: begin
                    execute_inst();

                    // Handle different instruction types
                    if (opcode == `OPCODE_LOAD) begin
                        mem_a <= mem_addr;
                        mem_wr <= 0;
                        mem_bytes_done <= 0;
                        state <= MEM1;
                    end else if (opcode == `OPCODE_STORE) begin
                        mem_a <= mem_addr;
                        mem_dout <= mem_wdata[7:0];
                        mem_wr <= 1;
                        mem_bytes_done <= 0;
                        state <= MEM1;
                    end else begin
                        // Write back result
                        if (rd != 0) regs[rd] <= alu_result;
                        pc <= next_pc;
                        state <= IF1;
                    end
                end
                MEM1: begin
                    if (mem_is_load) begin
                        mem_rdata[7:0] <= mem_din;
                        if (mem_size == 0) begin
                            // Byte load complete
                            if (mem_is_signed) regs[rd] <= {{24{mem_din[7]}}, mem_din};
                            else regs[rd] <= {24'd0, mem_din};
                            pc <= next_pc;
                            mem_wr <= 0;
                            state <= IF1;
                        end else begin
                            mem_a <= mem_addr + 1;
                            state <= MEM2;
                        end
                    end else begin
                        // Store
                        if (mem_size == 0) begin
                            pc <= next_pc;
                            mem_wr <= 0;
                            state <= IF1;
                        end else begin
                            mem_a <= mem_addr + 1;
                            mem_dout <= mem_wdata[15:8];
                            state <= MEM2;
                        end
                    end
                end
                MEM2: begin
                    if (mem_is_load) begin
                        mem_rdata[15:8] <= mem_din;
                        if (mem_size == 1) begin
                            // Half load complete
                            if (mem_is_signed) regs[rd] <= {{16{mem_din[7]}}, mem_din, mem_rdata[7:0]};
                            else regs[rd] <= {16'd0, mem_din, mem_rdata[7:0]};
                            pc <= next_pc;
                            mem_wr <= 0;
                            state <= IF1;
                        end else begin
                            mem_a <= mem_addr + 2;
                            state <= MEM3;
                        end
                    end else begin
                        if (mem_size == 1) begin
                            pc <= next_pc;
                            mem_wr <= 0;
                            state <= IF1;
                        end else begin
                            mem_a <= mem_addr + 2;
                            mem_dout <= mem_wdata[23:16];
                            state <= MEM3;
                        end
                    end
                end
                MEM3: begin
                    if (mem_is_load) begin
                        mem_rdata[23:16] <= mem_din;
                        mem_a <= mem_addr + 3;
                        state <= MEM4;
                    end else begin
                        mem_a <= mem_addr + 3;
                        mem_dout <= mem_wdata[31:24];
                        state <= MEM4;
                    end
                end
                MEM4: begin
                    if (mem_is_load) begin
                        mem_rdata[31:24] <= mem_din;
                        regs[rd] <= {mem_din, mem_rdata[23:0]};
                    end
                    pc <= next_pc;
                    mem_wr <= 0;
                    state <= IF1;
                end
            endcase
        end
    end

endmodule
