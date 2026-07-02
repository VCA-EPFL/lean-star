-- RVUtil.lean - Lean formalization of Star/Bluespec/simple-processor/RVUtil.bsv,
-- restricted to the decode/ALU/branch-resolution surface that mkpipelined.bsv
-- actually calls (decodeInst, getInstFields, getImmediate, isJAL/isJALR/
-- isMemoryInst/isControlInst, execALU32, execControl32). Floating-point/AMO/CSR
-- opcode classes and helpers (isBRANCH aside) that the pipeline never dispatches
-- on are omitted, matching this codebase's practice of only modeling what
-- callers use.

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace RVUtil

-- Opcode field (inst[6:0]), 32-bit (non-compressed) instructions only.
def op_LOAD : BitVec 7 := 0b0000011
def op_OPIMM : BitVec 7 := 0b0010011
def op_AUIPC : BitVec 7 := 0b0010111
def op_STORE : BitVec 7 := 0b0100011
def op_OP : BitVec 7 := 0b0110011
def op_LUI : BitVec 7 := 0b0110111
def op_BRANCH : BitVec 7 := 0b1100011
def op_JALR : BitVec 7 := 0b1100111
def op_JAL : BitVec 7 := 0b1101111
def op_SYSTEM : BitVec 7 := 0b1110011

-- 5-bit opcode field (inst[6:2]; low 2 bits are always 2'b11 for 32-bit instrs).
def op5_LOAD : BitVec 5 := 0b00000
def op5_LOADFP : BitVec 5 := 0b00001
def op5_OPIMM : BitVec 5 := 0b00100
def op5_OPIMM32 : BitVec 5 := 0b00110
def op5_JALR : BitVec 5 := 0b11001
def op5_AUIPC : BitVec 5 := 0b00101
def op5_LUI : BitVec 5 := 0b01101
def op5_STORE : BitVec 5 := 0b01000
def op5_STOREFP : BitVec 5 := 0b01001
def op5_BRANCH : BitVec 5 := 0b11000
def op5_JAL : BitVec 5 := 0b11011

-- funct3 field (inst[14:12]), named per opcode class as in RVUtil.bsv.
def fn3_BEQ : BitVec 3 := 0b000
def fn3_BNE : BitVec 3 := 0b001
def fn3_BLT : BitVec 3 := 0b100
def fn3_BGE : BitVec 3 := 0b101
def fn3_BLTU : BitVec 3 := 0b110
def fn3_BGEU : BitVec 3 := 0b111
def fn3_B : BitVec 3 := 0b000
def fn3_H : BitVec 3 := 0b001
def fn3_W : BitVec 3 := 0b010
def fn3_BU : BitVec 3 := 0b100
def fn3_HU : BitVec 3 := 0b101
def fn3_ADDSUB : BitVec 3 := 0b000
def fn3_SLL : BitVec 3 := 0b001
def fn3_SLT : BitVec 3 := 0b010
def fn3_SLTU : BitVec 3 := 0b011
def fn3_XOR : BitVec 3 := 0b100
def fn3_SR : BitVec 3 := 0b101
def fn3_OR : BitVec 3 := 0b110
def fn3_AND : BitVec 3 := 0b111
def fn3_MUL : BitVec 3 := 0b000
def fn3_DIV : BitVec 3 := 0b100
def fn3_DIVU : BitVec 3 := 0b101
def fn3_REM : BitVec 3 := 0b110
def fn3_REMU : BitVec 3 := 0b111
def fn3_PRIV : BitVec 3 := 0b000

-- InstFields: result of getInstFields(instr). Only the sub-fields mkpipelined.bsv
-- and isLegalInstruction/decodeInst actually read are modeled (funct7 is kept
-- for the OPIMM-shift/OP legality checks; funct5/funct2/rs3/csr are FP/AMO/CSR
-- fields that this pipeline never dispatches on and are omitted).
structure InstFields where
  opcode : BitVec 7
  funct3 : BitVec 3
  funct7 : BitVec 7
  rd : BitVec 5
  rs1 : BitVec 5
  rs2 : BitVec 5
deriving Inhabited, BEq

def getInstFields (inst : BitVec 32) : InstFields :=
  { opcode := extract_bits inst 6 0,
    funct3 := extract_bits inst 14 12,
    funct7 := extract_bits inst 31 25,
    rd := extract_bits inst 11 7,
    rs1 := extract_bits inst 19 15,
    rs2 := extract_bits inst 24 20 }

-- Raw (sign-extended) immediate bit patterns, shared between InstFields-style
-- field access and the standalone getImmediateX functions below (RVUtil.bsv
-- recomputes these independently in both places; here they're factored once
-- since both call sites are exactly the same bit-slice-then-sign-extend logic).
def immBitsI (inst : BitVec 32) : BitVec 32 :=
  sign_extend (extract_bits inst 31 20)

def immBitsS (inst : BitVec 32) : BitVec 32 :=
  sign_extend (concat_bits (extract_bits inst 31 25) 5 (extract_bits inst 11 7))

def immBitsB (inst : BitVec 32) : BitVec 32 :=
  sign_extend
    (concat_bits (extract_bit inst 31) 12
      (concat_bits (extract_bit inst 7) 11
        (concat_bits (extract_bits inst 30 25) 5
          (concat_bits (extract_bits inst 11 8) 1 (0 : BitVec 1)))))

def immBitsU (inst : BitVec 32) : BitVec 32 :=
  concat_bits (extract_bits inst 31 12) 12 (0 : BitVec 12)

def immBitsJ (inst : BitVec 32) : BitVec 32 :=
  sign_extend
    (concat_bits (extract_bit inst 31) 20
      (concat_bits (extract_bits inst 19 12) 12
        (concat_bits (extract_bit inst 20) 11
          (concat_bits (extract_bits inst 30 21) 1 (0 : BitVec 1)))))

def getImmediateI (inst : BitVec 32) : BitVec 32 := immBitsI inst
def getImmediateS (inst : BitVec 32) : BitVec 32 := immBitsS inst
def getImmediateB (inst : BitVec 32) : BitVec 32 := immBitsB inst
def getImmediateU (inst : BitVec 32) : BitVec 32 := immBitsU inst
def getImmediateJ (inst : BitVec 32) : BitVec 32 := immBitsJ inst

inductive ImmediateType where
  | ImmI | ImmS | ImmB | ImmU | ImmJ
deriving BEq, Inhabited

def getImmediateTypeFrom32BitInst (inst : BitVec 32) : t_maybe ImmediateType :=
  let op5 := extract_bits inst 6 2
  if op5 == op5_LOAD || op5 == op5_LOADFP || op5 == op5_OPIMM || op5 == op5_OPIMM32 || op5 == op5_JALR then
    Valid ImmediateType.ImmI
  else if op5 == op5_AUIPC || op5 == op5_LUI then
    Valid ImmediateType.ImmU
  else if op5 == op5_STORE || op5 == op5_STOREFP then
    Valid ImmediateType.ImmS
  else if op5 == op5_BRANCH then
    Valid ImmediateType.ImmB
  else if op5 == op5_JAL then
    Valid ImmediateType.ImmJ
  else
    Invalid Unit_

-- DecodedInst: result of decodeInst(instr).
structure DecodedInst where
  legal : t_bool
  valid_rs1 : t_bool
  valid_rs2 : t_bool
  valid_rd : t_bool
  immediateType : t_maybe ImmediateType
  inst : BitVec 32
deriving Inhabited, BEq

def getImmediate (dInst : DecodedInst) : BitVec 32 :=
  match dInst.immediateType with
  | Valid ImmediateType.ImmI => getImmediateI dInst.inst
  | Valid ImmediateType.ImmS => getImmediateS dInst.inst
  | Valid ImmediateType.ImmB => getImmediateB dInst.inst
  | Valid ImmediateType.ImmU => getImmediateU dInst.inst
  | Valid ImmediateType.ImmJ => getImmediateJ dInst.inst
  | Invalid _ => 0

def isMultiplyInst (inst : BitVec 32) : t_bool :=
  let fields := getInstFields inst
  if fields.funct7 == (0b0000001 : BitVec 7) && fields.funct3 == fn3_MUL && fields.opcode == op_OP
  then BTrue Unit_ else BFalse Unit_

-- isLegalInstruction: only the opcode classes RVUtil.bsv actually classifies
-- as legal are checked; everything else falls through to `False` as in the
-- source's `default: False` arm.
def isLegalInstruction (inst : BitVec 32) : t_bool :=
  let fields := getInstFields inst
  let baseLegal : Bool :=
    if fields.opcode == op_LOAD then
      fields.funct3 == fn3_B || fields.funct3 == fn3_H || fields.funct3 == fn3_W
        || fields.funct3 == fn3_BU || fields.funct3 == fn3_HU
    else if fields.opcode == op_OPIMM then
      if fields.funct3 == fn3_ADDSUB || fields.funct3 == fn3_SLT || fields.funct3 == fn3_SLTU
          || fields.funct3 == fn3_XOR || fields.funct3 == fn3_OR || fields.funct3 == fn3_AND then
        true
      else if fields.funct3 == fn3_SLL then
        extract_bits fields.funct7 6 1 == (0b000000 : BitVec 6) && extract_bit fields.funct7 0 == (0 : BitVec 1)
      else if fields.funct3 == fn3_SR then
        (extract_bits fields.funct7 6 1 == (0b000000 : BitVec 6)
            || extract_bits fields.funct7 6 1 == (0b010000 : BitVec 6))
          && extract_bit fields.funct7 0 == (0 : BitVec 1)
      else false
    else if fields.opcode == op_AUIPC then true
    else if fields.opcode == op_STORE then
      fields.funct3 == fn3_B || fields.funct3 == fn3_H || fields.funct3 == fn3_W
    else if fields.opcode == op_OP then
      if fields.funct3 == fn3_ADDSUB || fields.funct3 == fn3_SR then
        fields.funct7 == (0b0000000 : BitVec 7) || fields.funct7 == (0b0100000 : BitVec 7)
      else if fields.funct3 == fn3_DIV || fields.funct3 == fn3_DIVU || fields.funct3 == fn3_REM
          || fields.funct3 == fn3_REMU || fields.funct3 == fn3_SLL || fields.funct3 == fn3_SLT
          || fields.funct3 == fn3_SLTU || fields.funct3 == fn3_XOR || fields.funct3 == fn3_OR
          || fields.funct3 == fn3_AND then
        fields.funct7 == (0b0000000 : BitVec 7)
      else false
    else if fields.opcode == op_LUI then true
    else if fields.opcode == op_BRANCH then
      fields.funct3 == fn3_BEQ || fields.funct3 == fn3_BNE || fields.funct3 == fn3_BLT
        || fields.funct3 == fn3_BGE || fields.funct3 == fn3_BLTU || fields.funct3 == fn3_BGEU
    else if fields.opcode == op_JALR then fields.funct3 == (0b000 : BitVec 3)
    else if fields.opcode == op_JAL then true
    else if fields.opcode == op_SYSTEM then
      if fields.funct3 == fn3_PRIV then
        let combined := concat_bits fields.funct7 5 fields.rs2
        fields.rd == (0b00000 : BitVec 5) &&
          (if combined == (0b000000000000 : BitVec 12) then fields.rs1 == (0b00000 : BitVec 5) -- ECALL
           else if combined == (0b000000000001 : BitVec 12) then fields.rs1 == (0b00000 : BitVec 5) -- EBREAK
           else if combined == (0b001100000010 : BitVec 12) then fields.rs1 == (0b00000 : BitVec 5) -- MRET
           else if combined == (0b000100000101 : BitVec 12) then fields.rs1 == (0b00000 : BitVec 5) -- WFI
           else false)
      else false
    else false
  bool_or (if baseLegal then BTrue Unit_ else BFalse Unit_) (isMultiplyInst inst)

def usesRD (inst : BitVec 32) : t_bool :=
  let op5 := extract_bits inst 6 2
  let b :=
    op5 == (0b01101 : BitVec 5) -- lui
      || op5 == (0b11011 : BitVec 5) -- jal
      || op5 == (0b00000 : BitVec 5) -- loads
      || op5 == (0b01100 : BitVec 5) -- OP
      || op5 == (0b11001 : BitVec 5) -- jalr
      || op5 == (0b00100 : BitVec 5) -- OPIMM
      || op5 == (0b00101 : BitVec 5) -- auipc
  if b then BTrue Unit_ else BFalse Unit_

def usesRS1 (inst : BitVec 32) : t_bool :=
  let op5 := extract_bits inst 6 2
  let b :=
    op5 == (0b11000 : BitVec 5) -- branch
      || op5 == (0b00000 : BitVec 5) -- loads
      || op5 == (0b01000 : BitVec 5) -- store
      || op5 == (0b01100 : BitVec 5) -- OP
      || op5 == (0b11001 : BitVec 5) -- jalr
      || op5 == (0b00100 : BitVec 5) -- OPIMM
  if b then BTrue Unit_ else BFalse Unit_

def usesRS2 (inst : BitVec 32) : t_bool :=
  let op5 := extract_bits inst 6 2
  let b :=
    op5 == (0b11000 : BitVec 5) -- branch
      || op5 == (0b01000 : BitVec 5) -- store
      || op5 == (0b01100 : BitVec 5) -- OP
  if b then BTrue Unit_ else BFalse Unit_

def decodeInst (input_inst : BitVec 32) : DecodedInst :=
  { legal := isLegalInstruction input_inst,
    valid_rs1 := usesRS1 input_inst,
    valid_rs2 := usesRS2 input_inst,
    valid_rd := usesRD input_inst,
    immediateType := getImmediateTypeFrom32BitInst input_inst,
    inst := input_inst }

def alu32 (funct3 : BitVec 3) (inst_30 : BitVec 1) (a b : BitVec 32) : BitVec 32 :=
  let shamt : BitVec 5 := truncate b 5
  if funct3 == fn3_ADDSUB then (if inst_30 == (1 : BitVec 1) then a - b else a + b)
  else if funct3 == fn3_SLL then shift_left a shamt
  else if funct3 == fn3_SLT then zero_extend (if a.toInt < b.toInt then (1 : BitVec 1) else (0 : BitVec 1)) 32
  else if funct3 == fn3_SLTU then zero_extend (if a.toNat < b.toNat then (1 : BitVec 1) else (0 : BitVec 1)) 32
  else if funct3 == fn3_XOR then bit_xor a b
  else if funct3 == fn3_SR then
    (if inst_30 == (1 : BitVec 1) then shift_right_arith a shamt else shift_right_logical a shamt)
  else if funct3 == fn3_OR then bit_or a b
  else if funct3 == fn3_AND then bit_and a b
  else 0

-- execALU32(inst, rv1, rv2, imm, pc) : the ALU result / effective address /
-- store data depending on instruction class.
def execALU32 (inst rs1_val rs2_val imm_val pc : BitVec 32) : BitVec 32 :=
  let isLUI := extract_bit inst 2 == (1 : BitVec 1) && extract_bit inst 5 == (1 : BitVec 1)
  let isAUIPC := extract_bit inst 2 == (1 : BitVec 1) && extract_bit inst 5 == (0 : BitVec 1)
  let isIMM := extract_bit inst 5 == (0 : BitVec 1)
  if isLUI then imm_val
  else if isAUIPC then pc + imm_val
  else
    let alu_src1 := rs1_val
    let alu_src2 := if isIMM then imm_val else rs2_val
    let funct3 := extract_bits inst 14 12
    let inst_30 := if funct3 == fn3_ADDSUB && isIMM then (0 : BitVec 1) else extract_bit inst 30
    alu32 funct3 inst_30 alu_src1 alu_src2

-- ExecControlResult: result of execControl32(...).
structure ExecControlResult where
  taken : t_bool
  nextPC : BitVec 32
deriving Inhabited, BEq

-- execControl32(inst, rv1, rv2, imm, pc) : branch/jump resolution.
def execControl32 (inst rs1_val rs2_val imm_val pc : BitVec 32) : ExecControlResult :=
  let isControl := extract_bits inst 6 4 == (0b110 : BitVec 3)
  let isJALv := extract_bit inst 2 == (1 : BitVec 1) && extract_bit inst 3 == (1 : BitVec 1)
  let isJALRv := extract_bit inst 2 == (1 : BitVec 1) && extract_bit inst 3 == (0 : BitVec 1)
  let incPC := pc + (4 : BitVec 32)
  let funct3 := extract_bits inst 14 12
  if !isControl then
    { taken := BFalse Unit_, nextPC := incPC }
  else if isJALv then
    { taken := BTrue Unit_, nextPC := pc + imm_val }
  else if isJALRv then
    { taken := BTrue Unit_, nextPC := bit_and (rs1_val + imm_val) (bit_not (1 : BitVec 32)) }
  else
    let takenB :=
      if funct3 == fn3_BEQ then rs1_val == rs2_val
      else if funct3 == fn3_BNE then rs1_val != rs2_val
      else if funct3 == fn3_BLT then rs1_val.toInt < rs2_val.toInt
      else if funct3 == fn3_BGE then rs1_val.toInt >= rs2_val.toInt
      else if funct3 == fn3_BLTU then rs1_val.toNat < rs2_val.toNat
      else if funct3 == fn3_BGEU then rs1_val.toNat >= rs2_val.toNat
      else false -- unreachable: BRANCH opcode only ever carries these 6 funct3 values
    { taken := (if takenB then BTrue Unit_ else BFalse Unit_),
      nextPC := if takenB then pc + imm_val else incPC }

def isControlInst (dInst : DecodedInst) : t_bool :=
  if extract_bits dInst.inst 6 4 == (0b110 : BitVec 3) then BTrue Unit_ else BFalse Unit_

def isBRANCH (dInst : DecodedInst) : t_bool :=
  if extract_bits dInst.inst 6 4 == (0b110 : BitVec 3) && extract_bit dInst.inst 2 == (0 : BitVec 1)
  then BTrue Unit_ else BFalse Unit_

def isJALR (dInst : DecodedInst) : t_bool :=
  if extract_bits dInst.inst 6 4 == (0b110 : BitVec 3) && extract_bits dInst.inst 3 2 == (0b01 : BitVec 2)
  then BTrue Unit_ else BFalse Unit_

def isJAL (dInst : DecodedInst) : t_bool :=
  if extract_bits dInst.inst 6 4 == (0b110 : BitVec 3) && extract_bits dInst.inst 3 2 == (0b11 : BitVec 2)
  then BTrue Unit_ else BFalse Unit_

def isMemoryInst (dInst : DecodedInst) : t_bool :=
  if extract_bit dInst.inst 6 == (0 : BitVec 1) && extract_bits dInst.inst 4 3 == (0b00 : BitVec 2)
  then BTrue Unit_ else BFalse Unit_

end RVUtil
