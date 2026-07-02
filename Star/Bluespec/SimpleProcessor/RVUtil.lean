-- RVUtil.lean - Formal spec surface for the external RVUtil BSV package.
-- RVUtil is a course-provided RISC-V decode/ALU/control library that is not
-- part of this repository; its instruction-set semantics are treated as an
-- uninterpreted (opaque) black box here, following the same "hand-written
-- opaque spec" convention as Star.Bluespec.Lib.mkSimpleBRAM2. Only the field
-- accessors and function signatures that mkpipelined.bsv actually uses are
-- modeled.

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace RVUtil

-- DecodedInst: result of decodeInst(instr). BSV struct fields accessed by
-- mkpipelined.bsv are valid_rs1/valid_rs2/valid_rd and the raw instruction
-- bits themselves (accessed as `dInst.inst`).
structure DecodedInst where
  inst : BitVec 32
  valid_rs1 : t_bool
  valid_rs2 : t_bool
  valid_rd : t_bool
deriving Inhabited, BEq

-- InstFields: result of getInstFields(instr). Register indices are 5 bits
-- (32-entry register file); funct3 is the standard 3-bit RISC-V field.
structure InstFields where
  rd : BitVec 5
  rs1 : BitVec 5
  rs2 : BitVec 5
  funct3 : BitVec 3
deriving Inhabited, BEq

-- ExecControlResult: result of execControl32(...). Only `.nextPC` is read
-- by mkpipelined.bsv.
structure ExecControlResult where
  nextPC : BitVec 32
deriving Inhabited, BEq

-- opaque: instruction-set semantics live outside this repository; these are
-- treated as uninterpreted functions with the signatures RVUtil exposes.
opaque decodeInst (instr : BitVec 32) : DecodedInst

opaque getInstFields (instr : BitVec 32) : InstFields

opaque getImmediate (dInst : DecodedInst) : BitVec 32

opaque isJAL (dInst : DecodedInst) : t_bool
opaque isJALR (dInst : DecodedInst) : t_bool
opaque isMemoryInst (dInst : DecodedInst) : t_bool
opaque isControlInst (dInst : DecodedInst) : t_bool

-- execALU32(inst, rv1, rv2, imm, pc) : the ALU result / effective address /
-- store data depending on instruction class.
opaque execALU32 (inst rv1 rv2 imm pc : BitVec 32) : BitVec 32

-- execControl32(inst, rv1, rv2, imm, pc) : branch/jump resolution.
opaque execControl32 (inst rv1 rv2 imm pc : BitVec 32) : ExecControlResult

end RVUtil
