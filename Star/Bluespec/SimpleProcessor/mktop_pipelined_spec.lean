import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
open BluespecPrelude
open BluespecVerification
open Params_types

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace M_mktop_pipeliend.Spec
structure state where
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  memory : Array (BitVec 32) := .mk (List.replicate 65536 default)
  mmioReq : Option t_mem
  mmioResp : Option t_mem
  memBusiness : t_membusiness
  decodedInst : RVUtil.DecodedInst
  nextPC : BitVec 32
deriving Inhabited

def isWaitingMMIO (s : state) := s.mmioReq.isSome

def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

def stepOne (s : state) : state :=
  if s.mmioResp.isSome then
    let instr := s.decodedInst.inst
    let fields := RVUtil.getInstFields instr
    let rdIdx := fields.rd
    let isValidRd := bool_and s.decodedInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
    let data := processMem s.memBusiness s.mmioResp.get!.data
    { s with rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd data (arr_get s.rf rdIdx.toNat)), pc := s.nextPC }
  else
    let pc := s.pc
    let instr := s.memory.getD pc.toNat default
    let dInst := RVUtil.decodeInst instr
    let fields := RVUtil.getInstFields instr
    let rdIdx := fields.rd
    let isValidRd := bool_and dInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
    let rs1Idx := fields.rs1
    let rs2Idx := fields.rs2
    let rv1 := ite_bsv (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                (0 : BitVec 32) (arr_get s.rf rs1Idx.toNat)
    let rv2 := ite_bsv (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                (0 : BitVec 32) (arr_get s.rf rs2Idx.toNat)
    let imm := RVUtil.getImmediate dInst
    let funct3 := (RVUtil.getInstFields dInst.inst).funct3
    let size := extract_bits funct3 1 0
    let addr0 := rv1 + imm
    let offset := extract_bits addr0 1 0
    let dataCtrl := ite_bsv (RVUtil.isControlInst dInst) (pc + (4 : BitVec 32))
                      (RVUtil.execALU32 dInst.inst rv1 rv2 imm pc)
    let isMemInst := RVUtil.isMemoryInst dInst

    let shiftAmount := concat_bits offset 3 (0 : BitVec 3)
    let byteEn : BitVec 4 :=
      if size == (0b00 : BitVec 2) then shift_left (0b0001 : BitVec 4) offset
      else if size == (0b01 : BitVec 2) then shift_left (0b0011 : BitVec 4) offset
      else shift_left (0b1111 : BitVec 4) offset -- size = 0b10 (word); 0b11 unused by RV32I
    let dataMem := shift_left rv2 shiftAmount
    let addrMem := concat_bits (extract_bits addr0 31 2) 2 (0 : BitVec 2)
    let isUnsignedMem := extract_bit funct3 2
    let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_)
                    byteEn (0 : BitVec 4)
    let reqMem : t_mem := { byte_en := typeMem, addr := addrMem, data := dataMem }
    let mmioTarget := isMMIO addrMem

    let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm pc).nextPC

    let finalIsUnsigned := ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)
    let finalMmio := match _ : isMemInst with | BTrue _ => mmioTarget | BFalse _ => BFalse Unit_
    let memBusinessVal : t_membusiness :=
      { isUnsigned := bitvec1_to_bool finalIsUnsigned, size := size, offset := offset, mmio := finalMmio }
    match _ : isMemInst with
    | BTrue _ =>
      { (match _ : mmioTarget with
        | BTrue _ => { s with mmioReq := some reqMem, decodedInst := dInst }
        | BFalse _ => { if typeMem == 0 then
                        let finalMem := processMem memBusinessVal (s.memory.getD addrMem.toNat default)
                        { s with rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalMem (arr_get s.rf rdIdx.toNat)), nextPC := nextPC }
                      else
                        { s with memory := s.memory.setIfInBounds addrMem.toNat dataMem } with pc := nextPC })
        with memBusiness := memBusinessVal }
    | BFalse _ =>
      { s with rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd dataCtrl (arr_get s.rf rdIdx.toNat)), pc := nextPC }

inductive run : state → state → Prop where
| blocked : ∀ s, isWaitingMMIO s → run s s
| step : ∀ s s' , ¬ isWaitingMMIO s → run (stepOne s) s' → run s s'

-- method Action getMMIOReq(): forwarded straight through to the core's toMMIO queue.
def meth_getMMIOReq : state → t_mem → state → Prop :=
  fun s req s' => run s s' ∧ req = s'.mmioReq.get!

-- method Action getMMIOResp(Mem a): recover the pending request shape from
-- `mmioreq`, splice in the caller-supplied response data, and enqueue it into
-- the core's fromMMIO queue. (As noted above, nothing in this source
-- enqueues into `mmioreq` anymore, so this method's guard is in fact never
-- satisfiable.)
def meth_getMMIOResp (s : state) (a : t_mem) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := stepOne { s with mmioResp := some a, mmioReq := none } }
def meth_RDY_getMMIOResp (s : state) : t_bool :=
  if s.mmioReq.isSome then BTrue Unit_ else BFalse Unit_

end M_mktop_pipeliend.Spec
