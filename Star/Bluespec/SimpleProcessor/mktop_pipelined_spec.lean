import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Basic
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
import Star.Bluespec.SimpleProcessor.mktop_pipelined
open BluespecPrelude
open BluespecVerification
open ReachingStar Bluespec
open Params_types

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace M_mktop_pipelined.Spec
structure State where
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  memory : Array (BitVec 32) := .mk (List.replicate 65536 default)
  mmioReq : Option t_mem
  mmioResp : Option t_mem
  memBusiness : t_membusiness
  decodedInst : RVUtil.DecodedInst
  nextPC : BitVec 32
deriving Inhabited

def isWaitingMMIO (s : State) := s.mmioReq.isSome

def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

def stepOne (s : State) : State :=
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
    let funct3 := fields.funct3
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
      (match _ : mmioTarget with
        | BTrue _ =>
          { s with mmioReq := some reqMem, decodedInst := dInst, nextPC := nextPC, memBusiness := memBusinessVal }
        | BFalse _ => { if typeMem == 0 then
                        let finalMem := processMem memBusinessVal (s.memory.getD addrMem.toNat default)
                        { s with rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalMem (arr_get s.rf rdIdx.toNat)) }
                      else
                        { s with memory := s.memory.setIfInBounds addrMem.toNat dataMem } with pc := nextPC })
    | BFalse _ =>
      { s with rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd dataCtrl (arr_get s.rf rdIdx.toNat)), pc := nextPC }

inductive run : State → State → Prop where
| blocked : ∀ s, isWaitingMMIO s → run s s
| step : ∀ s s' , ¬isWaitingMMIO s → run (stepOne s) s' → run s s'

def meth_getMMIOReq : Footprint → State → State → Prop :=
  fun e s s' =>
    ∃ req, run s s'
            ∧ req = s'.mmioReq.get!
            ∧ e = Footprint.arg0 req

def meth_getMMIOResp (s : State) (a : t_mem) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_, avAction_ := stepOne { s with mmioResp := some a, mmioReq := none } }
def meth_RDY_getMMIOResp (s : State) : t_bool :=
  if s.mmioReq.isSome then BTrue Unit_ else BFalse Unit_

def initS : State := default

#eval (stepOne $ stepOne { initS with pc := 0, rf := .mk (List.replicate 32 0), memory := .mk (List.replicate 10 0x00108093) }).rf

end M_mktop_pipelined.Spec

namespace M_mktop_pipelined

@[grind cases]
inductive Method : Type where
| meth_getMMIOReq
| meth_getMMIOResp

@[grind cases]
inductive Rule : Type where
| rule_RL_fetch
| rule_RL_decode
| rule_RL_execute
| rule_RL_writeback
| rule_RL_requestI
| rule_RL_responseI
| rule_RL_requestD
| rule_RL_responseD

def SpecModule : Bluespec.Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .meth_getMMIOReq => M_mktop_pipelined.Spec.meth_getMMIOReq
    | .meth_getMMIOResp => ofAVMethod1 M_mktop_pipelined.Spec.meth_getMMIOResp M_mktop_pipelined.Spec.meth_RDY_getMMIOResp
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.State
  methods
    | .meth_getMMIOReq => ofAVMethod0 M_mktop_pipelined.meth_getMMIOReq M_mktop_pipelined.meth_RDY_getMMIOReq
    | .meth_getMMIOResp => ofAVMethod1 M_mktop_pipelined.meth_getMMIOResp M_mktop_pipelined.meth_RDY_getMMIOResp
  rules
    | .rule_RL_fetch => ofRule M_mktop_pipelined.rule_RL_fetch
    | .rule_RL_decode => ofRule M_mktop_pipelined.rule_RL_decode
    | .rule_RL_execute => ofRule M_mktop_pipelined.rule_RL_execute
    | .rule_RL_writeback => ofRule M_mktop_pipelined.rule_RL_writeback
    | .rule_RL_requestI => ofRule M_mktop_pipelined.rule_RL_requestI
    | .rule_RL_responseI => ofRule M_mktop_pipelined.rule_RL_responseI
    | .rule_RL_requestD => ofRule M_mktop_pipelined.rule_RL_requestD
    | .rule_RL_responseD => ofRule M_mktop_pipelined.rule_RL_responseD

-- The abstraction relation (the user's `phi0`); couples impl and spec state.
def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop := sorry

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v : t_mem), e.1 = .meth_getMMIOReq ∧ e.2 = Footprint.arg0 v) ∨
    (∃ (a : t_mem) (v : unit_), e.1 = .meth_getMMIOResp ∧ e.2 = Footprint.arg1 a v) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [ImplModule, Module.getMethod, ofAVMethod0, ofAVMethod1] at *; grind)

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : t_mem), e.1 = .meth_getMMIOReq ∧ e.2 = Footprint.arg0 v) ∨
    (∃ (a : t_mem) (v : unit_), e.1 = .meth_getMMIOResp ∧ e.2 = Footprint.arg1 a v) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [SpecModule, Module.getMethod, M_mktop_pipelined.Spec.meth_getMMIOReq,
      M_mktop_pipelined.Spec.meth_getMMIOResp, M_mktop_pipelined.Spec.meth_RDY_getMMIOResp,
      ofAVMethod1] at *; grind)


@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .rule_RL_fetch i i' ∨
  ImplModule.getRule .rule_RL_decode i i' ∨
  ImplModule.getRule .rule_RL_execute i i' ∨
  ImplModule.getRule .rule_RL_writeback i i' ∨
  ImplModule.getRule .rule_RL_requestI i i' ∨
  ImplModule.getRule .rule_RL_responseI i i' ∨
  ImplModule.getRule .rule_RL_requestD i i' ∨
  ImplModule.getRule .rule_RL_responseD i i' := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_fetch_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_decode_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_execute_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_writeback_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestI_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseI_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_requestD_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_rule_RL_responseD_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_fetch (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_fetch i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_decode (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_decode i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_execute (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_execute i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_writeback (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_writeback i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_requestI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_requestI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_responseI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_responseI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_requestD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_requestD i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_rule_RL_responseD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_responseD i i' → phi0 i' s := by
  sorry

-- Rule/method reconvergence lemmas needed by StructuredRefinement's
-- `method_rule_commute` field (again, vacuous in mkFIFOTest_refines.lean since
-- its Method type is empty; needed explicitly here for our 2 real methods).

@[local grind →] theorem reconverge_rule_RL_fetch_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_fetch s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_fetch s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_fetch_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_fetch s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_fetch s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_decode_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_decode s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_decode s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_decode_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_decode s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_decode s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_execute_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_execute s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_execute s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_execute_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_execute s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_execute s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_writeback_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_writeback s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_writeback s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_writeback_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_writeback s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_writeback s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestI_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_requestI s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestI_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_requestI s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseI_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_responseI s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseI_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_responseI s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestD_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_requestD s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestD_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_requestD s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseD_meth_getMMIOReq (s s' s'' : ImplModule.State) (v : t_mem) :
  ImplModule.getRule .rule_RL_responseD s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseD_meth_getMMIOResp (s s' s'' : ImplModule.State) (a : t_mem) (v : unit_) :
  ImplModule.getRule .rule_RL_responseD s s' →
  ImplModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseD s'' s''' := by
  sorry

-- Per-method lemmas needed by StructuredRefinement's `flushed_indistinguishable`
-- (flush_indistinguishable_*) and `flushed_method_preserved` (reach_flush_again_*)
-- fields (mkFIFOTest_refines.lean's Method type is empty so these are vacuous
-- there; ours has 2 real methods, so they're needed explicitly here).

@[local grind →] theorem flush_indistinguishable_meth_getMMIOReq
    (i i' : ImplModule.State) (s : SpecModule.State) (v : t_mem) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s' := by
  sorry

@[local grind →] theorem flush_indistinguishable_meth_getMMIOResp
    (i i' : ImplModule.State) (s : SpecModule.State) (a : t_mem) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s' := by
  sorry

@[local grind →] theorem reach_flush_again_meth_getMMIOReq
    (i i' : ImplModule.State) (s s' : SpecModule.State) (v : t_mem) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.meth_getMMIOReq, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  sorry

@[local grind →] theorem reach_flush_again_meth_getMMIOResp
    (i i' : ImplModule.State) (s s' : SpecModule.State) (a : t_mem) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ i' →
  SpecModule.getMethod s ⟨.meth_getMMIOResp, Footprint.arg1 a v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  sorry

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  sorry

-- ──────────────────────────────────────────────────────────────────────
-- Below: fixed generic boilerplate (closes `refines` via enough_star).
-- ──────────────────────────────────────────────────────────────────────

attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

def mktop_pipelined_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := phi0
  rules_strongly_normalising := rules_strongly_normalising
  -- Split on both the rule and the method name first (16 concrete goals, one
  -- per reconverge_r_m lemma) rather than letting a bare `grind` see all 16 at
  -- once, for the same reason rules_commute_weakly needed an explicit split.
  method_rule_commute := by
    intro a b c e h hm
    obtain ⟨r, hr⟩ := h
    obtain ⟨name, footprint⟩ := e
    cases r <;> cases name <;> grind
  -- Explicit case split (rather than the default `by grind`): with 8 rules and
  -- 64 pairwise commute_* lemmas, letting grind consider all of them at once
  -- for a single combined goal blows past its term-generation limit. Splitting
  -- into 64 concrete (r1, r2) goals first means each one only needs the one
  -- matching commutes_r1_r2 lemma.
  rules_commute_weakly := by
    intro a b c hbc hab
    obtain ⟨r1, hr1⟩ := hab
    obtain ⟨r2, hr2⟩ := hbc
    cases r1 <;> cases r2 <;> grind

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mktop_pipelined_refinement

#print axioms refines

end M_mktop_pipelined
