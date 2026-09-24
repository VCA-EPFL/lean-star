import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Processor.Params_types
import Star.Bluespec.Processor.RVUtil
import Star.Bluespec.Lib.mkSimpleBRAM
import Star.Bluespec.Lib.mkFIFO
import Star.Bluespec.Processor.mktop_pipelined
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
open BluespecPrelude
open Params_types
open BluespecVerification
open ReachingStar Bluespec

set_option maxHeartbeats 1000000

-- ═══ Specification (fill in State, methods, and phi0) ═══

namespace M_mktop_pipelined.Spec

structure State where
  pc : BitVec 32
  halted : BitVec 1
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  imem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  dmem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  output : List t_commitinst
deriving Inhabited

def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

def stepOne (s : State) : State :=
  let pc := s.pc
  let instr := s.imem.getD pc.toNat default
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
  let addrMem : BitVec 30 := extract_bits addr0 31 2
  let isUnsignedMem := extract_bit funct3 2
  let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_) byteEn (0 : BitVec 4)
  let isStore := if typeMem != (0 : BitVec 4) then BTrue Unit_ else BFalse Unit_
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm pc).nextPC
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool (ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)), size := size, offset := offset }
  let finalData : BitVec 32 :=
    match _ : isMemInst with
    | BTrue _ => processMem memBusinessVal (s.dmem.getD addrMem.toNat default)
    | BFalse _ => dataCtrl
  let newDmem : Array (BitVec 32) :=
    match _ : isMemInst with
    | BTrue _ => (match _ : isStore with
        | BTrue _ => s.dmem.setIfInBounds addrMem.toNat dataMem
        | BFalse _ => s.dmem)
    | BFalse _ => s.dmem
  let legalCommitInfo : t_commitinst := { inst := instr, pc := pc, rd := rdIdx, data := ite_bsv isValidRd finalData 0 }
  let legalNewState : State :=
    { s with
        rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
        dmem := newDmem,
        pc := nextPC,
        output := legalCommitInfo :: s.output }
  let illegalNewState : State := { s with pc := pc + (4 : BitVec 32), halted := 1 }
  match _ : dInst.legal with
  | BTrue _ => legalNewState
  | BFalse _ => illegalNewState

def meth_doFetch (s : State) : t_actionvalue_ Unit State :=
  let s' := stepOne s
  { avValue_ := (), avAction_ := s' }
def meth_RDY_doFecth (_ : State) : t_bool := BTrue Unit_

def meth_getCommitInst (s : State) : t_actionvalue_ t_commitinst State :=
  let c := s.output.head!
  let s' := { s with output := s.output.tail! }
  { avValue_ := c, avAction_ := s' }
def meth_RDY_getCommitInst (s : State) : t_bool :=
  if !s.output.isEmpty then BTrue Unit_ else BFalse Unit_

def initS : State := default

#eval ((stepOne (stepOne { initS with pc := 0, rf := .mk (List.replicate 32 0), imem := .mk (List.replicate 10 0x00108093) }))).rf

end M_mktop_pipelined.Spec

namespace M_mktop_pipelined.Refines

@[grind cases]
inductive Method : Type where
| doFetch
| getCommitInst

@[grind cases]
inductive Rule : Type where
| RL_requestI
| RL_responseI
| RL_requestD
| RL_responseD
| RL_decode
| RL_execute
| RL_writeback

def SpecModule : Bluespec.Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.Spec.meth_doFetch M_mktop_pipelined.Spec.meth_RDY_doFecth
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.state
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.meth_doFetch M_mktop_pipelined.meth_RDY_doFetch
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules
    | .RL_requestI => ofRule M_mktop_pipelined.rule_RL_requestI
    | .RL_responseI => ofRule M_mktop_pipelined.rule_RL_responseI
    | .RL_requestD => ofRule M_mktop_pipelined.rule_RL_requestD
    | .RL_responseD => ofRule M_mktop_pipelined.rule_RL_responseD
    | .RL_decode => ofRule M_mktop_pipelined.rule_RL_decode
    | .RL_execute => ofRule M_mktop_pipelined.rule_RL_execute
    | .RL_writeback => ofRule M_mktop_pipelined.rule_RL_writeback

-- The abstraction relation (the user's `phi0`); couples impl and spec state.
def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop := sorry

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v : unit_), e.1 = .doFetch ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (v : t_commitinst), e.1 = .getCommitInst ∧ e.2 = (Footprint.arg0 v)) := by
  sorry

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : unit_), e.1 = .doFetch ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (v : t_commitinst), e.1 = .getCommitInst ∧ e.2 = (Footprint.arg0 v)) := by
  sorry

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .RL_requestI i i' ∨ ImplModule.getRule .RL_responseI i i' ∨ ImplModule.getRule .RL_requestD i i' ∨ ImplModule.getRule .RL_responseD i i' ∨ ImplModule.getRule .RL_decode i i' ∨ ImplModule.getRule .RL_execute i i' ∨ ImplModule.getRule .RL_writeback i i' := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_requestD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_responseD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_decode_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_writeback_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem reconverge_RL_requestI_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_requestI s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_requestI_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_requestI s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_responseI_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_responseI s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_responseI_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_responseI s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_requestD_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_requestD s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_requestD_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_requestD s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_responseD_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_responseD s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_responseD_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_responseD s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_decode_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_decode s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_decode s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_decode_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_decode s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_decode s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_execute_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_execute s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_execute s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_execute_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_execute s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_execute s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_writeback_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_writeback s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_writeback s'' s''' := by
  sorry

@[local grind →] theorem reconverge_RL_writeback_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_writeback s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_writeback s'' s''' := by
  sorry

@[local grind →] theorem phi0_indistinguishable_doFetch (i i' : ImplModule.State) (s : SpecModule.State) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.doFetch, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s' := by
  sorry

@[local grind →] theorem phi0_indistinguishable_getCommitInst (i i' : ImplModule.State) (s : SpecModule.State) (v : t_commitinst) :
  phi0 i s →
  ImplModule.getMethod i ⟨.getCommitInst, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s' := by
  sorry

@[local grind →] theorem reach_phi0_again_doFetch (i i' : ImplModule.State) (s s' : SpecModule.State) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.doFetch, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  sorry

@[local grind →] theorem reach_phi0_again_getCommitInst (i i' : ImplModule.State) (s s' : SpecModule.State) (v : t_commitinst) :
  phi0 i s →
  ImplModule.getMethod i ⟨.getCommitInst, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_requestI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_responseI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_requestD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestD i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_responseD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseD i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_decode (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_decode i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_execute (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_execute i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_writeback (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_writeback i i' → phi0 i' s := by
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
  method_rule_commute := by intro a b c e h hm; obtain ⟨r, hr⟩ := h; cases r <;> grind

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mktop_pipelined_refinement

#print axioms refines

end M_mktop_pipelined.Refines
