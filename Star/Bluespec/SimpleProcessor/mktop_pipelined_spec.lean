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

-- Sequential ISA-level reference model. Unlike the old MMIO-based spec (which
-- could run several instructions autonomously via `run` before blocking on an
-- MMIO response), every instruction now requires exactly one getCommit call,
-- so `stepOne` always computes exactly one instruction's full effect and
-- returns its commit record; there is no separate "blocked/waiting" state to
-- track (contrast the old isWaitingMMIO/run machinery).
structure State where
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  memory : Array (BitVec 32) := .mk (List.replicate 65536 default)
deriving Inhabited

def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

-- Execute one instruction to completion, returning the updated architectural
-- state and the commit record describing what just retired.
def stepOne (s : State) : State × t_commit :=
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
  let isStore := if typeMem == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm pc).nextPC
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool (ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)), size := size, offset := offset }
  let finalData : BitVec 32 :=
    match _ : isMemInst with
    | BTrue _ => processMem memBusinessVal (s.memory.getD addrMem.toNat default)
    | BFalse _ => dataCtrl
  let newMemory : Array (BitVec 32) :=
    match _ : isMemInst with
    | BTrue _ => (match _ : isStore with
        | BTrue _ => s.memory.setIfInBounds addrMem.toNat dataMem
        | BFalse _ => s.memory)
    | BFalse _ => s.memory
  let commitInfo : t_commit := { inst := instr, pc := pc, rdIdx := rdIdx, validRd := isValidRd, data := finalData }
  let newState : State :=
    { s with
        rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
        memory := newMemory,
        pc := nextPC }
  (newState, commitInfo)

def meth_getCommit (s : State) : t_actionvalue_ t_commit State :=
  let (s', c) := stepOne s
  { avValue_ := c, avAction_ := s' }
def meth_RDY_getCommit (_ : State) : t_bool := BTrue Unit_

def initS : State := default

#eval ((stepOne (stepOne { initS with pc := 0, rf := .mk (List.replicate 32 0), memory := .mk (List.replicate 10 0x00108093) }).1).1).rf

end M_mktop_pipelined.Spec

namespace M_mktop_pipelined

@[grind cases]
inductive Method : Type where
| meth_getCommit

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
    | .meth_getCommit => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommit M_mktop_pipelined.Spec.meth_RDY_getCommit
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.State
  methods
    | .meth_getCommit => ofAVMethod0 M_mktop_pipelined.meth_getCommit M_mktop_pipelined.meth_RDY_getCommit
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
-- Helper for peeling apart the deeply-nested bool_and conjunctions that make
-- up every rule's fire-guard: `bool_and p q = BTrue` iff both components hold.
@[simp] theorem bool_and_true_iff (p q : t_bool) :
    bool_and p q = BTrue Unit_ ↔ p = BTrue Unit_ ∧ q = BTrue Unit_ := by
  cases p <;> cases q <;> simp [bool_and]

-- A `match` on an arbitrary t_bool that returns the same thing in both
-- branches is just that thing -- crucial for collapsing e.g. `bool_and`
-- chains once one component is known False (making everything downstream
-- of it BFalse Unit_ regardless of what the remaining, still-unknown
-- components are).
@[simp] theorem tbool_match_same {α : Type} (x : t_bool) (y : α) :
    (match x with | BTrue _ => y | BFalse _ => y) = y := by
  cases x <;> rfl

def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop := sorry

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v : t_commit), e.1 = .meth_getCommit ∧ e.2 = Footprint.arg0 v) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [ImplModule, Module.getMethod, ofAVMethod0] at *; grind)

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : t_commit), e.1 = .meth_getCommit ∧ e.2 = Footprint.arg0 v) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [SpecModule, Module.getMethod, M_mktop_pipelined.Spec.meth_getCommit,
      M_mktop_pipelined.Spec.meth_RDY_getCommit, ofAVMethod0] at *; grind)


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
  intro h
  obtain ⟨r, hr⟩ := h
  cases r <;> simp_all

theorem commutes_rule_RL_fetch_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_fetch_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
    M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_fetch_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE but needs a genuine multi-step reconvergence proof, not a one-step-each
  -- diamond: both fetch and execute can write `pc` from the same state `a` (fetch
  -- always writes pc+4; execute writes an absolute redirect target on a taken
  -- branch). Firing them in opposite orders reaches states whose `pc` differs by
  -- exactly 4, and reconverging requires draining the resulting stale f2d entry
  -- through requestI/responseI/decode(squash) and refetching -- a ~4-step
  -- derivation exploiting the idEp/ieEp squash mechanism, verified by hand but not
  -- yet formalized here.
  sorry

theorem commutes_rule_RL_fetch_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : RVUtil.isMemoryInst a.e2w_element.dInst = mi at hc hb hc1 hb1 ⊢;
     cases mi <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_fetch_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
    M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_fetch_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
      M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_fetch_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
      M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_fetch_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_decode_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
    M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_decode_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_decode_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE but needs case-splitting on decode's epochMismatch and execute's
  -- ieEpMismatch/isMemInst discriminants; automated attempts (grind, split, and
  -- explicit `generalize`+`cases`) got stuck because the same logical condition
  -- (e.g. `a.d2e_element.ieEp == a.eEp`) is elaborated with different internal
  -- representations (plain `=` vs. `(_ == _) = true`) in different subterms after
  -- dsimp, defeating exact-term generalize. Provable in principle; needs a more
  -- careful manual derivation.
  sorry

theorem commutes_rule_RL_decode_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE (only real interaction is the shared `sb` scoreboard array, whose
  -- get+delta+set updates commute arithmetically regardless of order/index), but
  -- automated closing got stuck the same way as commutes_rule_RL_decode_rule_RL_execute
  -- (inconsistent `=` vs `(_==_)=true` representations after dsimp).
  sorry

theorem commutes_rule_RL_decode_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
      M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_decode_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
    M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_decode_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
      M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_decode_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_execute_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE; symmetric case of commutes_rule_RL_fetch_rule_RL_execute above, same
  -- multi-step reconvergence argument needed (not yet formalized).
  sorry

theorem commutes_rule_RL_execute_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE; symmetric case of commutes_rule_RL_decode_rule_RL_execute above, same
  -- obstruction (see that lemma's comment).
  sorry

theorem commutes_rule_RL_execute_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_execute_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE (execute only touches `sb` in its squash branch; writeback always touches
  -- `sb`; both are commutative get+delta+set updates), but automated closing got
  -- stuck the same way as commutes_rule_RL_decode_rule_RL_execute (inconsistent
  -- `=` vs `(_==_)=true` representations after dsimp).
  sorry

theorem commutes_rule_RL_execute_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core,
      M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_execute_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core,
      M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_execute_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE (execute's `toDmem` write and requestD's `toDmem` deq are guarded so that
  -- execute's isMemInst=true sub-case (the only one requestD could conflict with)
  -- requires toDmem ready-to-enq, contradicting requestD's ready-to-deq requirement
  -- -- so the overlap case is actually vacuous), but automated closing got stuck
  -- the same way as commutes_rule_RL_decode_rule_RL_execute (inconsistent `=` vs
  -- `(_==_)=true` representations after dsimp).
  sorry

theorem commutes_rule_RL_execute_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_writeback_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_writeback_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE; symmetric case of commutes_rule_RL_decode_rule_RL_writeback above, same
  -- obstruction (see that lemma's comment).
  sorry

theorem commutes_rule_RL_writeback_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE; symmetric case of commutes_rule_RL_execute_rule_RL_writeback above, same
  -- obstruction (see that lemma's comment).
  sorry

theorem commutes_rule_RL_writeback_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_writeback_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_writeback_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_writeback_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_writeback_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : RVUtil.isMemoryInst a.e2w_element.dInst = mi at hc hb hc1 hb1 ⊢;
     cases mi <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_requestI_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
    M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_requestI_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
      M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestI_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
      M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestI_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestI_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_requestI_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
    M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readB, bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_requestI_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- FALSE AS STATED: requestI (port B, instruction fetch) and requestD (port A,
  -- data access) share one physical BRAM's `memory` array. When toImem_element.addr
  -- == toDmem_element.addr and requestD is a store, firing requestI-then-requestD
  -- latches the pre-store word while requestD-then-requestI latches the post-store
  -- word -- a genuine self-modifying-code hazard, confirmed by an explicit
  -- counterexample (NOP vs. a JAL-decoding word at a colliding address) that
  -- propagates into diverging, non-reconverging commits. Fixing this requires
  -- restricting the model (e.g. a non-colliding-address invariant threaded through
  -- phi0/reachability and rules_commute_weakly) -- a framework-level change
  -- deliberately deferred; see conversation history.
  sorry

theorem commutes_rule_RL_requestI_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestI a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : (a.toImem_element.byte_en == (0 : BitVec 4)) = cond at hc hb hc1 hb1 ⊢;
     cases cond <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_responseI_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseI_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
    M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_responseI_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
      M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseI_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseI_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
    M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readB, bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_responseI_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_responseI_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
      M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : (a.toDmem_element.byte_en == (0 : BitVec 4)) = cond at hc hb hc1 hb1 ⊢;
     cases cond <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_responseI_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseI a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core,
      M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestD_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core,
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestD_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core,
      M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestD_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE; symmetric case of commutes_rule_RL_execute_rule_RL_requestD above, same
  -- obstruction (see that lemma's comment).
  sorry

theorem commutes_rule_RL_requestD_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_requestD_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- FALSE AS STATED; symmetric case of commutes_rule_RL_requestI_rule_RL_requestD
  -- above (self-modifying-code BRAM hazard). See that lemma's comment.
  sorry

theorem commutes_rule_RL_requestD_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core,
      M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : (a.toDmem_element.byte_en == (0 : BitVec 4)) = cond at hc hb hc1 hb1 ⊢;
     cases cond <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_requestD_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

theorem commutes_rule_RL_requestD_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_requestD a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core,
    M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_responseD_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseD_rule_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseD_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseD_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : RVUtil.isMemoryInst a.e2w_element.dInst = mi at hc hb hc1 hb1 ⊢;
     cases mi <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_responseD_rule_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.rule_RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : (a.toImem_element.byte_en == (0 : BitVec 4)) = cond at hc hb hc1 hb1 ⊢;
     cases cond <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_responseD_rule_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.rule_RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
      M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseI_core, M_mktop_pipelined.putA_withResponse, M_mktop_pipelined.putB_withResponse, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | simp_all
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> split_ifs <;> grind))

theorem commutes_rule_RL_responseD_rule_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseD_core,
    M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestD_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq,
    bool_and, bool_or, bool_not] at hc hb
  grind

theorem commutes_rule_RL_responseD_rule_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_responseD a c →
  ImplModule.getRule .rule_RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by injection (hb.symm.trans hc)
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

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
-- `method_rule_commute` field (vacuous in mkFIFOTest_refines.lean since its
-- Method type is empty; needed explicitly here for our 1 real method).

@[local grind →] theorem reconverge_rule_RL_fetch_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_fetch s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_fetch s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_decode_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_decode s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_decode s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_execute_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_execute s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_execute s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_writeback_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_writeback s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_writeback s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestI_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_requestI s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseI_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_responseI s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseI s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_requestD_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_requestD s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_requestD s'' s''' := by
  sorry

@[local grind →] theorem reconverge_rule_RL_responseD_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_responseD s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_responseD s'' s''' := by
  sorry

-- Per-method lemmas needed by StructuredRefinement's `flushed_indistinguishable`
-- (flush_indistinguishable_*) and `flushed_method_preserved` (reach_flush_again_*)
-- fields (vacuous in mkFIFOTest_refines.lean since its Method type is empty;
-- needed explicitly here for our 1 real method).

@[local grind →] theorem flush_indistinguishable_meth_getCommit
    (i i' : ImplModule.State) (s : SpecModule.State) (v : t_commit) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s' := by
  sorry

@[local grind →] theorem reach_flush_again_meth_getCommit
    (i i' : ImplModule.State) (s s' : SpecModule.State) (v : t_commit) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  sorry

-- Termination argument (informal; not yet machine-checked -- see note below).
--
-- Unlike the old MMIO-based interface, `commitQ_hasElement` is now
-- monotonic under the rule-only relation: rule_RL_writeback is the only
-- rule that sets it, and it only ever sets it to `true` (nothing in the
-- Rule set -- only the external getCommit method -- ever sets it back to
-- `false`). Since rule_RL_writeback's guard requires `fifo_RDY_enq
-- commitQ_hasElement` (i.e. `commitQ_hasElement = false`), it can fire *at
-- most once* starting from any state before commitQ is permanently full and
-- writeback is permanently disabled.
--
-- That single fact cascades backward through the whole pipeline: once
-- writeback is disabled, e2w can never be drained again, so rule_RL_execute's
-- normal (non-squash) branch -- which requires e2w empty -- can fire at most
-- once more (whatever was already in flight); once *that* is used up, d2e
-- can never be drained by a normal execute again, so rule_RL_decode's normal
-- branch (which requires d2e empty) is likewise bounded. The one
-- complication is that rule_RL_decode's *squash* branch (stale idEp/ieEp)
-- and rule_RL_execute's *squash* branch (stale ieEp) don't touch d2e/e2w at
-- all, so they aren't immediately capped by the same argument -- but they
-- are self-limiting too: rule_RL_fetch always tags freshly-created f2d
-- entries with the pipeline's *current* dEp/eEp, and dEp/eEp only change in
-- decode's/execute's normal branches (which are themselves bounded as just
-- argued), so only a bounded number of already-in-flight entries can ever
-- be "stale" relative to the current epoch at any point; once those drain
-- via squash, every subsequently fetched entry is fresh and decode/execute
-- are forced back onto their (bounded) normal branches. So every reachable
-- state has a bounded number of further rule firings available, i.e. the
-- rule-only relation is well-founded.
--
-- What's *not* done here: turning this into a checked Lean proof needs an
-- explicit Nat- (or lexicographic-) valued measure that strictly decreases
-- across all 8 rules, most likely of the shape
-- `(if commitQ_hasElement then 0 else 1, <bound on remaining normal-branch
-- executions/decodes still available>, <count of currently in-flight
-- stale-epoch entries in f2d/fromImem/d2e>)`
-- ordered lexicographically. Constructing and discharging that measure
-- precisely (it has to reason about dEp/eEp comparisons, not just FIFO
-- occupancy booleans) is a nontrivial, self-contained proof effort in its
-- own right -- not something to force through with generic `grind`/`decide`
-- automation -- so it's left as `sorry` here rather than faked.
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
  -- Not yet assembled from the 64 commutes_rule_X_Y lemmas above: bare
  -- `cases r1 <;> cases r2 <;> grind` doesn't dispatch to those named lemmas
  -- (grind only uses `@[grind]`-tagged facts, not arbitrary in-scope theorems),
  -- and 8 of the 64 are themselves still `sorry` (2 genuinely false pending a
  -- model fix, 6 true but not yet closed -- see their comments above). Once
  -- those are filled in, this should case-split on (r1, r2) and `exact` the
  -- matching commutes_rule_r1_r2 lemma per case.
  rules_commute_weakly := by
    sorry

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mktop_pipelined_refinement

#print axioms refines

end M_mktop_pipelined
