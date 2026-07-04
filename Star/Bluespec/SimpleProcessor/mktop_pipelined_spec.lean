import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Basic
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
import Star.Bluespec.SimpleProcessor.mktop_pipelined
import Star.Bluespec.SimpleProcessor.core_step_lemmas
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
  -- Mirrors M_mktop_pipelined.State.halt: set by stepOne when the
  -- instruction at `pc` is illegal. `pc`/`rf`/`memory` are left unchanged
  -- (the illegal instruction never actually retires), and once set nothing
  -- ever clears it (meth_RDY_getCommit below refuses to fire again).
  halt : Bool := false
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
  -- Illegal instruction: mirror rule_RL_decode_core's `illegal` handling --
  -- nothing retires (pc/rf/memory frozen), and halt latches permanently.
  let legalCommitInfo : t_commit := { inst := instr, pc := pc, data := ite_bsv isValidRd (some finalData) none }
  let legalNewState : State :=
    { s with
        rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
        memory := newMemory,
        pc := nextPC }
  let illegalCommitInfo : t_commit := { inst := instr, pc := pc, data := none }
  match _ : dInst.legal with
  | BTrue _ => (legalNewState, legalCommitInfo)
  | BFalse _ => ({ s with halt := true }, illegalCommitInfo)

def meth_getCommit (s : State) : t_actionvalue_ t_commit State :=
  let (s', c) := stepOne s
  { avValue_ := c, avAction_ := s' }
def meth_RDY_getCommit (s : State) : t_bool := if s.halt then BFalse Unit_ else BTrue Unit_

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

-- Array helpers for the scoreboard (`sb`) interactions in the commute proofs
-- below: every rule that touches `sb` does so via a "read, add a signed
-- delta, write back" pattern (`arr_set sb idx (arr_get sb idx + delta)`).
-- These lemmas let two such updates -- from two different rules firing on
-- the same starting state, at potentially-equal or distinct indices -- be
-- shown to commute without needing to know which case (squash/normal,
-- mem/non-mem, etc.) either rule actually took.
theorem arr_set_comm {α : Type} [Inhabited α] (arr : Array α) (i j : Nat) (vi vj : α) (hij : i ≠ j) :
    arr_set (arr_set arr i vi) j vj = arr_set (arr_set arr j vj) i vi := by
  unfold arr_set
  apply Array.ext_getElem?
  intro k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> subst_vars
  · exact absurd rfl hij
  · simp_all [Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self, Ne.symm hij]
  · simp_all [Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self, Ne.symm hij]
  · simp_all [Array.getElem?_setIfInBounds_ne (Ne.symm hki), Array.getElem?_setIfInBounds_ne (Ne.symm hkj)]

theorem arr_get_arr_set_self {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (v : α) (h : i < arr.size) :
    arr_get (arr_set arr i v) i = v := by
  unfold arr_get arr_set
  simp [Array.getElem!_eq_getD, h]

theorem arr_get_arr_set_ne {α : Type} [Inhabited α] (arr : Array α) (i j : Nat) (v : α) (h : i ≠ j) :
    arr_get (arr_set arr i v) j = arr_get arr j := by
  unfold arr_get arr_set
  simp [Array.getElem!_eq_getD, h]

theorem arr_set_set_self {α : Type} (arr : Array α) (i : Nat) (v1 v2 : α) :
    arr_set (arr_set arr i v1) i v2 = arr_set arr i v2 := by
  unfold arr_set
  apply Array.ext_getElem?
  intro k
  by_cases hk : k = i <;> simp_all [Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self]

theorem arr_set_of_oob {α : Type} (arr : Array α) (i : Nat) (v : α) (h : ¬ i < arr.size) :
    arr_set arr i v = arr := by
  unfold arr_set
  simp only [Array.set!_eq_setIfInBounds]
  apply Array.ext_getElem?
  intro k
  rw [Array.getElem?_setIfInBounds]
  by_cases hk : i = k <;> simp_all

theorem arr_get_set_delta_comm {n : Nat}
    (arr : Array (BitVec n)) (i j : Nat) (di dj : BitVec n) :
    arr_set (arr_set arr i (arr_get arr i + di)) j
      (arr_get (arr_set arr i (arr_get arr i + di)) j + dj) =
    arr_set (arr_set arr j (arr_get arr j + dj)) i
      (arr_get (arr_set arr j (arr_get arr j + dj)) i + di) := by
  by_cases hij : i = j
  · subst hij
    rw [arr_set_set_self, arr_set_set_self]
    by_cases hbound : i < arr.size
    · rw [arr_get_arr_set_self _ _ _ hbound, arr_get_arr_set_self _ _ _ hbound]
      generalize arr_get arr i = x
      rw [BitVec.add_assoc, BitVec.add_comm di dj, ← BitVec.add_assoc]
    · rw [arr_set_of_oob _ _ _ hbound, arr_set_of_oob _ _ _ hbound]
  · rw [arr_get_arr_set_ne _ _ _ _ hij, arr_get_arr_set_ne _ _ _ _ (Ne.symm hij)]
    exact arr_set_comm _ _ _ _ _ hij

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
  ImplModule.getRule .rule_RL_writeback i i' := by
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
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted,
    M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq] at hc hb
  obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  rcases h : a.f2d_hasElement with _ | _
  · simp [h] at hb1
  · simp [h] at hc1

-- 3 cases total (not 8!), since `hmi` turns out to be unnecessary --
-- `rule_RL_execute_core_normal_branch` leaves isMemInst symbolic, and the
-- pc/eEp outcome is driven purely by pcMismatch regardless of mem-ness (a
-- memory instruction can never actually trigger the "taken branch" case in
-- practice, but Lean can't assume that without a reachability argument, so
-- leaving isMemInst unresolved and splitting only on pcMismatch handles the
-- adversarial "mem + redirect" case for free, with no extra proof burden).
theorem commutes_rule_RL_fetch_rule_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted] at hc
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at hb
  obtain ⟨hc_g, hc_e⟩ := Prod.mk.injEq .. |>.mp hc
  by_cases hieEp : a.d2e_element.ieEp = a.eEp
  · -- not squash: further split on pcMismatch
    by_cases hpcm : (RVUtil.execControl32 a.d2e_element.dInst.inst a.d2e_element.rv1 a.d2e_element.rv2
        (RVUtil.getImmediate a.d2e_element.dInst) a.d2e_element.pc).nextPC = a.d2e_element.ppc
    · ---------------------------------------------------------------
      -- EASY: correctly predicted (or a memory instruction, which is
      -- always "correctly predicted" in this sense) -- one-step diamond.
      ---------------------------------------------------------------
      rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
          a.d2e_hasElement a.e2w_hasElement hieEp] at hb
      simp only [hpcm] at hb
      obtain ⟨hb_g, hb_e⟩ := Prod.mk.injEq .. |>.mp hb
      refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩
      · show M_mktop_pipelined.rule_RL_execute c = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        simp only [hpcm]
        simp only [bool_and_true_iff] at hc_g hb_g
        simp [hc_g, hb_g, ite_bsv, bool_not]
      · show M_mktop_pipelined.rule_RL_fetch b = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
        rw [← hb_e]
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        simp only [hpcm]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
        simp only [bool_and_true_iff] at hc_g hb_g
        simp [hc_g, hb_g, ite_bsv, bool_not]
    · ---------------------------------------------------------------
      -- HARD: taken/mispredicted redirect. 3-step witness on the c-path
      -- (execute, decode(squash), fetch) vs 1 step on the b-path (fetch).
      ---------------------------------------------------------------
      have hpcm' : ((RVUtil.execControl32 a.d2e_element.dInst.inst a.d2e_element.rv1 a.d2e_element.rv2
            (RVUtil.getImmediate a.d2e_element.dInst) a.d2e_element.pc).nextPC == a.d2e_element.ppc) = false :=
        beq_eq_false_iff_ne'' _ _ |>.mpr hpcm
      have hpcm'' : bool_not (if (RVUtil.execControl32 a.d2e_element.dInst.inst a.d2e_element.rv1 a.d2e_element.rv2
            (RVUtil.getImmediate a.d2e_element.dInst) a.d2e_element.pc).nextPC == a.d2e_element.ppc
            then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ := by rw [hpcm']; rfl
      rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
          a.d2e_hasElement a.e2w_hasElement hieEp] at hb
      simp only [hpcm', ite_bsv, bool_not, Bool.false_eq_true, if_false] at hb
      obtain ⟨hb_g, hb_e⟩ := Prod.mk.injEq .. |>.mp hb
      have heEpNe : ¬ a.eEp + (-1 : BitVec 1) = a.eEp := by
        intro h
        have : (-1 : BitVec 1) = 0 := by
          have := congrArg (· - a.eEp) h
          simpa using this
        simp at this
      have ha_f2d : a.f2d_hasElement = false := by
        rcases h : a.f2d_hasElement with _ | _
        · rfl
        · exfalso; simp [fifo_RDY_enq, h] at hc_g
      have ha_halt : a.halt = false := by
        rcases h : a.halt with _ | _
        · rfl
        · exfalso; simp [M_mktop_pipelined.not_halted, h] at hc_g
      set c1 := (M_mktop_pipelined.rule_RL_execute c).2 with hc1_def
      have hc1_eq : c1 = { c with
          sb := a.sb, d2e_hasElement := false, dmem := execDmemNormal a.d2e_element a.dmem,
          eEp := a.eEp + (-1 : BitVec 1),
          pc := (RVUtil.execControl32 a.d2e_element.dInst.inst a.d2e_element.rv1 a.d2e_element.rv2
            (RVUtil.getImmediate a.d2e_element.dInst) a.d2e_element.pc).nextPC,
          e2w_hasElement := true,
          e2w_element := ({ data := execDataNormal a.d2e_element a.dmem, dInst := a.d2e_element.dInst, pc := a.d2e_element.pc } : t_e2w) } := by
        rw [hc1_def]
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        dsimp only
        rw [hpcm'']
        simp only [ite_bsv]
      set c2 := (M_mktop_pipelined.rule_RL_decode c1).2 with hc2_def
      have hc2_eq : c2 = { c1 with f2d_hasElement := false } := by
        rw [hc2_def]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [rule_RL_decode_core_squash_branch c1.imem c1.f2d_element c1.dEp c1.eEp c1.sb c1.rf
            c1.pc c1.d2e_element c1.halt c1.f2d_hasElement c1.d2e_hasElement
            (by simp only [hc1_eq, ← hc_e]) (by
              simp only [hc1_eq, ← hc_e]
              exact Ne.symm heEpNe)]
      have hc2_f2d : c2.f2d_hasElement = false := by rw [hc2_eq]
      have hc2_halt : c2.halt = false := by
        simp only [hc2_eq, hc1_eq, ← hc_e]; exact ha_halt
      set c3 := (M_mktop_pipelined.rule_RL_fetch c2).2 with hc3_def
      have hc3_eq : c3 = { c2 with
          f2d_hasElement := true,
          f2d_element := { pc := c2.pc, ppc := c2.pc + 4, idEp := c2.dEp, ieEp := c2.eEp },
          pc := c2.pc + 4 } := by
        rw [hc3_def]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
      set b1 := (M_mktop_pipelined.rule_RL_fetch b).2 with hb1_def
      have hb_f2d : b.f2d_hasElement = false := by simp only [← hb_e]; exact ha_f2d
      have hb_halt : b.halt = false := by simp only [← hb_e]; exact ha_halt
      have hb1_eq : b1 = { b with
          f2d_hasElement := true,
          f2d_element := { pc := b.pc, ppc := b.pc + 4, idEp := b.dEp, ieEp := b.eEp },
          pc := b.pc + 4 } := by
        rw [hb1_def]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
      have hfinal : c3 = b1 := by
        simp only [hc3_eq, hc2_eq, hc1_eq, hb1_eq, ← hb_e, ← hc_e, ite_bsv, bool_not]
      have step1 : ImplModule.getARule c c1 := ⟨.rule_RL_execute, by
        show M_mktop_pipelined.rule_RL_execute c = (BTrue Unit_, c1)
        rw [hc1_eq]
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        dsimp only
        rw [hpcm'']
        simp only [ite_bsv]
        simp only [bool_and_true_iff] at hb_g
        simp [hb_g]⟩
      have step2 : ImplModule.getARule c1 c2 := ⟨.rule_RL_decode, by
        show M_mktop_pipelined.rule_RL_decode c1 = (BTrue Unit_, c2)
        rw [hc2_eq]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [rule_RL_decode_core_squash_branch c1.imem c1.f2d_element c1.dEp c1.eEp c1.sb c1.rf
            c1.pc c1.d2e_element c1.halt c1.f2d_hasElement c1.d2e_hasElement
            (by simp only [hc1_eq, ← hc_e]) (by
              simp only [hc1_eq, ← hc_e]
              exact Ne.symm heEpNe)]
        simp [fifo_RDY_deq, hc1_eq, ← hc_e]⟩
      have step3 : ImplModule.getARule c2 c3 := ⟨.rule_RL_fetch, by
        show M_mktop_pipelined.rule_RL_fetch c2 = (BTrue Unit_, c3)
        rw [hc3_eq]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
        simp [fifo_RDY_enq, hc2_f2d, hc2_halt]⟩
      have stepb1 : ImplModule.getARule b b1 := ⟨.rule_RL_fetch, by
        show M_mktop_pipelined.rule_RL_fetch b = (BTrue Unit_, b1)
        rw [hb1_eq]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
        simp [fifo_RDY_enq, hb_f2d, hb_halt]⟩
      refine ⟨c3, ?_, hfinal ▸ ?_⟩
      · exact .tail (.tail (.single step1) step2) step3
      · exact .single stepb1
  · ---------------------------------------------------------------
    -- EASY: squash (stale ieEp) -- one-step diamond.
    ---------------------------------------------------------------
    rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
        a.d2e_hasElement a.e2w_hasElement hieEp] at hb
    dsimp only at hb
    obtain ⟨hb_g, hb_e⟩ := Prod.mk.injEq .. |>.mp hb
    refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩
    · show M_mktop_pipelined.rule_RL_execute c = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
      dsimp only [M_mktop_pipelined.rule_RL_execute]
      rw [← hc_e]
      dsimp only
      rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
          a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
      simp only [bool_and_true_iff] at hc_g hb_g
      simp [hc_g, hb_g]
    · show M_mktop_pipelined.rule_RL_fetch b = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
      rw [← hb_e]
      dsimp only [M_mktop_pipelined.rule_RL_execute]
      rw [← hc_e]
      dsimp only
      rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
          a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
      dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted]
      simp only [bool_and_true_iff] at hc_g hb_g
      simp [hc_g, hb_g]

theorem commutes_rule_RL_fetch_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : RVUtil.isMemoryInst a.e2w_element.dInst = mi at hc hb hc1 hb1 ⊢;
     cases mi <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       simp_all)

theorem commutes_rule_RL_decode_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core,
    M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq] at hc hb
  obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  rcases h : a.f2d_hasElement with _ | _
  · simp [h] at hc1
  · simp [h] at hb1

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
  -- Likely needs a genuine multi-step reconvergence proof, same flavor as
  -- commutes_rule_RL_fetch_rule_RL_execute, not a one-step diamond -- and unlike
  -- that lemma this one isn't yet confirmed provable. Since execute requires
  -- d2e full, decode's *normal* branch (which needs d2e empty to enqueue) is
  -- guard-excluded when firing on `a` directly, forcing decode-on-a into its
  -- squash branch (a pure passthrough, no real interaction). But when decode
  -- instead fires on `b` (state after execute), `b.d2e_hasElement` is always
  -- false (execute unconditionally clears it) and `b.eEp` may have been bumped
  -- by execute's own branch resolution -- so decode-on-b's epoch-mismatch
  -- determination reads a *different* eEp than decode-on-a did, and since eEp
  -- is a single bit (BitVec 1), a squash-due-to-ieEp-mismatch on `a` can flip to
  -- a *non*-squash (normal decode, real d2e write) on `b`. Reconverging that
  -- with the squash-only witness on the other side needs the same kind of
  -- bounded multi-step derivation as the fetch/execute pc race, not yet
  -- worked out here.
  sorry

theorem commutes_rule_RL_decode_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  -- TRUE, but needs (a) an added scoreboard invariant hypothesis and (b) a
  -- genuine multi-step (decode-then-execute) reconvergence proof, not a
  -- one-step diamond. Two-part finding, worked out but not yet landed here:
  --
  -- (a) GUARD-LEVEL ISSUE (RESOLVED): rule_RL_writeback_core's fire-guard never
  -- checks `sb`, so an *unconstrained* state `a` with `a.sb[R] = 0` (decode's
  -- rs1Ready/rs2Ready check passes) while `a.e2w_element.dInst` simultaneously
  -- targets `rd = R` with isValidRd = true is type-valid -- confirmed by direct
  -- computation, firing writeback wraps sb[R] from 0 to 3#2, flipping decode's
  -- ready check. This is fixed by adding the standard scoreboard invariant as a
  -- hypothesis: `sb_e2w_inv : a.e2w_hasElement → a.e2w_element.dInst.valid_rd →
  -- rd ≠ 0 → a.sb[rd] ≠ 0` (verified in a scratch proof: with this in hand,
  -- case-splitting decode's epochMismatch and the isJAL/isJALR discriminants
  -- closes the guard/pc/dEp parts of the diamond cleanly, using
  -- arr_get_set_delta_comm for the `sb` array-commuting part).
  --
  -- (b) VALUE-LEVEL ISSUE (helper lemmas built, not yet wired in): decode
  -- stores rv1/rv2 (raw rf reads) into d2e *unconditionally*, even when
  -- valid_rs1/valid_rs2 = false (usesRS1/usesRS2 are pure functions of the
  -- opcode bits, not the register-index bits -- e.g. LUI's immediate bits can
  -- coincidentally equal R). So even with (a), decode-on-a and decode-on-b can
  -- read a different (architecturally unused) rf value at that index, making
  -- the two d2e states literally unequal. Resolving this needs one more step
  -- (execute) on both sides, showing execute's actual output doesn't depend on
  -- that stray value -- true for every real RV32I opcode, false only for
  -- SYSTEM-class/reserved encodings (bit2(inst)=0 with invalid rs1/rs2), which
  -- this simplified core's pipeline never gates out (isLegalInstruction is
  -- computed but checked nowhere). See RVUtil_rv_irrelevance.lean for the
  -- (mostly proven) supporting lemmas and exact remaining TODOs -- not yet
  -- imported/used here.
  sorry

theorem commutes_rule_RL_execute_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_rule_RL_fetch_rule_RL_execute hb hc
  exact ⟨d, hd2, hd1⟩

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
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core,
      M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : bool_not (if a.d2e_element.ieEp == a.eEp then BTrue Unit_ else BFalse Unit_) = iem at hc hb hc1 hb1 ⊢;
     cases iem <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       (try rw [arr_get_set_delta_comm]) <;>
       simp_all)

theorem commutes_rule_RL_writeback_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.not_halted] at hc hb ⊢ <;>
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
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     generalize hm : bool_not (if a.d2e_element.ieEp == a.eEp then BTrue Unit_ else BFalse Unit_) = iem at hc hb hc1 hb1 ⊢;
     cases iem <;>
       simp only [fifo_RDY_enq, fifo_RDY_deq] at hc hb hc1 hb1 ⊢ <;>
       (try rw [arr_get_set_delta_comm]) <;>
       simp_all)

theorem commutes_rule_RL_writeback_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_writeback a b →
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
