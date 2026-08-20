import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Basic
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
import Star.Bluespec.SimpleProcessor.mktop_pipelined
import Star.Bluespec.SimpleProcessor.core_step_lemmas
import Star.Bluespec.SimpleProcessor.RVUtil_rv_irrelevance
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
-- `imem`/`dmem` are split (rather than a single unified `memory`, as a naive
-- sequential ISA model would have) to match `M_mktop_pipelined.State`'s own
-- split -- see that file's header for why (avoiding a self-modifying-code
-- hazard by construction). `imem` is never written by any rule (mirroring
-- the impl, where nothing ever writes `imem` either), so this refinement is
-- only meaningful for programs that don't rely on writing their own
-- instruction stream; with a *unified* memory here instead, `phi0` could
-- never relate impl's frozen `imem` to a spec memory that stores keep
-- mutating, so the split is required for the correspondence to be
-- statable at all, not just for parity with the impl's own model.
structure State where
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  imem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  dmem : Array (BitVec 32) := .mk (List.replicate 65536 default)
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
  -- `imem`/`dmem` are WORD-addressed (matching `M_mktop_pipelined`'s
  -- `rule_RL_decode_core`/`rule_RL_execute_core`, which both index by
  -- `pc >> 2` / `addr >> 2`, not the raw byte address) -- see `instrAddr`
  -- below and `addrMem`'s definition further down.
  let instrAddr : BitVec 30 := truncate (shift_right_logical pc (2 : Nat)) 30
  let instr := s.imem.getD instrAddr.toNat default
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
  let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_)
                  byteEn (0 : BitVec 4)
  let isStore := if typeMem == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
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
  -- Illegal instruction: mirror rule_RL_decode_core/rule_RL_execute_core's
  -- `.legal` gating under the no-halt design -- the instruction still
  -- retires (it commits, with `data := none`, exactly like a legal
  -- instruction with no destination register), but never touches
  -- `rf`/`dmem`, and `pc` always takes the sequential fall-through (`pc +
  -- 4`) rather than `nextPC`, since decode's `redirected`/execute's
  -- `pcMismatch` are both gated on `.legal` and so never fire for it (see
  -- those rules' header comments in mktop_pipelined.lean).
  let legalCommitInfo : t_commit := { inst := instr, pc := pc, data := ite_bsv isValidRd (some finalData) none }
  let legalNewState : State :=
    { s with
        rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
        dmem := newDmem,
        pc := nextPC }
  let illegalCommitInfo : t_commit := { inst := instr, pc := pc, data := none }
  let illegalNewState : State := { s with pc := pc + (4 : BitVec 32) }
  match _ : dInst.legal with
  | BTrue _ => (legalNewState, legalCommitInfo)
  | BFalse _ => (illegalNewState, illegalCommitInfo)

def meth_getCommit (s : State) : t_actionvalue_ t_commit State :=
  let (s', c) := stepOne s
  { avValue_ := c, avAction_ := s' }
def meth_RDY_getCommit (_ : State) : t_bool := BTrue Unit_

def initS : State := default

#eval ((stepOne (stepOne { initS with pc := 0, rf := .mk (List.replicate 32 0), imem := .mk (List.replicate 10 0x00108093) }).1).1).rf

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

-- `BFalse`/`BTrue` are absorbing/identity elements on the right of
-- `bool_and`, needed once `.legal`-gated terms (`redirected`, `pcMismatch`)
-- appear with a symbolic `.legal` on the left: `bool_and legal (BFalse _)`
-- collapses regardless of `legal`'s value, and `bool_and legal (BTrue _)` is
-- just `legal` itself, in both cases without needing to case-split `legal`.
@[simp] theorem bool_and_false_right (p : t_bool) : bool_and p (BFalse Unit_) = BFalse Unit_ := by
  cases p <;> rfl

@[simp] theorem bool_and_true_right (p : t_bool) : bool_and p (BTrue Unit_) = p := by
  cases p <;> rfl

-- A `match` on an arbitrary t_bool that returns the same thing in both
-- branches is just that thing -- crucial for collapsing e.g. `bool_and`
-- chains once one component is known False (making everything downstream
-- of it BFalse Unit_ regardless of what the remaining, still-unknown
-- components are).
@[simp] theorem tbool_match_same {α : Type} (x : t_bool) (y : α) :
    (match x with | BTrue _ => y | BFalse _ => y) = y := by
  cases x <;> rfl

-- Dual of `bool_and_true_iff`/`bool_not`, needed to unpack decode's
-- `squashOrIllegal := bool_or epochMismatch illegal` guard down to its
-- underlying idEp/ieEp/legal comparisons (see `PipeInv` below).
theorem bool_or_eq_false_iff (a b : t_bool) :
    bool_or a b = BFalse Unit_ ↔ a = BFalse Unit_ ∧ b = BFalse Unit_ := by
  cases a <;> cases b <;> simp [bool_or]

theorem bool_not_eq_false_iff (x : t_bool) : bool_not x = BFalse Unit_ ↔ x = BTrue Unit_ := by
  cases x <;> simp [bool_not]

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

-- `n`-fold `Spec.stepOne`, keeping only the resulting state (dropping the
-- intermediate commit records) -- the spec-side lookahead anchor for
-- describing what a "settled" (dead-end) impl pipeline's in-flight content
-- corresponds to, `n` instructions past `s`.
def specStepN (s : SpecModule.State) : Nat → SpecModule.State
  | 0 => s
  | n + 1 => (M_mktop_pipelined.Spec.stepOne (specStepN s n)).1

-- The abstraction relation (the user's `phi0`). Earlier draft: pin every
-- impl field of a dead-end state exactly against a `decodeAt`/`executeAt`
-- (pipeline-formula) reconstruction of the in-flight instructions. PROBLEM
-- (found while attempting `reach_flush_again_meth_getCommit`): that
-- reconstruction was never actually tied back to `Spec.stepOne` anywhere --
-- `decodeAt`/`executeAt` are the PIPELINE's own core functions, so asserting
-- e.g. `i.e2w_element = executeAt d2e_I1 i.eEp sb2 s1.dmem` pins `i`'s shape
-- but says nothing about whether that shape is what a *correct* RISC-V
-- implementation would actually produce -- establishing that requires an
-- independent "decode+execute+writeback chain computes the same thing as
-- Spec.stepOne" equivalence lemma that (a) doesn't exist anywhere in this
-- codebase and (b) is a substantial standalone verification effort in its
-- own right (ALU/branch/immediate/memory semantics, redirect-vs-squash
-- ordering, illegal-instruction handling, ...).
--
-- FIX: define `phi0` as a genuine *coinductive* correspondence instead --
-- "the largest relation `R` between impl and spec states such that every
-- `R`-related pair (a) looks like a dead end with the right shape, and (b)
-- can advance -- by draining the pending commit and firing whatever pure
-- rules apply -- to another `R`-related pair one spec-step later." Standard
-- greatest-fixed-point-as-existential-over-post-fixed-points encoding: since
-- `phi0` no longer pins down *how* a dead end's in-flight content was
-- computed (only that SOME advance to a next dead end exists, matching the
-- next `Spec.stepOne` state), `reach_flush_again_meth_getCommit` below
-- becomes almost definitional -- it just re-packages the same witnessing
-- `R`. The real pipeline-correctness content (that `phi0` is ever actually
-- inhabited by a reachable state) is thus, as before, NOT established here
-- -- it was never in scope for this file either way (see the note this
-- comment replaces).
--
-- Shapes (unchanged from the earlier draft): under the no-halt design,
-- illegal instructions flow through the pipeline exactly like legal ones
-- (see mktop_pipelined.lean's header/rule comments), so fetch never blocks
-- on anything but f2d being full -- f2d is *always* occupied at a dead end.
-- That leaves exactly two shapes for how far behind decode can get stuck:
--   (A) "capacity jam": e2w, d2e both hold real, freshly-tagged in-flight
--       instructions and f2d holds a *fresh* entry, blocked from decoding
--       purely because d2e has no room (capacity, not a hazard).
--   (B) "RAW jam": only e2w holds a real instruction; d2e is empty, and
--       f2d holds a fresh entry that can't decode for some other reason
--       (an operand hazard, asserted directly via decode's own guard rather
--       than re-derived by hand).
def phi0_step (R : ImplModule.State → SpecModule.State → Prop)
    (i : ImplModule.State) (s : SpecModule.State) : Prop :=
  i.imem = s.imem ∧
  i.commitQ_hasElement = true ∧ i.commitQ_element = (M_mktop_pipelined.Spec.stepOne s).2 ∧
  i.rf = (specStepN s 1).rf ∧
  i.e2w_hasElement = true ∧
  i.f2d_hasElement = true ∧ i.f2d_element.idEp = i.dEp ∧ i.f2d_element.ieEp = i.eEp ∧
  ( (i.d2e_hasElement = true ∧ i.d2e_element.ieEp = i.eEp) ∨
    (i.d2e_hasElement = false ∧ (M_mktop_pipelined.rule_RL_decode i).1 ≠ BTrue Unit_) ) ∧
  ∃ i'', Relation.ReflTransGen ImplModule.getARule { i with commitQ_hasElement := false } i'' ∧
    R i'' (specStepN s 1)

def phi0 (i : ImplModule.State) (s : SpecModule.State) : Prop :=
  ∃ R : ImplModule.State → SpecModule.State → Prop, R i s ∧ ∀ a b, R a b → phi0_step R a b

-- `phi0` is itself a post-fixed point of `phi0_step` (it satisfies its own
-- unfolding), by reusing the same witnessing `R` one step later -- this is
-- what makes `phi0` genuinely self-sustaining rather than just "true once".
theorem phi0_unfold {i : ImplModule.State} {s : SpecModule.State} (h : phi0 i s) :
    phi0_step phi0 i s := by
  obtain ⟨R, hRi, hSS⟩ := h
  obtain ⟨himem, hcq, hcqe, hrf, he2w, hf2d, hidEp, hieEp, hshape, i'', hreach, hRi''⟩ := hSS i s hRi
  exact ⟨himem, hcq, hcqe, hrf, he2w, hf2d, hidEp, hieEp, hshape, i'', hreach, ⟨R, hRi'', hSS⟩⟩

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

-- ──────────────────────────────────────────────────────────────────────
-- Epoch-consistency invariant (`PipeInv`), inductively preserved by every
-- rule (`I i → R i i' → I i'`). This is FALSE for arbitrary values of
-- `ImplModule.State` -- nothing stops hand-picking a state where `f2d`/`d2e`
-- carry unrelated `ieEp` tags, since these are independent record fields --
-- but every state reachable via `ImplModule.getARule` (in particular, the
-- actual initial state, where `d2e_hasElement = false` makes it vacuous)
-- satisfies it. This is exactly the missing fact needed to rule out the
-- `commutes_rule_RL_decode_rule_RL_execute` counterexample (see that
-- theorem's comment): the counterexample needs `f2d_element.ieEp ≠ eEp`
-- while `d2e_element.ieEp = eEp`, which the second conjunct below makes
-- impossible whenever both FIFOs are simultaneously occupied.
--
-- Why each conjunct is preserved:
-- * J (`d2e_hasElement → d2e_element.ieEp = eEp`): `eEp` only changes in
--   `rule_RL_execute`, which *always* drains `d2e` (unconditionally sets
--   `d2e_hasElement := false`) when it fires, so J is vacuous immediately
--   after any `eEp` change. The only rule that can set `d2e_hasElement` from
--   false to true is `rule_RL_decode`'s normal (non-squash) branch, which
--   requires `epochMismatch = false`, i.e. `f2d_element.ieEp = eEp` at that
--   moment, and tags the new `d2e_element.ieEp` with exactly that value.
-- * K (`f2d_hasElement ∧ d2e_hasElement → f2d_element.ieEp = d2e_element.ieEp`):
--   `rule_RL_decode` always drains `f2d` (`f2d_hasElement := false`)
--   unconditionally, and `rule_RL_execute` always drains `d2e`
--   unconditionally, so K's antecedent is only possibly true right after
--   `rule_RL_fetch` refills `f2d` while `d2e` was already occupied -- in
--   which case J (applied to the pre-fetch state) pins `d2e_element.ieEp`
--   to the pre-fetch `eEp`, which is exactly the tag `rule_RL_fetch` gives
--   the new `f2d_element`.
def PipeInv (i : ImplModule.State) : Prop :=
  (i.d2e_hasElement → i.d2e_element.ieEp = i.eEp) ∧
  (i.f2d_hasElement ∧ i.d2e_hasElement → i.f2d_element.ieEp = i.d2e_element.ieEp)

theorem PipeInv_preserved_rule_RL_fetch {i i' : ImplModule.State} (hInv : PipeInv i)
    (hr : ImplModule.getRule .rule_RL_fetch i i') : PipeInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hJ, hK⟩ := hInv
  refine ⟨hJ, ?_⟩
  rintro ⟨_, hd2e⟩
  exact (hJ hd2e).symm

theorem PipeInv_preserved_rule_RL_decode {i i' : ImplModule.State} (hInv : PipeInv i)
    (hr : ImplModule.getRule .rule_RL_decode i i') : PipeInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
    M_mktop_pipelined.rule_RL_decode_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  clear hguard
  subst hi2
  obtain ⟨hJ, hK⟩ := hInv
  constructor
  · intro hd2e
    generalize hsq :
      bool_or (bool_not (if (i.f2d_element.idEp == i.dEp) = true then BTrue Unit_ else BFalse Unit_))
        (bool_not (if (i.f2d_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_)) = sq at *
    cases sq
    case BTrue a =>
      cases a
      dsimp only at hd2e ⊢
      exact hJ hd2e
    case BFalse a =>
      cases a
      dsimp only at hd2e ⊢
      simp only [bool_or_eq_false_iff] at hsq
      obtain ⟨_, hB⟩ := hsq
      rw [bool_not_eq_false_iff] at hB
      split_ifs at hB
      rename_i heq
      exact (beq_iff_eq ..).mp heq
  · intro h
    dsimp only at h
    exact absurd h.1 (by simp)

theorem PipeInv_preserved_rule_RL_execute {i i' : ImplModule.State} (hInv : PipeInv i)
    (hr : ImplModule.getRule .rule_RL_execute i i') : PipeInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute,
    M_mktop_pipelined.rule_RL_execute_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  refine ⟨?_, ?_⟩ <;> simp

theorem PipeInv_preserved_rule_RL_writeback {i i' : ImplModule.State} (hInv : PipeInv i)
    (hr : ImplModule.getRule .rule_RL_writeback i i') : PipeInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

theorem PipeInv_preserved {i i' : ImplModule.State} (hInv : PipeInv i)
    (hr : ImplModule.getARule i i') : PipeInv i' := by
  rcases ImplModule.get_rule_cases hr with h | h | h | h
  · exact PipeInv_preserved_rule_RL_fetch hInv h
  · exact PipeInv_preserved_rule_RL_decode hInv h
  · exact PipeInv_preserved_rule_RL_execute hInv h
  · exact PipeInv_preserved_rule_RL_writeback hInv h

-- ──────────────────────────────────────────────────────────────────────
-- Scoreboard consistency invariant (`SbInv`), same overall shape/purpose as
-- `PipeInv` above: `sb` is fully DERIVED information -- it exactly counts,
-- per register, how many of {d2e, e2w}'s current occupants (0, 1, or both)
-- validly write to it. This is exactly the missing fact needed to rule out
-- `commutes_rule_RL_decode_rule_RL_writeback`'s guard-level obstruction
-- (see that theorem's comment): without it, nothing stops `e2w`'s pending
-- write from aliasing a register decode's *readiness* check depends on
-- while `sb` at that register happens to be 0, letting writeback's release
-- flip decode's fire-guard between the two firing orders.
--
-- Why this is preserved by every rule -- and why no bound on `sb`'s
-- absolute value or reachability argument is needed, just clean +1/-1
-- cancellation: every rule that adds a register's contribution to `sb`
-- does so only when that register's *destination* slot was previously
-- empty, per that same rule's own fire-guard:
-- * decode's normal (real-issue) branch requires `d2e` EMPTY beforehand
--   (fire-guard's `fifo_RDY_enq d2eHasElement`), so the OLD d2e
--   contribution at every register is 0 -- decode's `sb` bump exactly
--   turns that 0 into the new d2e occupant's own contribution, leaving
--   `e2w`'s (untouched) contribution alone.
-- * execute's normal (non-squash) branch requires `e2w` EMPTY beforehand
--   (fire-guard's `fifo_RDY_enq e2wHasElement`), so moving the reservation
--   from d2e to e2w doesn't need to touch `sb` at all: the net
--   contribution at that register is unchanged, only which FIFO holds it.
-- * execute's squash branch releases exactly the old d2e occupant's own
--   contribution (0 or 1), which is precisely what `sb` needs to lose to
--   reflect d2e's new (empty) state.
-- * writeback releases exactly the old e2w occupant's own contribution,
--   symmetrically.
def dInstRd (dInst : RVUtil.DecodedInst) : BitVec 5 := (RVUtil.getInstFields dInst.inst).rd

def dInstWrites (dInst : RVUtil.DecodedInst) : t_bool :=
  bool_and dInst.legal
    (bool_and dInst.valid_rd (bool_not (if dInstRd dInst == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))

def sbContrib (hasElement : Bool) (dInst : RVUtil.DecodedInst) (r : BitVec 5) : BitVec 2 :=
  ite_bsv (bool_and (if hasElement then BTrue Unit_ else BFalse Unit_)
      (bool_and (dInstWrites dInst) (if dInstRd dInst == r then BTrue Unit_ else BFalse Unit_)))
    (1 : BitVec 2) (0 : BitVec 2)

def SbInv (i : ImplModule.State) : Prop :=
  i.sb.size = 32 ∧
  ∀ r : BitVec 5, arr_get i.sb r.toNat =
    sbContrib i.d2e_hasElement i.d2e_element.dInst r + sbContrib i.e2w_hasElement i.e2w_element.dInst r

theorem arr_set_size {α : Type} (arr : Array α) (i : Nat) (v : α) : (arr_set arr i v).size = arr.size := by
  unfold arr_set; simp

theorem SbInv_preserved_rule_RL_fetch {i i' : ImplModule.State} (hInv : SbInv i)
    (hr : ImplModule.getRule .rule_RL_fetch i i') : SbInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

theorem SbInv_preserved_rule_RL_decode {i i' : ImplModule.State} (hInv : SbInv i)
    (hr : ImplModule.getRule .rule_RL_decode i i') : SbInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
    M_mktop_pipelined.rule_RL_decode_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  obtain ⟨hsize, hpt⟩ := hInv
  subst hi2
  refine ⟨?_, fun r => ?_⟩ <;>
  · generalize hsq :
      bool_or (bool_not (if (i.f2d_element.idEp == i.dEp) = true then BTrue Unit_ else BFalse Unit_))
        (bool_not (if (i.f2d_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_)) = sq at *
    cases sq
    case BTrue a => cases a; dsimp only; first | exact hsize | exact hpt r
    case BFalse a =>
      cases a
      dsimp only
      have hd2e : i.d2e_hasElement = false := by
        dsimp only [fifo_RDY_enq] at hguard
        simp only [bool_and_true_iff] at hguard
        rcases h : i.d2e_hasElement with _ | _
        · rfl
        · exfalso; simp [h] at hguard
      first
      | (rw [arr_set_size]; exact hsize)
      | (set instr := M_mkSimpleMem.read i.imem (truncate (shift_right_logical i.f2d_element.pc 2) 30) with hinstr
         set decodedInst := RVUtil.decodeInst instr with hdecodedInst
         set rdIdx := (RVUtil.getInstFields instr).rd with hrdIdx
         have hIH := hpt r
         rw [hd2e] at hIH
         have hzero : sbContrib false i.d2e_element.dInst r = 0 := rfl
         rw [hzero, zero_add] at hIH
         have hbound : rdIdx.toNat < i.sb.size := by rw [hsize]; exact rdIdx.isLt.trans_le (by decide)
         have hdr0 : dInstRd decodedInst = rdIdx := by
           rw [dInstRd, hdecodedInst]; unfold RVUtil.decodeInst; exact hrdIdx.symm
         by_cases heq : rdIdx = r
         · subst heq
           rw [arr_get_arr_set_self _ _ _ hbound, hIH, add_comm]
           unfold sbContrib dInstWrites
           rw [hdr0]
           simp [bool_and_true_right]
           rfl
         · have hne : rdIdx.toNat ≠ r.toNat := by
             intro h; apply heq; exact BitVec.eq_of_toNat_eq h
           rw [arr_get_arr_set_ne _ _ _ _ hne, hIH]
           have hdrne : dInstRd decodedInst ≠ r := hdr0 ▸ heq
           unfold sbContrib
           simp [hdrne]
           rfl)

#print axioms SbInv_preserved_rule_RL_decode

theorem SbInv_preserved_rule_RL_execute {i i' : ImplModule.State} (hInv : SbInv i)
    (hr : ImplModule.getRule .rule_RL_execute i i') : SbInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute,
    M_mktop_pipelined.rule_RL_execute_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  obtain ⟨hsize, hpt⟩ := hInv
  subst hi2
  have hd2e : i.d2e_hasElement = true := by
    dsimp only [fifo_RDY_deq] at hguard
    simp only [bool_and_true_iff] at hguard
    rcases h : i.d2e_hasElement with _ | _
    · exfalso; simp [h] at hguard
    · rfl
  refine ⟨?_, fun r => ?_⟩ <;>
  · generalize hsq :
      bool_not (if (i.d2e_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_) = sq at *
    cases sq
    case BFalse a =>
      cases a
      dsimp only
      first
      | exact hsize
      | (have hIH := hpt r
         have he2w_old : i.e2w_hasElement = false := by
           dsimp only [fifo_RDY_enq] at hguard
           simp only [bool_and_true_iff] at hguard
           rcases h : i.e2w_hasElement with _ | _
           · rfl
           · exfalso; simp [h] at hguard
         rw [hd2e, he2w_old] at hIH
         have hzero1 : sbContrib false i.e2w_element.dInst r = 0 := rfl
         rw [hzero1, add_zero] at hIH
         have hzero2 : sbContrib false i.d2e_element.dInst r = 0 := rfl
         rw [hIH, hzero2, zero_add])
    case BTrue a =>
      cases a
      dsimp only
      first
      | (rw [arr_set_size]; exact hsize)
      | (have hIH := hpt r
         rw [hd2e] at hIH
         have hbound : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.toNat < i.sb.size := by
           rw [hsize]
           exact (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.isLt.trans_le (by decide)
         by_cases heq : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = r
         · subst heq
           rw [arr_get_arr_set_self _ _ _ hbound, hIH]
           have hD : sbContrib false i.d2e_element.dInst (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = 0 := rfl
           rw [hD, zero_add]
           generalize hB : sbContrib i.e2w_hasElement i.e2w_element.dInst
             (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = B
           unfold sbContrib dInstWrites dInstRd
           generalize hc : (if (RVUtil.getInstFields i.d2e_element.dInst.inst).rd == (0 : BitVec 5)
             then BTrue Unit_ else BFalse Unit_) = c at *
           generalize hleg : i.d2e_element.dInst.legal = leg at *
           generalize hvrd : i.d2e_element.dInst.valid_rd = vrd at *
           cases leg <;> cases vrd <;> cases c <;> simp [bool_and, bool_not, ite_bsv] <;> bv_decide
         · have hne : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.toNat ≠ r.toNat := by
             intro h; apply heq; exact BitVec.eq_of_toNat_eq h
           rw [arr_get_arr_set_ne _ _ _ _ hne, hIH]
           have hdrne : dInstRd i.d2e_element.dInst ≠ r := heq
           unfold sbContrib
           simp [hdrne])

theorem SbInv_preserved_rule_RL_writeback {i i' : ImplModule.State} (hInv : SbInv i)
    (hr : ImplModule.getRule .rule_RL_writeback i i') : SbInv i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  obtain ⟨hsize, hpt⟩ := hInv
  subst hi2
  have he2w : i.e2w_hasElement = true := by
    dsimp only [fifo_RDY_deq] at hguard
    simp only [bool_and_true_iff] at hguard
    rcases h : i.e2w_hasElement with _ | _
    · exfalso; simp [h] at hguard
    · rfl
  refine ⟨?_, fun r => ?_⟩
  · rw [arr_set_size]; exact hsize
  · have hIH := hpt r
    rw [he2w] at hIH
    have hbound : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.toNat < i.sb.size := by
      rw [hsize]
      exact (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.isLt.trans_le (by decide)
    by_cases heq : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = r
    · subst heq
      rw [arr_get_arr_set_self _ _ _ hbound, hIH]
      have hzero : sbContrib false i.e2w_element.dInst (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = 0 := rfl
      rw [hzero, add_zero]
      generalize hA : sbContrib i.d2e_hasElement i.d2e_element.dInst
        (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = A
      unfold sbContrib dInstWrites dInstRd
      generalize hc : (if (RVUtil.getInstFields i.e2w_element.dInst.inst).rd == (0 : BitVec 5)
        then BTrue Unit_ else BFalse Unit_) = c at *
      generalize hleg : i.e2w_element.dInst.legal = leg at *
      generalize hvrd : i.e2w_element.dInst.valid_rd = vrd at *
      cases leg <;> cases vrd <;> cases c <;> simp [bool_and, bool_not, ite_bsv] <;> bv_decide
    · have hne : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.toNat ≠ r.toNat := by
        intro h; apply heq; exact BitVec.eq_of_toNat_eq h
      rw [arr_get_arr_set_ne _ _ _ _ hne, hIH]
      have hdrne : dInstRd i.e2w_element.dInst ≠ r := heq
      unfold sbContrib
      simp [hdrne]

theorem SbInv_preserved {i i' : ImplModule.State} (hInv : SbInv i)
    (hr : ImplModule.getARule i i') : SbInv i' := by
  rcases ImplModule.get_rule_cases hr with h | h | h | h
  · exact SbInv_preserved_rule_RL_fetch hInv h
  · exact SbInv_preserved_rule_RL_decode hInv h
  · exact SbInv_preserved_rule_RL_execute hInv h
  · exact SbInv_preserved_rule_RL_writeback hInv h

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
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core] at hc
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at hb
  obtain ⟨hc_g, hc_e⟩ := Prod.mk.injEq .. |>.mp hc
  by_cases hieEp : a.d2e_element.ieEp = a.eEp
  · -- not squash: split on whether execute's `pcMismatch` actually fires --
    -- bundling "correctly predicted" and "instruction is illegal (so any
    -- apparent misprediction is suppressed by execute's `.legal` gate,
    -- regardless of what the raw ALU/branch computation says)" into the
    -- single non-firing case.
    generalize hpm : bool_and a.d2e_element.dInst.legal
        (bool_not (if (RVUtil.execControl32 a.d2e_element.dInst.inst a.d2e_element.rv1 a.d2e_element.rv2
          (RVUtil.getImmediate a.d2e_element.dInst) a.d2e_element.pc).nextPC == a.d2e_element.ppc
          then BTrue Unit_ else BFalse Unit_)) = pm
    cases pm
    · ---------------------------------------------------------------
      -- HARD (pm = BTrue): taken/mispredicted redirect (necessarily
      -- legal -- a redirect on an illegal instruction is exactly the case
      -- the BFalse branch below absorbed). 3-step witness on the c-path
      -- (execute, decode(squash), fetch) vs 1 step on the b-path (fetch).
      ---------------------------------------------------------------
      rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
          a.d2e_hasElement a.e2w_hasElement hieEp] at hb
      rw [hpm] at hb
      simp only [ite_bsv] at hb
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
        rw [hpm]
        simp only [ite_bsv]
      set c2 := (M_mktop_pipelined.rule_RL_decode c1).2 with hc2_def
      have hc2_eq : c2 = { c1 with f2d_hasElement := false } := by
        rw [hc2_def]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [rule_RL_decode_core_squash_branch c1.imem c1.f2d_element c1.dEp c1.eEp c1.sb c1.rf
            c1.pc c1.d2e_element c1.f2d_hasElement c1.d2e_hasElement
            (by simp only [hc1_eq, ← hc_e]) (by
              simp only [hc1_eq, ← hc_e]
              exact Ne.symm heEpNe)]
      have hc2_f2d : c2.f2d_hasElement = false := by rw [hc2_eq]
      set c3 := (M_mktop_pipelined.rule_RL_fetch c2).2 with hc3_def
      have hc3_eq : c3 = { c2 with
          f2d_hasElement := true,
          f2d_element := { pc := c2.pc, ppc := c2.pc + 4, idEp := c2.dEp, ieEp := c2.eEp },
          pc := c2.pc + 4 } := by
        rw [hc3_def]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
      set b1 := (M_mktop_pipelined.rule_RL_fetch b).2 with hb1_def
      have hb_f2d : b.f2d_hasElement = false := by simp only [← hb_e]; exact ha_f2d
      have hb1_eq : b1 = { b with
          f2d_hasElement := true,
          f2d_element := { pc := b.pc, ppc := b.pc + 4, idEp := b.dEp, ieEp := b.eEp },
          pc := b.pc + 4 } := by
        rw [hb1_def]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
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
        rw [hpm]
        simp only [ite_bsv]
        simp only [bool_and_true_iff] at hb_g
        simp [hb_g]⟩
      have step2 : ImplModule.getARule c1 c2 := ⟨.rule_RL_decode, by
        show M_mktop_pipelined.rule_RL_decode c1 = (BTrue Unit_, c2)
        rw [hc2_eq]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [rule_RL_decode_core_squash_branch c1.imem c1.f2d_element c1.dEp c1.eEp c1.sb c1.rf
            c1.pc c1.d2e_element c1.f2d_hasElement c1.d2e_hasElement
            (by simp only [hc1_eq, ← hc_e]) (by
              simp only [hc1_eq, ← hc_e]
              exact Ne.symm heEpNe)]
        simp [fifo_RDY_deq, hc1_eq, ← hc_e]⟩
      have step3 : ImplModule.getARule c2 c3 := ⟨.rule_RL_fetch, by
        show M_mktop_pipelined.rule_RL_fetch c2 = (BTrue Unit_, c3)
        rw [hc3_eq]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
        simp [fifo_RDY_enq, hc2_f2d]⟩
      have stepb1 : ImplModule.getARule b b1 := ⟨.rule_RL_fetch, by
        show M_mktop_pipelined.rule_RL_fetch b = (BTrue Unit_, b1)
        rw [hb1_eq]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
        simp [fifo_RDY_enq, hb_f2d]⟩
      refine ⟨c3, ?_, hfinal ▸ ?_⟩
      · exact .tail (.tail (.single step1) step2) step3
      · exact .single stepb1
    · ---------------------------------------------------------------
      -- EASY (pm = BFalse): no redirect (correctly predicted, or
      -- illegal) -- one-step diamond.
      ---------------------------------------------------------------
      rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
          a.d2e_hasElement a.e2w_hasElement hieEp] at hb
      simp only [hpm] at hb
      obtain ⟨hb_g, hb_e⟩ := Prod.mk.injEq .. |>.mp hb
      refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩
      · show M_mktop_pipelined.rule_RL_execute c = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        simp only [hpm]
        simp only [bool_and_true_iff] at hc_g hb_g
        simp [hc_g, hb_g, ite_bsv, bool_not]
      · show M_mktop_pipelined.rule_RL_fetch b = (BTrue Unit_, (M_mktop_pipelined.rule_RL_execute c).2)
        rw [← hb_e]
        dsimp only [M_mktop_pipelined.rule_RL_execute]
        rw [← hc_e]
        dsimp only
        rw [rule_RL_execute_core_normal_branch a.d2e_element a.eEp a.sb (a.pc + 4#32) a.dmem
            a.e2w_element a.d2e_hasElement a.e2w_hasElement hieEp]
        simp only [hpm]
        dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
        simp only [bool_and_true_iff] at hb_g
        simp [hc_g, hb_g, ite_bsv, bool_not]
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
      dsimp only [M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core]
      simp only [bool_and_true_iff] at hb_g
      simp [hc_g, hb_g]

theorem commutes_rule_RL_fetch_rule_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_fetch a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.rule_RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core,
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
    M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core, M_mktop_pipelined.fifo_RDY_enq, M_mktop_pipelined.fifo_RDY_deq] at hc hb
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

-- TRUE given `PipeInv a` (see that def's comment for why the invariant is
-- exactly what's needed): without it, this is FALSE as a statement over the
-- bare `State` type, since nothing stops hand-picking `a` with
-- `a.f2d_element.ieEp ≠ a.eEp` (forcing decode-on-`a` to squash) while
-- `a.d2e_element.ieEp = a.eEp` and that d2e entry mispredicts -- execute
-- would set `b.eEp := a.eEp + 1`, which happens to equal
-- `a.f2d_element.ieEp`, making decode-on-`b` see the SAME f2d entry as
-- epoch-matching and take the *normal* branch instead of squashing it
-- (a discontinuity `PipeInv`'s second conjunct rules out, since it pins
-- `a.f2d_element.ieEp = a.d2e_element.ieEp` whenever both FIFOs are
-- occupied -- exactly the case here).
theorem commutes_rule_RL_decode_rule_RL_execute {a b c : ImplModule.State} (hInv : PipeInv a) :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbg : (M_mktop_pipelined.rule_RL_execute a).1 = BTrue Unit_ := by rw [hb]
  have hd2e : a.d2e_hasElement = true := by
    dsimp [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core, fifo_RDY_deq] at hbg
    rcases h : a.d2e_hasElement with _|_
    · exfalso; rw [h] at hbg; simp at hbg
    · rfl
  have hcg : (M_mktop_pipelined.rule_RL_decode a).1 = BTrue Unit_ := by rw [hc]
  have hf2d : a.f2d_hasElement = true := by
    dsimp [M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, fifo_RDY_deq] at hcg
    rcases h : a.f2d_hasElement with _|_
    · exfalso; rw [h] at hcg; simp at hcg
    · rfl
  obtain ⟨hJ, hK⟩ := hInv
  have hK' : a.f2d_element.ieEp = a.d2e_element.ieEp := hK ⟨hf2d, hd2e⟩
  by_cases hidEpEq : a.f2d_element.idEp = a.dEp
  · -- idEp matches: decode must be squashing via ieEp (else it would need d2e
    -- empty to issue, contradicting hd2e), so by hK' execute must ALSO be
    -- squashing (same ieEp, stale relative to the same eEp).
    have hieEpNe : a.f2d_element.ieEp ≠ a.eEp := by
      intro hieEpEq
      have hcg' := hcg
      dsimp [M_mktop_pipelined.rule_RL_decode] at hcg'
      rw [rule_RL_decode_core_normal_branch a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
        a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpEq] at hcg'
      dsimp only at hcg'
      simp only [fifo_RDY_enq, hd2e] at hcg'
      simp at hcg'
    have hd2eIeEpNe : a.d2e_element.ieEp ≠ a.eEp := hK' ▸ hieEpNe
    dsimp only [M_mktop_pipelined.rule_RL_decode] at hc
    rw [rule_RL_decode_core_squash_branch a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
      a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpNe] at hc
    dsimp only [M_mktop_pipelined.rule_RL_execute] at hb
    rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
      a.d2e_hasElement a.e2w_hasElement hd2eIeEpNe] at hb
    obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
    obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
    refine ⟨M_mktop_pipelined.rule_RL_execute c |>.2,
      Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩,
      Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at ⊢
      rw [← hc2]
      dsimp only
      rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
        a.d2e_hasElement a.e2w_hasElement hd2eIeEpNe]
      simp [hd2e, fifo_RDY_deq, bool_and]
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
        M_mktop_pipelined.rule_RL_execute] at ⊢
      rw [← hb2]
      dsimp only
      rw [rule_RL_decode_core_squash_branch a.imem a.f2d_element a.dEp a.eEp _ a.rf a.pc a.d2e_element
        a.f2d_hasElement false hidEpEq hieEpNe]
      rw [← hc2]
      dsimp only
      rw [rule_RL_execute_core_squash_branch a.d2e_element a.eEp a.sb a.pc a.dmem a.e2w_element
        a.d2e_hasElement a.e2w_hasElement hd2eIeEpNe]
      simp [hf2d, fifo_RDY_deq, bool_and]
  · -- idEp mismatches: decode squashes on that alone, regardless of ieEp; the
    -- idEp check is unaffected by anything execute does (execute never
    -- touches dEp or f2d), so decode-on-b squashes for the same reason.
    dsimp only [M_mktop_pipelined.rule_RL_decode] at hc
    rw [rule_RL_decode_core_squash_branch_idEp a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
      a.f2d_hasElement a.d2e_hasElement hidEpEq] at hc
    dsimp only at hc
    obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
    obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
    refine ⟨M_mktop_pipelined.rule_RL_execute c |>.2,
      Relation.ReflTransGen.single ⟨.rule_RL_execute, ?_⟩,
      Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at ⊢
      rw [← hc2]
      dsimp only
      have hbg' := hbg
      dsimp [M_mktop_pipelined.rule_RL_execute] at hbg'
      simp only [hbg']
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
        M_mktop_pipelined.rule_RL_execute] at ⊢
      rw [← hb2]
      dsimp only
      rw [rule_RL_decode_core_squash_branch_idEp a.imem a.f2d_element a.dEp _ _ a.rf _ a.d2e_element
        a.f2d_hasElement false hidEpEq]
      rw [← hc2]
      unfold M_mktop_pipelined.rule_RL_execute_core
      dsimp only
      simp [hf2d, fifo_RDY_deq, bool_and]

-- Two stacked obstructions to a clean one-step diamond here; `SbInv` fully
-- resolves both, and both sub-cases now close without needing an extra
-- execute step:
--
-- (a) GUARD-LEVEL, FULLY RESOLVED by `SbInv a`: without it, nothing stops a
-- state `a` with `a.sb[R] = 0` while `a.e2w_element.dInst` simultaneously
-- targets `rd = R` validly -- firing writeback would then wrap `sb[R]` from
-- 0 to 3#2, flipping decode's rs1Ready/rs2Ready check between the two
-- firing orders (if decode's instruction reads `R` as rs1/rs2). `SbInv a`
-- rules this out directly: writeback's release always lands `sb[R]` on 0
-- (regardless of its prior value, since that prior value is itself pinned
-- by `SbInv`), and if decode's instruction validly reads `R` as rs1/rs2,
-- `a.sb[R]` must *already* have been 0 for decode to have fired on `a` at
-- all -- so both orders agree the register is ready. See
-- `decodeOperandsReady_agree`.
--
-- (b) VALUE-LEVEL, RESOLVED at the source: decode's `rv1`/`rv2` fields
-- (`rule_RL_decode_core`) are zeroed whenever the operand is architecturally
-- unused (`valid_rs1`/`valid_rs2 = false`), not just when the register index
-- is `x0` -- a deliberate simplification of the original `pipelined.bsv`
-- (which stores the raw `rf` read unconditionally, discarding it later
-- exactly the same way; the two are externally indistinguishable, since
-- nothing ever reads an unused operand's value downstream -- `execALU32`/
-- `execControl32` special-case every instruction class that doesn't use
-- rs1/rs2, and `isValidRd`/`dInstWrites` gate the *result* away from `rf`
-- and `commitQ` for any instruction that doesn't validly write a
-- destination anyway). This closes the residual case that used to be
-- `sorry` here (decode's rs1/rs2 aliasing writeback's released register
-- while being architecturally unused by decode's instruction, e.g. EBREAK's
-- fixed-but-nonzero rs2 bit pattern): a per-step "clean up the stale value
-- afterward" fix doesn't work (writeback's single-slot `commitQ` blocks a
-- second writeback until the external `getCommit` method drains it, which
-- `ImplModule.getARule`'s rule-only reachability can never invoke -- see
-- git history for the dead-end analysis), so the fix has to prevent the
-- divergence from being created at all. `decodeD2eNormal_rf_agree'`/
-- `decodePcDEpNormal_rf_agree'` below generalize the straightforward
-- rf-agreement lemmas to also accept "architecturally unused" as an
-- alternative to "the two rf reads agree", and the `hwrite`-true branch
-- derives that fact directly from `SbInv`/`hopReady` (if the aliased slot
-- were validly used, decode couldn't have fired on `a` at all, by the same
-- contradiction as (a)) -- so no case split on aliasing is needed anymore.
theorem bool_or_false_right (p : t_bool) : bool_or p (BFalse Unit_) = p := by cases p <;> rfl

theorem arr_set_self_get {α : Type} [Inhabited α] (arr : Array α) (i : Nat) :
    arr_set arr i (arr_get arr i) = arr := by
  unfold arr_set arr_get
  apply Array.ext_getElem?
  intro k
  by_cases hk : k = i
  · subst hk
    by_cases hbound : k < arr.size
    · simp [Array.getElem?_setIfInBounds_self, hbound, Array.getElem!_eq_getD]
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hbound]
  · simp [Array.getElem?_setIfInBounds_ne, hk, Ne.symm hk]

theorem decodeSbNormal_writeback_comm (imem : Array (BitVec 32)) (f2dElement : t_f2d)
    (sb : Array (BitVec 2)) (e2wDInst : RVUtil.DecodedInst) :
    arr_set (decodeSbNormal imem f2dElement sb) (dInstRd e2wDInst).toNat
        (arr_get (decodeSbNormal imem f2dElement sb) (dInstRd e2wDInst).toNat +
          ite_bsv (dInstWrites e2wDInst) (-1 : BitVec 2) (0 : BitVec 2)) =
      decodeSbNormal imem f2dElement
        (arr_set sb (dInstRd e2wDInst).toNat
          (arr_get sb (dInstRd e2wDInst).toNat + ite_bsv (dInstWrites e2wDInst) (-1 : BitVec 2) (0 : BitVec 2))) := by
  unfold decodeSbNormal
  dsimp only
  exact arr_get_set_delta_comm sb _ _ _ _

-- Generalized versions of the "rf agrees at rs1/rs2" facts decode's own
-- outputs need: agreement at a register index isn't required if that
-- operand is architecturally unused (`valid_rs1`/`valid_rs2 = false`)
-- anyway, since decode now zeros it in that case regardless of `rf`'s
-- content there (see `rule_RL_decode_core`'s header comment).
theorem decodeD2eNormal_rf_agree' (imem : Array (BitVec 32)) (f2dElement : t_f2d)
    (rf rf' : Array (BitVec 32))
    (h1 : arr_get rf (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs1.toNat =
      arr_get rf' (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs1.toNat ∨
      (RVUtil.decodeInst (M_mkSimpleMem.read imem
        (truncate (shift_right_logical f2dElement.pc 2) 30))).valid_rs1 = BFalse Unit_)
    (h2 : arr_get rf (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs2.toNat =
      arr_get rf' (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs2.toNat ∨
      (RVUtil.decodeInst (M_mkSimpleMem.read imem
        (truncate (shift_right_logical f2dElement.pc 2) 30))).valid_rs2 = BFalse Unit_) :
    decodeD2eNormal imem f2dElement rf = decodeD2eNormal imem f2dElement rf' := by
  unfold decodeD2eNormal
  dsimp only
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp_all [bool_and, ite_bsv]

theorem decodePcDEpNormal_rf_agree' (imem : Array (BitVec 32)) (f2dElement : t_f2d)
    (rf rf' : Array (BitVec 32)) (pc : BitVec 32) (dEp : BitVec 1)
    (h1 : arr_get rf (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs1.toNat =
      arr_get rf' (RVUtil.getInstFields
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs1.toNat ∨
      (RVUtil.decodeInst (M_mkSimpleMem.read imem
        (truncate (shift_right_logical f2dElement.pc 2) 30))).valid_rs1 = BFalse Unit_) :
    decodePcDEpNormal imem f2dElement rf pc dEp = decodePcDEpNormal imem f2dElement rf' pc dEp := by
  unfold decodePcDEpNormal
  dsimp only
  rcases h1 with h1 | h1
  · rw [h1]
  · rw [h1]; simp only [bool_and, ite_bsv]; rfl

theorem decodeOperandsReady_agree (imem : Array (BitVec 32)) (f2dElement : t_f2d)
    (sb sb' : Array (BitVec 2))
    (hagree : ∀ idx : BitVec 5, arr_get sb idx.toNat = 0 → arr_get sb' idx.toNat = 0)
    (h : decodeOperandsReady imem f2dElement sb = BTrue Unit_) :
    decodeOperandsReady imem f2dElement sb' = BTrue Unit_ := by
  unfold decodeOperandsReady at h ⊢
  simp only [bool_and_true_iff] at h
  obtain ⟨hr1, hr2⟩ := h
  refine bool_and_true_iff .. |>.mpr ⟨?_, ?_⟩
  · rcases hv1 : (RVUtil.decodeInst
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).valid_rs1 with _ | _
    · simp only [hv1, bool_and, bool_not, bool_or_false_right] at hr1
      have h0 : arr_get sb (RVUtil.getInstFields
          (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs1.toNat = 0 := by
        simpa using hr1
      rw [hagree _ h0]
      simp [hv1, bool_or, bool_and]
    · simp [hv1, bool_not, bool_or, bool_and]
  · rcases hv2 : (RVUtil.decodeInst
        (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).valid_rs2 with _ | _
    · simp only [hv2, bool_and, bool_not, bool_or_false_right] at hr2
      have h0 : arr_get sb (RVUtil.getInstFields
          (M_mkSimpleMem.read imem (truncate (shift_right_logical f2dElement.pc 2) 30))).rs2.toNat = 0 := by
        simpa using hr2
      rw [hagree _ h0]
      simp [hv2, bool_or, bool_and]
    · simp [hv2, bool_not, bool_or, bool_and]

theorem commutes_rule_RL_decode_rule_RL_writeback {a b c : ImplModule.State} (hInv : SbInv a) :
  ImplModule.getRule .rule_RL_decode a c →
  ImplModule.getRule .rule_RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbg : (M_mktop_pipelined.rule_RL_writeback a).1 = BTrue Unit_ := by rw [hb]
  have he2w : a.e2w_hasElement = true := by
    dsimp [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, fifo_RDY_deq] at hbg
    rcases h : a.e2w_hasElement with _|_
    · exfalso; rw [h] at hbg; simp at hbg
    · rfl
  have hcq : a.commitQ_hasElement = false := by
    dsimp [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core, fifo_RDY_enq] at hbg
    simp only [he2w, bool_and_true_iff] at hbg
    rcases h : a.commitQ_hasElement with _|_
    · rfl
    · exfalso; simp [h] at hbg
  have hcg : (M_mktop_pipelined.rule_RL_decode a).1 = BTrue Unit_ := by rw [hc]
  have hf2d : a.f2d_hasElement = true := by
    dsimp [M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_decode_core, fifo_RDY_deq] at hcg
    rcases h : a.f2d_hasElement with _|_
    · exfalso; rw [h] at hcg; simp at hcg
    · rfl
  by_cases hidEpEq : a.f2d_element.idEp = a.dEp
  · by_cases hieEpEq : a.f2d_element.ieEp = a.eEp
    · -- Case 2: normal issue (the hard case).
      dsimp only [M_mktop_pipelined.rule_RL_decode] at hc
      rw [rule_RL_decode_core_normal_branch a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
        a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpEq] at hc
      dsimp only at hc
      obtain ⟨hcg', hc2⟩ := Prod.mk.injEq .. |>.mp hc
      simp only [bool_and_true_iff] at hcg'
      obtain ⟨_, hopReady, _, hd2eEnq⟩ := hcg'
      have hd2e : a.d2e_hasElement = false := by
        simp only [fifo_RDY_enq] at hd2eEnq
        rcases h : a.d2e_hasElement with _ | _
        · rfl
        · exfalso; simp [h] at hd2eEnq
      -- The scoreboard fact writeback firing on `a` gives us, via `SbInv a`.
      obtain ⟨hsize, hpt⟩ := hInv
      have hsb_a : ∀ r : BitVec 5, arr_get a.sb r.toNat = sbContrib true a.e2w_element.dInst r := by
        intro r
        have h := hpt r
        rw [hd2e, he2w] at h
        have hzero : sbContrib false a.d2e_element.dInst r = 0 := rfl
        rwa [hzero, zero_add] at h
      have hsb_a_Rw : arr_get a.sb (dInstRd a.e2w_element.dInst).toNat =
          ite_bsv (dInstWrites a.e2w_element.dInst) 1 0 := by
        have h := hsb_a (dInstRd a.e2w_element.dInst)
        unfold sbContrib at h
        simpa using h
      dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at hb
      obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
      have hb_sb : b.sb = arr_set a.sb (dInstRd a.e2w_element.dInst).toNat
          (arr_get a.sb (dInstRd a.e2w_element.dInst).toNat +
            ite_bsv (dInstWrites a.e2w_element.dInst) (-1) 0) := by
        rw [← hb2]; rfl
      have hb_rf : b.rf = arr_set a.rf (dInstRd a.e2w_element.dInst).toNat
          (ite_bsv (dInstWrites a.e2w_element.dInst) a.e2w_element.data
            (arr_get a.rf (dInstRd a.e2w_element.dInst).toNat)) := by
        rw [← hb2]; rfl
      have hb_sb_Rw : arr_get b.sb (dInstRd a.e2w_element.dInst).toNat = 0 := by
        rw [hb_sb, arr_get_arr_set_self]
        · rw [hsb_a_Rw]; cases dInstWrites a.e2w_element.dInst <;> simp [ite_bsv]
        · rw [hsize]; exact (dInstRd a.e2w_element.dInst).isLt.trans_le (by decide)
      -- Writeback's release never turns a *ready* (sb = 0) register unready:
      -- if `a.sb[idx] = 0`, so is `b.sb[idx]`, whether or not `idx` aliases
      -- writeback's own register (which lands on 0 either way, per
      -- `hb_sb_Rw`, regardless of `a.sb`'s prior value there).
      have hsb_agree0 : ∀ idx : BitVec 5, arr_get a.sb idx.toNat = 0 → arr_get b.sb idx.toNat = 0 := by
        intro idx h0
        by_cases heq : idx = dInstRd a.e2w_element.dInst
        · rw [heq]; exact hb_sb_Rw
        · rw [hb_sb, arr_get_arr_set_ne]
          · exact h0
          · intro hcon; exact heq (BitVec.eq_of_toNat_eq hcon.symm)
      have hopReady_b : decodeOperandsReady a.imem a.f2d_element b.sb = BTrue Unit_ :=
        decodeOperandsReady_agree a.imem a.f2d_element a.sb b.sb hsb_agree0 hopReady
      -- Given decode's own d2e-entry/pc/dEp outputs agree regardless of
      -- which order fired (`hD2eEq`/`hPcDEpEq`), the two orders reconverge
      -- in one step each: writeback-on-c and decode-on-b land on the exact
      -- same state (sb via `arr_get_set_delta_comm`-style commuting,
      -- pc/dEp/d2e/rf by direct substitution).
      have closeGood :
          decodeD2eNormal a.imem a.f2d_element a.rf = decodeD2eNormal a.imem a.f2d_element b.rf →
          decodePcDEpNormal a.imem a.f2d_element a.rf a.pc a.dEp =
            decodePcDEpNormal a.imem a.f2d_element b.rf a.pc a.dEp →
          ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
        intro hD2eEq hPcDEpEq
        refine ⟨M_mktop_pipelined.rule_RL_writeback c |>.2,
          Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩,
          Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩
        · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
            M_mktop_pipelined.rule_RL_writeback_core] at ⊢
          rw [← hc2]
          dsimp only
          simp [he2w, hcq, fifo_RDY_deq, fifo_RDY_enq, bool_and]
        · rw [hb_sb] at hopReady_b
          rw [hb_rf] at hD2eEq hPcDEpEq
          dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
            M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at ⊢
          rw [← hb2]
          dsimp only
          rw [rule_RL_decode_core_normal_branch a.imem a.f2d_element a.dEp a.eEp _ _ a.pc a.d2e_element
            a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpEq]
          rw [← hc2]
          dsimp only
          have hSbEq := decodeSbNormal_writeback_comm a.imem a.f2d_element a.sb a.e2w_element.dInst
          simp only [dInstRd, dInstWrites, bool_and, beq_iff_eq] at hopReady_b hD2eEq hPcDEpEq hSbEq ⊢
          simp only [hopReady_b, hD2eEq, hPcDEpEq, hf2d, fifo_RDY_deq, fifo_RDY_enq, hd2e]
          rw [hSbEq.symm]
          simp
      -- rf-agreement facts: writeback's rf write never touches an index
      -- other than its own `rd`, and if it doesn't actually write at all,
      -- `b.rf = a.rf` everywhere (setting a register to its own value is a
      -- no-op read-wise, regardless of bounds).
      have hb_rf_not_write : dInstWrites a.e2w_element.dInst = BFalse Unit_ → b.rf = a.rf := by
        intro hnw
        rw [hb_rf, hnw]
        simp only [ite_bsv]
        exact arr_set_self_get a.rf _
      have hrf_ne : ∀ idx : BitVec 5, idx ≠ dInstRd a.e2w_element.dInst →
          arr_get a.rf idx.toNat = arr_get b.rf idx.toNat := by
        intro idx hidx
        rw [hb_rf, arr_get_arr_set_ne]
        intro hcon; exact hidx (BitVec.eq_of_toNat_eq hcon.symm)
      by_cases hwrite : dInstWrites a.e2w_element.dInst = BTrue Unit_
      · -- writeback really does write `Rw`. Even when decode's rs1/rs2
        -- alias `Rw`, either they don't (rf agrees via `hrf_ne`) or -- since
        -- `hwrite` pins `a.sb[Rw] ≠ 0` via `hsb_a_Rw` -- decode's readiness
        -- check on `a` forces that slot to be architecturally unused
        -- (else decode couldn't have fired on `a` in the first place, same
        -- contradiction as `decodeOperandsReady_agree`'s guard-level
        -- argument); either way `decodeD2eNormal_rf_agree'`/
        -- `decodePcDEpNormal_rf_agree'` apply directly, no case split on
        -- aliasing needed.
        have hopReady' := hopReady
        unfold decodeOperandsReady at hopReady'
        simp only [bool_and_true_iff] at hopReady'
        obtain ⟨hr1, hr2⟩ := hopReady'
        have h1 : arr_get a.rf (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs1.toNat =
            arr_get b.rf (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs1.toNat ∨
          (RVUtil.decodeInst (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).valid_rs1 = BFalse Unit_ := by
          by_cases hidx : (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs1 = dInstRd a.e2w_element.dInst
          · right
            rcases hv : (RVUtil.decodeInst (M_mkSimpleMem.read a.imem
                (truncate (shift_right_logical a.f2d_element.pc 2) 30))).valid_rs1 with u | u <;> cases u
            · exfalso
              rw [hv] at hr1
              simp only [bool_and, bool_not, bool_or_false_right] at hr1
              rw [hidx, hsb_a_Rw, hwrite] at hr1
              simp [ite_bsv] at hr1
            · rfl
          · left; exact hrf_ne _ hidx
        have h2 : arr_get a.rf (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs2.toNat =
            arr_get b.rf (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs2.toNat ∨
          (RVUtil.decodeInst (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).valid_rs2 = BFalse Unit_ := by
          by_cases hidx : (RVUtil.getInstFields (M_mkSimpleMem.read a.imem
              (truncate (shift_right_logical a.f2d_element.pc 2) 30))).rs2 = dInstRd a.e2w_element.dInst
          · right
            rcases hv : (RVUtil.decodeInst (M_mkSimpleMem.read a.imem
                (truncate (shift_right_logical a.f2d_element.pc 2) 30))).valid_rs2 with u | u <;> cases u
            · exfalso
              rw [hv] at hr2
              simp only [bool_and, bool_not, bool_or_false_right] at hr2
              rw [hidx, hsb_a_Rw, hwrite] at hr2
              simp [ite_bsv] at hr2
            · rfl
          · left; exact hrf_ne _ hidx
        have hD2eEq := decodeD2eNormal_rf_agree' a.imem a.f2d_element a.rf b.rf h1 h2
        have hPcDEpEq := decodePcDEpNormal_rf_agree' a.imem a.f2d_element a.rf b.rf a.pc a.dEp h1
        exact closeGood hD2eEq hPcDEpEq
      · have hnw : dInstWrites a.e2w_element.dInst = BFalse Unit_ := by
          rcases h : dInstWrites a.e2w_element.dInst with _ | _
          · exact absurd h hwrite
          · rfl
        have hrfEq : b.rf = a.rf := hb_rf_not_write hnw
        exact closeGood (by rw [hrfEq]) (by rw [hrfEq])
    · -- Case 1b: squash via ieEp mismatch.
      have hieEpNe : a.f2d_element.ieEp ≠ a.eEp := hieEpEq
      dsimp only [M_mktop_pipelined.rule_RL_decode] at hc
      rw [rule_RL_decode_core_squash_branch a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
        a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpNe] at hc
      dsimp only at hc
      obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
      obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
      refine ⟨M_mktop_pipelined.rule_RL_writeback c |>.2,
        Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩,
        Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩
      · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
          M_mktop_pipelined.rule_RL_writeback_core] at ⊢
        rw [← hc2]
        dsimp only
        simp_all [fifo_RDY_deq, fifo_RDY_enq, bool_and]
      · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
          M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at ⊢
        rw [← hb2]
        dsimp only
        rw [rule_RL_decode_core_squash_branch a.imem a.f2d_element a.dEp _ _ _ _ a.d2e_element
          a.f2d_hasElement a.d2e_hasElement hidEpEq hieEpNe]
        rw [← hc2]
        dsimp only
        simp_all [fifo_RDY_deq, fifo_RDY_enq, bool_and]
  · -- Case 1a: squash via idEp mismatch (regardless of ieEp).
    dsimp only [M_mktop_pipelined.rule_RL_decode] at hc
    rw [rule_RL_decode_core_squash_branch_idEp a.imem a.f2d_element a.dEp a.eEp a.sb a.rf a.pc a.d2e_element
      a.f2d_hasElement a.d2e_hasElement hidEpEq] at hc
    dsimp only at hc
    obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
    obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
    refine ⟨M_mktop_pipelined.rule_RL_writeback c |>.2,
      Relation.ReflTransGen.single ⟨.rule_RL_writeback, ?_⟩,
      Relation.ReflTransGen.single ⟨.rule_RL_decode, ?_⟩⟩
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
        M_mktop_pipelined.rule_RL_writeback_core] at ⊢
      rw [← hc2]
      dsimp only
      simp_all [fifo_RDY_deq, fifo_RDY_enq, bool_and]
    · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
        M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core] at ⊢
      rw [← hb2]
      dsimp only
      rw [rule_RL_decode_core_squash_branch_idEp a.imem a.f2d_element a.dEp _ _ _ _ a.d2e_element
        a.f2d_hasElement a.d2e_hasElement hidEpEq]
      rw [← hc2]
      dsimp only
      simp_all [fifo_RDY_deq, fifo_RDY_enq, bool_and]

theorem commutes_rule_RL_execute_rule_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_rule_RL_fetch_rule_RL_execute hb hc
  exact ⟨d, hd2, hd1⟩

theorem commutes_rule_RL_execute_rule_RL_decode {a b c : ImplModule.State} (hInv : PipeInv a) :
  ImplModule.getRule .rule_RL_execute a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_rule_RL_decode_rule_RL_execute hInv hb hc
  exact ⟨d, hd2, hd1⟩

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
      M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_fetch_core] at hc hb ⊢ <;>
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

theorem commutes_rule_RL_writeback_rule_RL_decode {a b c : ImplModule.State} (hInv : SbInv a) :
  ImplModule.getRule .rule_RL_writeback a c →
  ImplModule.getRule .rule_RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_rule_RL_decode_rule_RL_writeback hInv hb hc
  exact ⟨d, hd2, hd1⟩

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

-- fetch's guard is just `fifo_RDY_enq f2d`: uniformly false, since f2d is
-- always full in both phi0 shapes.
@[local grind →] theorem phi0_reaches_phi0_rule_RL_fetch (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_fetch i i' → phi0 i' s := by
  intro hphi0 hr
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hr1, hr2⟩ := Prod.mk.injEq .. |>.mp hr
  have hf2d_false : i.f2d_hasElement = false := by
    rcases h : i.f2d_hasElement with _ | _
    · rfl
    · simp [M_mktop_pipelined.fifo_RDY_enq, h] at hr1
  obtain ⟨_, _, _, _, _, hf2d, _, _, _, _, _, _⟩ := phi0_unfold hphi0
  simp [hf2d] at hf2d_false

-- decode's guard requires f2d full (always true) and either the fresh f2d
-- entry can't actually issue (Shape B, asserted directly) or d2e has no
-- room (Shape A -- using `rule_RL_decode_core_normal_branch` to resolve
-- decode's guard down to `fifo_RDY_enq d2eHasElement`, given matching
-- epoch tags, part of Shape A's definition -- legality is no longer needed
-- since decode issues legal/illegal instructions identically).
@[local grind →] theorem phi0_reaches_phi0_rule_RL_decode (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_decode i i' → phi0 i' s := by
  intro hphi0 hr
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule] at hr
  have hguard : (M_mktop_pipelined.rule_RL_decode i).1 = BTrue Unit_ := by rw [hr]
  obtain ⟨_, _, _, _, _, hf2d, hidEp, hieEp, hA | hB, _, _, _⟩ := phi0_unfold hphi0
  · obtain ⟨hd2e, _⟩ := hA
    dsimp only [M_mktop_pipelined.rule_RL_decode] at hguard
    rw [rule_RL_decode_core_normal_branch i.imem i.f2d_element i.dEp i.eEp i.sb i.rf i.pc
        i.d2e_element i.f2d_hasElement i.d2e_hasElement hidEp hieEp] at hguard
    dsimp only at hguard
    simp only [M_mktop_pipelined.fifo_RDY_deq, hf2d, hd2e, M_mktop_pipelined.fifo_RDY_enq] at hguard
    rcases h : decodeOperandsReady i.imem i.f2d_element i.sb with _ | _ <;> simp [h] at hguard
  · obtain ⟨_, hbad⟩ := hB
    exact hbad hguard

-- execute's guard requires d2e full (uniformly false in Shape B) and, when
-- d2e IS full (Shape A), e2w has no room -- `phi0`'s own Shape A conjunct
-- gives `d2e_element.ieEp = eEp` directly now.
@[local grind →] theorem phi0_reaches_phi0_rule_RL_execute (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_execute i i' → phi0 i' s := by
  intro hphi0 hr
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule] at hr
  have hguard : (M_mktop_pipelined.rule_RL_execute i).1 = BTrue Unit_ := by rw [hr]
  have close_via_d2e_empty (hd2e : i.d2e_hasElement = false) : False := by
    dsimp [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_execute_core,
      M_mktop_pipelined.fifo_RDY_deq] at hguard
    rw [hd2e] at hguard
    simp at hguard
  obtain ⟨_, _, _, _, he2w, _, _, _, hA | hB, _, _, _⟩ := phi0_unfold hphi0
  · obtain ⟨hd2e, hieEp⟩ := hA
    dsimp only [M_mktop_pipelined.rule_RL_execute] at hguard
    rw [rule_RL_execute_core_normal_branch i.d2e_element i.eEp i.sb i.pc i.dmem i.e2w_element
        i.d2e_hasElement i.e2w_hasElement hieEp] at hguard
    dsimp only at hguard
    simp only [M_mktop_pipelined.fifo_RDY_deq, hd2e, he2w, M_mktop_pipelined.fifo_RDY_enq] at hguard
    simp at hguard
  · obtain ⟨hd2e, _⟩ := hB
    exact close_via_d2e_empty hd2e

-- writeback's guard is just `fifo_RDY_deq e2w ∧ fifo_RDY_deq e2w ∧
-- fifo_RDY_enq commitQ` -- commitQ is always full in phi0, regardless of
-- shape.
@[local grind →] theorem phi0_reaches_phi0_rule_RL_writeback (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .rule_RL_writeback i i' → phi0 i' s := by
  intro hphi0 hr
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule] at hr
  have hguard : (M_mktop_pipelined.rule_RL_writeback i).1 = BTrue Unit_ := by rw [hr]
  have close_via (h : i.e2w_hasElement = false ∨ i.commitQ_hasElement = true) : False := by
    dsimp [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
      M_mktop_pipelined.fifo_RDY_deq, M_mktop_pipelined.fifo_RDY_enq] at hguard
    rcases h with h | h <;> simp [h] at hguard
  obtain ⟨_, hcq, _, _, _, _, _, _, _, _, _, _⟩ := phi0_unfold hphi0
  exact close_via (Or.inr hcq)

-- Unfolds `ImplModule.getMethod` for `meth_getCommit` down to the plain
-- function-level equation, dodging the raw `ofAVMethod0` existential (and
-- the `Footprint.arg0` injectivity step) at every call site below.
theorem ImplModule.getMethod_getCommit_iff {i i' : ImplModule.State} {v : t_commit} :
    ImplModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' ↔
      M_mktop_pipelined.meth_getCommit i = ⟨v, i'⟩ ∧ M_mktop_pipelined.meth_RDY_getCommit i = BTrue Unit_ := by
  dsimp [ImplModule, Module.getMethod, ofAVMethod0]
  constructor
  · rintro ⟨v', hmeth, harg, hrdy⟩
    have hv : v = v' := by
      simp only [Footprint.arg0, Footprint.mk.injEq] at harg
      exact eq_of_heq harg.2.2.2.2.2
    rw [hv]
    exact ⟨hmeth, hrdy⟩
  · rintro ⟨hmeth, hrdy⟩
    exact ⟨v, hmeth, rfl, hrdy⟩

theorem SpecModule.getMethod_getCommit_iff {i i' : SpecModule.State} {v : t_commit} :
    SpecModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' ↔
      M_mktop_pipelined.Spec.meth_getCommit i = ⟨v, i'⟩ ∧ M_mktop_pipelined.Spec.meth_RDY_getCommit i = BTrue Unit_ := by
  dsimp [SpecModule, Module.getMethod, ofAVMethod0]
  constructor
  · rintro ⟨v', hmeth, harg, hrdy⟩
    have hv : v = v' := by
      simp only [Footprint.arg0, Footprint.mk.injEq] at harg
      exact eq_of_heq harg.2.2.2.2.2
    rw [hv]
    exact ⟨hmeth, hrdy⟩
  · rintro ⟨hmeth, hrdy⟩
    exact ⟨v, hmeth, rfl, hrdy⟩

-- `rule_RL_fetch` neither reads nor writes `commitQ_hasElement`/`commitQ_element`
-- (its `_core` only takes `pc dEp eEp f2dHasElement`), and `meth_getCommit`
-- touches nothing BUT those two fields -- so the rule and the method act on
-- disjoint state and trivially commute in one step each way, regardless of
-- `phi0`/`PipeInv`/etc.
@[local grind →] theorem reconverge_rule_RL_fetch_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_fetch s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_fetch s'' s''' := by
  intro hr hm
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨hmeth, hrdy⟩ := hm
  dsimp [M_mktop_pipelined.meth_getCommit] at hmeth
  obtain ⟨hv, hs''⟩ := t_actionvalue_.mk.injEq .. |>.mp hmeth
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hg, hs'⟩ := Prod.mk.injEq .. |>.mp hr
  refine ⟨{ s' with commitQ_hasElement := false }, ?_, ?_⟩
  · rw [ImplModule.getMethod_getCommit_iff]
    dsimp [M_mktop_pipelined.meth_getCommit, M_mktop_pipelined.meth_RDY_getCommit]
    refine ⟨?_, ?_⟩
    · have hce : s'.commitQ_element = v := by rw [← hs']; exact hv
      rw [hce]
    · have hcb : s'.commitQ_hasElement = s.commitQ_hasElement := by rw [← hs']
      rw [hcb]; exact hrdy
  · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
      M_mktop_pipelined.rule_RL_fetch_core]
    rw [← hs'', ← hs']
    dsimp only
    rw [hg]

-- Same disjoint-field argument as fetch: `rule_RL_decode_core` reads only
-- `imem f2dElement dEp eEp sb rf pc d2eElement f2dHasElement d2eHasElement`
-- and `rule_RL_decode` writes only `f2d_hasElement pc dEp d2e_hasElement
-- d2e_element sb` -- none of which is `commitQ_hasElement`/`commitQ_element`.
-- `_core` is deliberately left un-dsimp'd (its internal squash/issue branch
-- is irrelevant): congruence on identical arguments suffices, without
-- needing to know which branch actually fires.
@[local grind →] theorem reconverge_rule_RL_decode_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_decode s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_decode s'' s''' := by
  intro hr hm
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨hmeth, hrdy⟩ := hm
  dsimp [M_mktop_pipelined.meth_getCommit] at hmeth
  obtain ⟨hv, hs''⟩ := t_actionvalue_.mk.injEq .. |>.mp hmeth
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode] at hr
  obtain ⟨hg, hs'⟩ := Prod.mk.injEq .. |>.mp hr
  refine ⟨{ s' with commitQ_hasElement := false }, ?_, ?_⟩
  · rw [ImplModule.getMethod_getCommit_iff]
    dsimp [M_mktop_pipelined.meth_getCommit, M_mktop_pipelined.meth_RDY_getCommit]
    refine ⟨?_, ?_⟩
    · have hce : s'.commitQ_element = v := by rw [← hs']; exact hv
      rw [hce]
    · have hcb : s'.commitQ_hasElement = s.commitQ_hasElement := by rw [← hs']
      rw [hcb]; exact hrdy
  · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode]
    rw [← hs'', ← hs']
    dsimp only
    rw [hg]

-- Same disjoint-field argument again: `rule_RL_execute_core` reads only
-- `d2eElement eEp sb pc dmem e2wElement d2eHasElement e2wHasElement` and
-- `rule_RL_execute` writes only `sb d2e_hasElement dmem eEp pc e2w_hasElement
-- e2w_element` -- again disjoint from `commitQ_hasElement`/`commitQ_element`.
@[local grind →] theorem reconverge_rule_RL_execute_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_execute s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_execute s'' s''' := by
  intro hr hm
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨hmeth, hrdy⟩ := hm
  dsimp [M_mktop_pipelined.meth_getCommit] at hmeth
  obtain ⟨hv, hs''⟩ := t_actionvalue_.mk.injEq .. |>.mp hmeth
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at hr
  obtain ⟨hg, hs'⟩ := Prod.mk.injEq .. |>.mp hr
  refine ⟨{ s' with commitQ_hasElement := false }, ?_, ?_⟩
  · rw [ImplModule.getMethod_getCommit_iff]
    dsimp [M_mktop_pipelined.meth_getCommit, M_mktop_pipelined.meth_RDY_getCommit]
    refine ⟨?_, ?_⟩
    · have hce : s'.commitQ_element = v := by rw [← hs']; exact hv
      rw [hce]
    · have hcb : s'.commitQ_hasElement = s.commitQ_hasElement := by rw [← hs']
      rw [hcb]; exact hrdy
  · dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute]
    rw [← hs'', ← hs']
    dsimp only
    rw [hg]

-- Writeback's guard requires `commitQ_hasElement = false` (`fifo_RDY_enq`,
-- to have room to push its own retirement record) while `getCommit`'s guard
-- requires `commitQ_hasElement = true` (`fifo_RDY_deq`, to have something to
-- drain) -- both read at the SAME state `s`, so the two hypotheses are
-- jointly contradictory and this holds vacuously.
@[local grind →] theorem reconverge_rule_RL_writeback_meth_getCommit (s s' s'' : ImplModule.State) (v : t_commit) :
  ImplModule.getRule .rule_RL_writeback s s' →
  ImplModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.meth_getCommit, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .rule_RL_writeback s'' s''' := by
  intro hr hm
  exfalso
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨_, hrdy⟩ := hm
  dsimp [M_mktop_pipelined.meth_RDY_getCommit, M_mktop_pipelined.fifo_RDY_deq] at hrdy
  dsimp [ImplModule, Module.getRule, ofRule] at hr
  have hguard : (M_mktop_pipelined.rule_RL_writeback s).1 = BTrue Unit_ := by rw [hr]
  dsimp [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_writeback_core,
    M_mktop_pipelined.fifo_RDY_deq, M_mktop_pipelined.fifo_RDY_enq] at hguard
  rcases h : s.commitQ_hasElement with _ | _
  · simp [h] at hrdy
  · simp [h] at hguard

-- `phi0`'s `i.commitQ_element = (Spec.stepOne s).2` conjunct is exactly the
-- fact needed: impl's `getCommit` returns `i.commitQ_element` (= `v`), which
-- by that equation is exactly the value spec's own (unconditionally ready)
-- `getCommit` returns from `s`.
@[local grind →] theorem flush_indistinguishable_meth_getCommit
    (i i' : ImplModule.State) (s : SpecModule.State) (v : t_commit) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s' := by
  intro hphi0 hm
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨hmeth, _⟩ := hm
  dsimp [M_mktop_pipelined.meth_getCommit] at hmeth
  obtain ⟨hv, _⟩ := t_actionvalue_.mk.injEq .. |>.mp hmeth
  obtain ⟨_, _, hcqe, _, _, _, _, _, _, _, _, _⟩ := phi0_unfold hphi0
  have hveq : (M_mktop_pipelined.Spec.stepOne s).2 = v := hcqe.symm.trans hv
  refine ⟨(M_mktop_pipelined.Spec.stepOne s).1, ?_⟩
  rw [SpecModule.getMethod_getCommit_iff]
  refine ⟨?_, rfl⟩
  dsimp [M_mktop_pipelined.Spec.meth_getCommit]
  rw [hveq]

-- Almost definitional now: `phi0_unfold` already hands us an `i''` reachable
-- (via pure rules, from `i` with `commitQ` cleared) that's `phi0`-related to
-- `specStepN s 1` -- exactly `i'`/`s'`, since both `getCommit` calls (impl's
-- and spec's) are deterministic functions computing precisely that.
@[local grind →] theorem reach_flush_again_meth_getCommit
    (i i' : ImplModule.State) (s s' : SpecModule.State) (v : t_commit) :
  phi0 i s →
  ImplModule.getMethod i ⟨.meth_getCommit, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.meth_getCommit, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hphi0 hm hsm
  rw [ImplModule.getMethod_getCommit_iff] at hm
  obtain ⟨hmeth, _⟩ := hm
  dsimp [M_mktop_pipelined.meth_getCommit] at hmeth
  obtain ⟨_, hi'⟩ := t_actionvalue_.mk.injEq .. |>.mp hmeth
  rw [SpecModule.getMethod_getCommit_iff] at hsm
  obtain ⟨hsmeth, _⟩ := hsm
  dsimp [M_mktop_pipelined.Spec.meth_getCommit] at hsmeth
  obtain ⟨_, hs'⟩ := t_actionvalue_.mk.injEq .. |>.mp hsmeth
  obtain ⟨_, _, _, _, _, _, _, _, _, i'', hreach, hphi0''⟩ := phi0_unfold hphi0
  rw [hi'] at hreach
  have hs1 : specStepN s 1 = s' := hs'
  rw [hs1] at hphi0''
  exact ⟨i'', hreach, hphi0''⟩

-- Termination argument, now machine-checked via an explicit decreasing
-- measure. `commitQ_hasElement` is monotonic under the rule-only relation
-- (only rule_RL_writeback ever sets it, and only false→true), so writeback
-- fires at most once; that cascades backward -- e2w's "fills" (execute's
-- normal branch) are bounded via commitQ, d2e's "fills" (decode's normal
-- branch) are bounded via e2w, and f2d's "fills" (fetch) are bounded via
-- d2e -- while the squash branches (stale idEp/ieEp) are bounded by the same
-- chain since they only ever fire on an entry that a *prior*, already-bounded
-- normal-branch redirect made stale.
--
-- `mu` below encodes this as a single Nat, built bottom-up: `b0` is
-- writeback's remaining budget (0 or 1); `totalE` is the e2w/commitQ pair's
-- remaining total events (fills+drains); `totalD`/`totalF` do the same for
-- d2e and f2d, each also adding a `freeDrain*` bonus term for "this stage's
-- current occupant is already stale, so it can drain via squash for free,
-- independent of downstream capacity". Every one of the 4 rules (in every
-- branch) strictly decreases `mu`, verified directly below rather than via
-- the lexicographic-tuple sketch from an earlier draft of this comment.
theorem strongly_normalising_of_measure {A : Type} (α : ReachingStar.Rule A) (mm : A → Nat)
    (h : ∀ a b, α a b → mm b < mm a) : strongly_normalising α := by
  intro a
  generalize hn : mm a = n
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    subst hn
    apply strongly_normalising'.step
    intro b hab
    exact ih (mm b) (h a b hab) b rfl

def b0 (i : ImplModule.State) : Nat := if i.commitQ_hasElement then 0 else 1
def totalE (i : ImplModule.State) : Nat := (if i.e2w_hasElement then 0 else 1) + 2 * b0 i
def freeDrainD2e (i : ImplModule.State) : Nat :=
  if i.d2e_hasElement ∧ i.d2e_element.ieEp ≠ i.eEp then 1 else 0
def totalD (i : ImplModule.State) : Nat :=
  (if i.d2e_hasElement then 0 else 1) + 2 * totalE i + 2 * freeDrainD2e i
def freeDrainF2d (i : ImplModule.State) : Nat :=
  if i.f2d_hasElement ∧ (i.f2d_element.idEp ≠ i.dEp ∨ i.f2d_element.ieEp ≠ i.eEp) then 1 else 0
def totalF (i : ImplModule.State) : Nat :=
  (if i.f2d_hasElement then 0 else 1) + 3 * totalD i + 2 * freeDrainF2d i

def mu (i : ImplModule.State) : Nat := totalF i

theorem freeDrainF2d_le_one (i : ImplModule.State) : freeDrainF2d i ≤ 1 := by
  unfold freeDrainF2d; split <;> omega

theorem mu_dec_fetch {i i' : ImplModule.State} (hr : ImplModule.getRule .rule_RL_fetch i i') :
    mu i' < mu i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
  have hf2d : i.f2d_hasElement = false := by
    rcases h : i.f2d_hasElement with _ | _
    · rfl
    · simp [M_mktop_pipelined.fifo_RDY_enq, h] at hg
  subst hi'
  dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d]
  simp [hf2d]

theorem mu_dec_decode {i i' : ImplModule.State} (hr : ImplModule.getRule .rule_RL_decode i i') :
    mu i' < mu i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode] at hr
  by_cases hidEp : i.f2d_element.idEp = i.dEp
  · by_cases hieEp : i.f2d_element.ieEp = i.eEp
    · -- normal issue: d2e was empty, becomes full & fresh
      rw [rule_RL_decode_core_normal_branch i.imem i.f2d_element i.dEp i.eEp i.sb i.rf i.pc
          i.d2e_element i.f2d_hasElement i.d2e_hasElement hidEp hieEp] at hr
      obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
      have hf2d : i.f2d_hasElement = true := by
        rcases h : i.f2d_hasElement with _ | _
        · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
        · rfl
      have hd2e : i.d2e_hasElement = false := by
        rcases h : i.d2e_hasElement with _ | _
        · rfl
        · simp [M_mktop_pipelined.fifo_RDY_deq, M_mktop_pipelined.fifo_RDY_enq, h] at hg
      subst hi'
      dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d, decodeD2eNormal]
      simp [hf2d, hd2e, hidEp, hieEp]
      omega
    · -- squash via ieEp mismatch: d2e untouched
      rw [rule_RL_decode_core_squash_branch i.imem i.f2d_element i.dEp i.eEp i.sb i.rf i.pc
          i.d2e_element i.f2d_hasElement i.d2e_hasElement hidEp hieEp] at hr
      obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
      have hf2d : i.f2d_hasElement = true := by
        rcases h : i.f2d_hasElement with _ | _
        · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
        · rfl
      subst hi'
      dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d]
      simp [hf2d, hidEp, hieEp]
      omega
  · -- squash via idEp mismatch: d2e untouched, regardless of ieEp
    rw [rule_RL_decode_core_squash_branch_idEp i.imem i.f2d_element i.dEp i.eEp i.sb i.rf i.pc
        i.d2e_element i.f2d_hasElement i.d2e_hasElement hidEp] at hr
    obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
    have hf2d : i.f2d_hasElement = true := by
      rcases h : i.f2d_hasElement with _ | _
      · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
      · rfl
    subst hi'
    dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d]
    simp [hf2d, hidEp]
    omega

theorem mu_dec_execute {i i' : ImplModule.State} (hr : ImplModule.getRule .rule_RL_execute i i') :
    mu i' < mu i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute] at hr
  by_cases hieEp : i.d2e_element.ieEp = i.eEp
  · -- normal: e2w was empty, becomes full; f2d's own freshness may flip
    -- (worst case) due to this redirect's eEp bump, so bound it generically
    -- via `freeDrainF2d_le_one` rather than computing its exact new value.
    rw [rule_RL_execute_core_normal_branch i.d2e_element i.eEp i.sb i.pc i.dmem i.e2w_element
        i.d2e_hasElement i.e2w_hasElement hieEp] at hr
    obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
    have hd2e : i.d2e_hasElement = true := by
      rcases h : i.d2e_hasElement with _ | _
      · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
      · rfl
    have he2w : i.e2w_hasElement = false := by
      rcases h : i.e2w_hasElement with _ | _
      · rfl
      · simp [M_mktop_pipelined.fifo_RDY_deq, M_mktop_pipelined.fifo_RDY_enq, h] at hg
    have hbound := freeDrainF2d_le_one i'
    subst hi'
    dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d] at hbound ⊢
    simp [hd2e, he2w, hieEp] at hbound ⊢
    split_ifs at hbound ⊢ <;> omega
  · -- squash: d2e's stale occupant releases for free; f2d/eEp untouched
    rw [rule_RL_execute_core_squash_branch i.d2e_element i.eEp i.sb i.pc i.dmem i.e2w_element
        i.d2e_hasElement i.e2w_hasElement hieEp] at hr
    obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
    have hd2e : i.d2e_hasElement = true := by
      rcases h : i.d2e_hasElement with _ | _
      · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
      · rfl
    subst hi'
    dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d]
    simp [hd2e, hieEp]
    omega

theorem mu_dec_writeback {i i' : ImplModule.State} (hr : ImplModule.getRule .rule_RL_writeback i i') :
    mu i' < mu i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨hg, hi'⟩ := Prod.mk.injEq .. |>.mp hr
  have he2w : i.e2w_hasElement = true := by
    rcases h : i.e2w_hasElement with _ | _
    · simp [M_mktop_pipelined.fifo_RDY_deq, h] at hg
    · rfl
  have hcq : i.commitQ_hasElement = false := by
    rcases h : i.commitQ_hasElement with _ | _
    · rfl
    · simp [M_mktop_pipelined.fifo_RDY_deq, M_mktop_pipelined.fifo_RDY_enq, h] at hg
  subst hi'
  dsimp [mu, totalF, totalD, totalE, freeDrainD2e, b0, freeDrainF2d]
  simp [he2w, hcq]

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  apply strongly_normalising_of_measure ImplModule.getARule mu
  intro a b hab
  obtain ⟨r, hr⟩ := hab
  cases r with
  | rule_RL_fetch => exact mu_dec_fetch hr
  | rule_RL_decode => exact mu_dec_decode hr
  | rule_RL_execute => exact mu_dec_execute hr
  | rule_RL_writeback => exact mu_dec_writeback hr

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
