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

-- One instruction, mirroring what the pipeline does with it (decode, execute, memory, writeback):
--   * operands read as 0 when the register is x0, unused by the instruction, or the instruction is
--     illegal (as in `RL_decode`);
--   * memories are indexed like the BRAMs: word address `(addr >> 2)[19:0]`;
--   * illegal instructions still perform their memory access and produce a commit record, but do
--     not write `rf` and fall through to `pc + 4`;
--   * the commit record's `data` is reported whenever `valid_rd` (as in `RL_writeback`), while `rf`
--     is only written for legal instructions with `rd ≠ x0`;
--   * commit records are appended, so `getCommitInst` returns them oldest first.
def stepOne (s : State) : State :=
  let pc := s.pc
  let instr := s.imem.getD (extract_bits (shift_right_logical pc 2) 19 0).toNat default
  let dInst := RVUtil.decodeInst instr
  let fields := RVUtil.getInstFields instr
  let rdIdx := fields.rd
  let isValidRd := bool_and (bool_and dInst.valid_rd dInst.legal)
    (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
  let rs1Idx := fields.rs1
  let rs2Idx := fields.rs2
  let rv1 := ite_bsv (bool_or (bool_or (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                (bool_not dInst.valid_rs1)) (bool_not dInst.legal))
              (0 : BitVec 32) (arr_get s.rf rs1Idx.toNat)
  let rv2 := ite_bsv (bool_or (bool_or (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                (bool_not dInst.valid_rs2)) (bool_not dInst.legal))
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
    else if size == (0b10 : BitVec 2) then shift_left (0b1111 : BitVec 4) offset
    else 0
  let dataMem := shift_left rv2 shiftAmount
  let addrMem : BitVec 20 :=
    extract_bits (shift_right_logical (concat_bits (extract_bits addr0 31 2) 2 (0 : BitVec 2)) 2) 19 0
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
  let commitInfo : t_commitinst :=
    { inst := instr, pc := pc, rd := rdIdx, data := ite_bsv dInst.valid_rd finalData 0 }
  { s with
      rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
      dmem := newDmem,
      pc := ite_bsv (bool_and dInst.legal (bool_not isMemInst)) nextPC (pc + (4 : BitVec 32)),
      halted := ite_bsv dInst.legal s.halted 1,
      output := s.output ++ [commitInfo] }

def meth_doFetch (s : State) : t_actionvalue_ unit_ State :=
  let s' := stepOne s
  { avValue_ := Unit_, avAction_ := s' }
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

-- Reachability of implementation states, modelled on `MSI.LTS.reachable` in
-- `StarExperimental/MSI_def.lean`: a step is either a rule firing or a method call from the
-- environment.
def ImplModule.atrans (s s' : ImplModule.State) : Prop :=
  ImplModule.getARule s s' ∨ ∃ e, ImplModule.getMethod s e s'

-- Initial (reset) states: all FIFOs (including the BRAMs' read-result queues) empty, scoreboard
-- cleared, epoch 0. `pc`, `rf` and the
-- memories are left abstract, since they do not influence the control of the processor.
def ImplModule.init (s : ImplModule.State) : Prop :=
  s.ireq.queue = [] ∧ s.dreq.queue = [] ∧
  s.toImem.queue = [] ∧ s.fromImem.queue = [] ∧
  s.toDmem.queue = [] ∧ s.fromDmem.queue = [] ∧
  s.f2d.queue = [] ∧ s.d2e.queue = [] ∧ s.e2w.queue = [] ∧
  s.retiredInst.queue = [] ∧
  s.sb = Array.replicate 32 0 ∧
  s.ep = 0 ∧
  s.iMem.readResult = [] ∧ s.dMem.readResult = []

-- Unlike `MSI.LTS.reachable` (which quantifies over *all* initial states, fine there because
-- `msi_init` has a single model), reachability here is from *some* initial state: `init` leaves
-- `pc`, `rf` and the memories free, and requiring every choice of them to reach `s` would make
-- almost no state reachable.
def ImplModule.reachable (s : ImplModule.State) : Prop :=
  ∃ s_init, ImplModule.init s_init ∧ Relation.ReflTransGen ImplModule.atrans s_init s

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v : unit_), e.1 = .doFetch ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (v : t_commitinst), e.1 = .getCommitInst ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, fp⟩ := e
  cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0] at h <;> obtain ⟨v, -, rfl, -⟩ := h
  · exact .inl ⟨v, rfl, rfl⟩
  · exact .inr ⟨v, rfl, rfl⟩

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : unit_), e.1 = .doFetch ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (v : t_commitinst), e.1 = .getCommitInst ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, fp⟩ := e
  cases name <;> dsimp only [SpecModule, Module.getMethod, ofAVMethod0] at h <;> obtain ⟨v, -, rfl, -⟩ := h
  · exact .inl ⟨v, rfl, rfl⟩
  · exact .inr ⟨v, rfl, rfl⟩

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .RL_requestI i i' ∨ ImplModule.getRule .RL_responseI i i' ∨ ImplModule.getRule .RL_requestD i i' ∨ ImplModule.getRule .RL_responseD i i' ∨ ImplModule.getRule .RL_decode i i' ∨ ImplModule.getRule .RL_execute i i' ∨ ImplModule.getRule .RL_writeback i i' := by
  rintro ⟨r, h⟩
  cases r <;> simp only [h, true_or, or_true]

-- ──────────────────────────────────────────────────────────────────────
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- Helpers for the commute proofs (adapted from CompiledProcessor/mktop_pipelined_refines.lean
-- to the unbounded, list-based `M_mkFIFO`).
@[simp] theorem bool_and_true_iff (p q : t_bool) :
    bool_and p q = BTrue Unit_ ↔ p = BTrue Unit_ ∧ q = BTrue Unit_ := by
  cases p <;> cases q <;> simp [bool_and]

@[simp] theorem bool_and_true_left (p : t_bool) : bool_and (BTrue Unit_) p = p := rfl

@[simp] theorem bool_and_true_right (p : t_bool) : bool_and p (BTrue Unit_) = p := by
  cases p <;> rfl

@[simp] theorem mkSimpleBRAM_RDY_put_true [Inhabited α] (s : M_mkSimpleBRAM.state α) :
    M_mkSimpleBRAM.meth_RDY_put s = BTrue Unit_ := rfl

@[simp] theorem mkSimpleBRAM_RDY_read_iff [Inhabited α] (s : M_mkSimpleBRAM.state α) :
    M_mkSimpleBRAM.meth_RDY_read s = BTrue Unit_ ↔ s.readResult ≠ [] := by
  unfold M_mkSimpleBRAM.meth_RDY_read; split <;> simp_all

@[simp] theorem mkFIFO_RDY_enq_true [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_enq s = BTrue Unit_ := rfl

@[simp] theorem mkFIFO_RDY_deq_iff [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_deq s = BTrue Unit_ ↔ s.queue ≠ [] := by
  unfold M_mkFIFO.meth_RDY_deq; split <;> simp_all

@[simp] theorem mkFIFO_RDY_first_iff [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_first s = BTrue Unit_ ↔ s.queue ≠ [] := by
  unfold M_mkFIFO.meth_RDY_first; split <;> simp_all

-- Term-level forms, for ready signals nested inside guards rather than equated to `BTrue`.
theorem mkFIFO_RDY_deq_of_ne [Inhabited α] {s : M_mkFIFO.state α} (h : s.queue ≠ []) :
    M_mkFIFO.meth_RDY_deq s = BTrue Unit_ := (mkFIFO_RDY_deq_iff s).mpr h

theorem mkFIFO_RDY_first_of_ne [Inhabited α] {s : M_mkFIFO.state α} (h : s.queue ≠ []) :
    M_mkFIFO.meth_RDY_first s = BTrue Unit_ := (mkFIFO_RDY_first_iff s).mpr h

@[simp] theorem mkFIFO_RDY_deq_enq [Inhabited α] (s : M_mkFIFO.state α) (x : α) :
    M_mkFIFO.meth_RDY_deq (M_mkFIFO.meth_enq s x).avAction_ = BTrue Unit_ :=
  mkFIFO_RDY_deq_of_ne (by simp [M_mkFIFO.meth_enq])

@[simp] theorem mkFIFO_RDY_first_enq [Inhabited α] (s : M_mkFIFO.state α) (x : α) :
    M_mkFIFO.meth_RDY_first (M_mkFIFO.meth_enq s x).avAction_ = BTrue Unit_ :=
  mkFIFO_RDY_first_of_ne (by simp [M_mkFIFO.meth_enq])

@[simp] theorem mkFIFO_enq_queue [Inhabited α] (s : M_mkFIFO.state α) (x : α) :
    (M_mkFIFO.meth_enq s x).avAction_.queue = s.queue ++ [x] := rfl

-- Enqueueing at the back of a non-empty queue does not affect its front.
theorem mkFIFO_first_enq [Inhabited α] (s : M_mkFIFO.state α) (x : α) (h : s.queue ≠ []) :
    M_mkFIFO.meth_first (M_mkFIFO.meth_enq s x).avAction_ = M_mkFIFO.meth_first s := by
  obtain ⟨q⟩ := s; cases q <;> simp_all [M_mkFIFO.meth_first, M_mkFIFO.meth_enq]

theorem mkFIFO_deq_enq [Inhabited α] (s : M_mkFIFO.state α) (x : α) (h : s.queue ≠ []) :
    (M_mkFIFO.meth_deq (M_mkFIFO.meth_enq s x).avAction_).avAction_
      = (M_mkFIFO.meth_enq (M_mkFIFO.meth_deq s).avAction_ x).avAction_ := by
  obtain ⟨q⟩ := s; cases q <;> simp_all [M_mkFIFO.meth_deq, M_mkFIFO.meth_enq]

theorem state_ext {s t : M_mktop_pipelined.state}
    (h0 : s.iMem = t.iMem)
    (h1 : s.dMem = t.dMem)
    (h2 : s.ireq = t.ireq)
    (h3 : s.dreq = t.dreq)
    (h4 : s.toImem = t.toImem)
    (h5 : s.fromImem = t.fromImem)
    (h6 : s.toDmem = t.toDmem)
    (h7 : s.fromDmem = t.fromDmem)
    (h8 : s.f2d = t.f2d)
    (h9 : s.d2e = t.d2e)
    (h10 : s.e2w = t.e2w)
    (h11 : s.retiredInst = t.retiredInst)
    (h12 : s.pc = t.pc)
    (h13 : s.ep = t.ep)
    (h14 : s.rf = t.rf)
    (h15 : s.sb = t.sb) :
    s = t := by
  cases s; cases t; simp_all

-- Two read-modify-write decrements of (possibly equal) scoreboard entries commute.
theorem arr_sub_comm (a : Array Nat) (i j : Nat) (u v : Nat) :
    arr_set (arr_set a i (arr_get a i - u)) j (arr_get (arr_set a i (arr_get a i - u)) j - v) =
    arr_set (arr_set a j (arr_get a j - v)) i (arr_get (arr_set a j (arr_get a j - v)) i - u) := by
  unfold arr_set arr_get
  apply Array.ext (by simp)
  intro k h1 h2
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at h1 h2
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp_all
  subst_vars; simp_all [Nat.sub_right_comm]

theorem writeback_e2w_ne (s : M_mktop_pipelined.state)
    (h : (M_mktop_pipelined.rule_RL_writeback s).1 = BTrue Unit_) : s.e2w.queue ≠ [] := by
  exact (mkFIFO_RDY_deq_iff _).mp ((bool_and_true_iff _ _).mp h).1

theorem writeback_mem_fromDmem (s : M_mktop_pipelined.state)
    (h : (M_mktop_pipelined.rule_RL_writeback s).1 = BTrue Unit_) :
    RVUtil.isMemoryInst (M_mkFIFO.meth_first s.e2w).dInst = BTrue Unit_ → s.fromDmem.queue ≠ [] := by
  intro hm
  have h1 := ((bool_and_true_iff _ _).mp h).2
  have h3 := ((bool_and_true_iff _ _).mp h1).1
  split at h3
  · exact (mkFIFO_RDY_deq_iff _).mp ((bool_and_true_iff _ _).mp h3).1
  · simp_all

theorem execute_d2e_ne (s : M_mktop_pipelined.state)
    (h : (M_mktop_pipelined.rule_RL_execute s).1 = BTrue Unit_) : s.d2e.queue ≠ [] :=
  (mkFIFO_RDY_deq_iff _).mp ((bool_and_true_iff _ _).mp h).1

-- Every 1-bit vector is `0#1` or `1#1`.
theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  rcases x with ⟨⟨_ | _ | n, hn⟩⟩
  · exact .inl rfl
  · exact .inr rfl
  · (simp at hn) <;> omega

open M_mktop_pipelined in
theorem execute_writeback_core (a : M_mktop_pipelined.state)
    (hc1 : (rule_RL_execute a).1 = BTrue Unit_) (hb1 : (rule_RL_writeback a).1 = BTrue Unit_) :
    (rule_RL_writeback (rule_RL_execute a).2).1 = BTrue Unit_ ∧
    (rule_RL_execute (rule_RL_writeback a).2).1 = BTrue Unit_ ∧
    (rule_RL_writeback (rule_RL_execute a).2).2 = (rule_RL_execute (rule_RL_writeback a).2).2 := by
  have he := writeback_e2w_ne a hb1
  have hd := execute_d2e_ne a hc1
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
  obtain ⟨_ | ⟨z, zs⟩⟩ := e2w
  · simp at he
  obtain ⟨_ | ⟨w, ws⟩⟩ := d2e
  · simp at hd
  obtain ⟨dInst, wpc, ppc, iEp, rv1, rv2⟩ := w
  rcases bv1_cases iEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl
  all_goals
    refine ⟨hb1, hc1, ?_⟩
    apply state_ext <;> try rfl
  all_goals (dsimp only [rule_RL_execute, rule_RL_writeback]; exact arr_sub_comm ..)

open M_mktop_pipelined in
theorem responseD_writeback_core (a : M_mktop_pipelined.state)
    (hc1 : (rule_RL_responseD a).1 = BTrue Unit_) (hb1 : (rule_RL_writeback a).1 = BTrue Unit_) :
    (rule_RL_writeback (rule_RL_responseD a).2).1 = BTrue Unit_ ∧
    (rule_RL_responseD (rule_RL_writeback a).2).1 = BTrue Unit_ ∧
    (rule_RL_writeback (rule_RL_responseD a).2).2 = (rule_RL_responseD (rule_RL_writeback a).2).2 := by
  have he := writeback_e2w_ne a hb1
  have hmf := writeback_mem_fromDmem a hb1
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
  obtain ⟨_ | ⟨z, zs⟩⟩ := e2w
  · simp at he
  refine ⟨?_, hc1, ?_⟩
  all_goals
    rcases hm : RVUtil.isMemoryInst z.dInst with ⟨⟩ | ⟨⟩
  -- Memory instruction: `fromDmem` is non-empty, so enqueueing at its back is invisible to
  -- writeback. Otherwise writeback does not look at `fromDmem`. Either way, once the
  -- instruction class is substituted into the unfolded rules, both sides agree definitionally.
  all_goals
    first
      | (have hne := hmf hm
         obtain ⟨_ | ⟨y, ys⟩⟩ := fromDmem
         · simp at hne)
      | skip
  all_goals
    first
      | exact hb1
      | (apply state_ext <;> try rfl
         all_goals
           dsimp only [rule_RL_writeback, rule_RL_responseD, M_mkFIFO.meth_first, List.headD_cons]
           rewrite [hm]
           rfl)
      | (dsimp only [rule_RL_writeback, rule_RL_responseD, M_mkFIFO.meth_first, List.headD_cons] at hb1 ⊢
         rewrite [hm] at hb1 ⊢
         exact hb1)

-- ──────────────────────────────────────────────────────────────────────
-- Reachability invariants: the scoreboard counts in-flight writers, and epochs are ordered.
section Invariants
open RVUtil M_mktop_pipelined

-- ── Array helpers ─────────────────────────────────────────────────────────
@[simp] theorem arr_set_size {α} (a : Array α) (i : Nat) (v : α) : (arr_set a i v).size = a.size := by
  simp [arr_set]

theorem arr_get_set [Inhabited α] (a : Array α) (i j : Nat) (v : α) (hi : i < a.size) :
    arr_get (arr_set a i v) j = if i = j then v else arr_get a j := by
  unfold arr_get arr_set
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases hij : i = j <;> simp_all

-- ── Scoreboard invariant ──────────────────────────────────────────────────
-- Whether an instruction writes a register (the condition the rules use to update `sb`).
def wr (d : t_decodedinst) : t_bool :=
  bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 d.valid_rd) (bool_to_bitvec1 d.legal))
    (bool_to_bitvec1 (bool_not (if ((getInstFields d.inst).rd == (0 : BitVec 5)) then BTrue Unit_ else BFalse Unit_))))

def writes (r : Nat) (d : t_decodedinst) : Bool :=
  match wr d with
  | BTrue _ => (getInstFields d.inst).rd.toNat == r
  | BFalse _ => false

-- Number of in-flight (`d2e`/`e2w`) writers of register `r`.
def inflight (s : state) (r : Nat) : Nat :=
  (s.d2e.queue.map (·.dInst)).countP (writes r) + (s.e2w.queue.map (·.dInst)).countP (writes r)

def SBInv (s : state) : Prop :=
  s.sb.size = 32 ∧ ∀ r < 32, arr_get s.sb r = inflight s r

theorem decode_fromImem_ne (s : state) (h : (rule_RL_decode s).1 = BTrue Unit_) :
    s.fromImem.queue ≠ [] := by
  simp only [rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff] at h
  casesm* _ ∧ _
  assumption

@[simp] theorem decodeInst_inst (x : BitVec 32) : (decodeInst x).inst = x := rfl

theorem writes_of_wr_true {d : t_decodedinst} {u} (r : Nat) (h : wr d = BTrue u) :
    writes r d = ((getInstFields d.inst).rd.toNat == r) := by
  simp [writes, h]

theorem writes_of_wr_false {d : t_decodedinst} {u} (r : Nat) (h : wr d = BFalse u) :
    writes r d = false := by
  simp [writes, h]

theorem rd_lt (x : BitVec 32) : (getInstFields x).rd.toNat < 32 := (getInstFields x).rd.isLt

theorem sbinv_decode (s : state) (h : SBInv s) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    SBInv (rule_RL_decode s).2 := by
  obtain ⟨hsz, hc⟩ := h
  refine ⟨?_, fun r hr => ?_⟩
  · dsimp only [rule_RL_decode]; split <;> simp [hsz]
  · have hr' := hc r hr
    unfold inflight at *
    dsimp only [rule_RL_decode]
    split
    · split
      all_goals
        rename_i hw
        rw [arr_get_set _ _ _ _ (by rw [hsz]; exact rd_lt _)]
        simp only [M_mkFIFO.meth_enq, List.map_append, List.countP_append, List.map_cons,
          List.map_nil, List.countP_cons, List.countP_nil]
      · rw [writes_of_wr_true r (d := decodeInst (M_mkFIFO.meth_first s.fromImem).data) hw]
        by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rd.toNat = r <;>
          simp_all <;> omega
      · rw [writes_of_wr_false r (d := decodeInst (M_mkFIFO.meth_first s.fromImem).data) hw]
        by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rd.toNat = r <;>
          simp_all
    · exact hr'

theorem sbinv_execute (s : state) (h : SBInv s) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    SBInv (rule_RL_execute s).2 := by
  have hne := execute_d2e_ne s hg
  obtain ⟨hsz, hc⟩ := h
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨_ | ⟨w, ws⟩⟩, e2w, retiredInst,
    pc, ep, rf, sb⟩ := s
  · simp at hne
  refine ⟨?_, fun r hr => ?_⟩
  · dsimp only [rule_RL_execute]; split <;> simp_all
  · have hr' := hc r hr
    unfold inflight at *
    dsimp only [rule_RL_execute]
    simp only [M_mkFIFO.meth_enq, M_mkFIFO.meth_deq, M_mkFIFO.meth_first, List.headD_cons, List.tail_cons,
      List.map_append, List.countP_append, List.map_cons, List.map_nil, List.countP_cons,
      List.countP_nil] at hr' ⊢
    split
    · -- squashed: the head of `d2e` leaves the pipeline, and its `sb` count is released
      split
      all_goals
        rename_i hw
        rw [arr_get_set _ _ _ _ (by rw [hsz]; exact rd_lt _)]
      · rw [writes_of_wr_true r (d := w.dInst) hw] at hr'
        by_cases hrd : (getInstFields w.dInst.inst).rd.toNat = r <;> simp_all <;> omega
      · rw [writes_of_wr_false r (d := w.dInst) hw] at hr'
        by_cases hrd : (getInstFields w.dInst.inst).rd.toNat = r <;> simp_all
    · -- not squashed: the head moves from `d2e` to `e2w`
      simp only [List.map_append, List.countP_append, List.map_cons, List.map_nil, List.countP_cons,
        List.countP_nil] at hr' ⊢
      omega

theorem sbinv_writeback (s : state) (h : SBInv s) (hg : (rule_RL_writeback s).1 = BTrue Unit_) :
    SBInv (rule_RL_writeback s).2 := by
  have hne := writeback_e2w_ne s hg
  obtain ⟨hsz, hc⟩ := h
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, ⟨_ | ⟨w, ws⟩⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  refine ⟨?_, fun r hr => ?_⟩
  · dsimp only [rule_RL_writeback]; simp_all
  · have hr' := hc r hr
    unfold inflight at *
    dsimp only [rule_RL_writeback]
    simp only [M_mkFIFO.meth_deq, M_mkFIFO.meth_first, List.headD_cons, List.tail_cons,
      List.map_cons, List.countP_cons] at hr' ⊢
    split
    all_goals
      rename_i hw
      rw [arr_get_set _ _ _ _ (by rw [hsz]; exact rd_lt _)]
    · rw [writes_of_wr_true r (d := w.dInst) hw] at hr'
      by_cases hrd : (getInstFields w.dInst.inst).rd.toNat = r <;> simp_all <;> omega
    · rw [writes_of_wr_false r (d := w.dInst) hw] at hr'
      by_cases hrd : (getInstFields w.dInst.inst).rd.toNat = r <;> simp_all

-- The operand-readiness part of decode's guard, as a 1-bit formula over its atoms.
theorem decode_ready_iff (F v1 v2 : t_bool) (e1 e2 : Bool) :
    bitvec1_to_bool (bit_or (bit_and (bit_and (bool_to_bitvec1 F)
        (bit_or (bit_and (bool_to_bitvec1 v1) (bool_to_bitvec1 (if e1 = true then BTrue Unit_ else BFalse Unit_)))
          (bit_not (bool_to_bitvec1 v1))))
        (bit_or (bit_and (bool_to_bitvec1 v2) (bool_to_bitvec1 (if e2 = true then BTrue Unit_ else BFalse Unit_)))
          (bit_not (bool_to_bitvec1 v2))))
      (bool_to_bitvec1 (bool_not F))) = BTrue Unit_ ↔
    (F = BTrue Unit_ → (v1 = BTrue Unit_ → e1 = true) ∧ (v2 = BTrue Unit_ → e2 = true)) := by
  rcases F with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases v1 with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases v2 with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    cases e1 <;> cases e2 <;>
    simp (config := {decide := true}) [bitvec1_to_bool, bit_or, bit_and, bit_not, bool_to_bitvec1, bool_not]

theorem arr_get_set_ne [Inhabited α] (a : Array α) (i j : Nat) (v : α) (h : i ≠ j) :
    arr_get (arr_set a i v) j = arr_get a j := by
  unfold arr_get arr_set
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  simp [h]

theorem arr_get_set_self [Inhabited α] (a : Array α) (i : Nat) :
    arr_get (arr_set a i (arr_get a i)) i = arr_get a i := by
  unfold arr_get arr_set
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : i < a.size <;> simp [h]

theorem writeback_rf_get (s : state) (j : Nat) (hj : writes j (M_mkFIFO.meth_first s.e2w).dInst = false) :
    arr_get (rule_RL_writeback s).2.rf j = arr_get s.rf j := by
  dsimp only [rule_RL_writeback]
  by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.e2w).dInst.inst).rd.toNat = j
  · have hw : ∃ u, wr (M_mkFIFO.meth_first s.e2w).dInst = BFalse u := by
      unfold writes at hj
      rcases hw : wr (M_mkFIFO.meth_first s.e2w).dInst with u | u
      · simp_all
      · exact ⟨u, rfl⟩
    obtain ⟨u, hw⟩ := hw
    split
    all_goals rename_i heq
    · exact nomatch heq.symm.trans hw
    · subst hrd; exact arr_get_set_self s.rf _
  · exact arr_get_set_ne _ _ _ _ hrd

-- When decode fires on a fresh instruction, every source register it uses has no in-flight writer.
theorem decode_reads (s : state) (h : (rule_RL_decode s).1 = BTrue Unit_) :
    (if ((M_mkFIFO.meth_first s.f2d).iEp == s.ep) then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ →
    ((decodeInst (M_mkFIFO.meth_first s.fromImem).data).valid_rs1 = BTrue Unit_ →
        arr_get s.sb (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs1.toNat = 0) ∧
    ((decodeInst (M_mkFIFO.meth_first s.fromImem).data).valid_rs2 = BTrue Unit_ →
        arr_get s.sb (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs2.toNat = 0) := by
  have hX := (decode_ready_iff _ _ _ _ _).mp ((bool_and_true_iff _ _).mp h).1
  simpa using hX

-- Decode's guard stays true when `sb` entries that were 0 stay 0.
theorem decode_guard_mono (s : state) (sb' : Array Nat) (h : (rule_RL_decode s).1 = BTrue Unit_)
    (hsb : ∀ r, arr_get s.sb r = 0 → arr_get sb' r = 0) :
    (rule_RL_decode { s with sb := sb' }).1 = BTrue Unit_ := by
  obtain ⟨hX, hY⟩ := (bool_and_true_iff _ _).mp h
  refine (bool_and_true_iff _ _).mpr ⟨?_, hY⟩
  have hX := (decode_ready_iff _ _ _ _ _).mp hX
  refine (decode_ready_iff _ _ _ _ _).mpr fun hF => ?_
  obtain ⟨h1, h2⟩ := hX hF
  simp only [beq_iff_eq] at h1 h2 ⊢
  exact ⟨fun hv => hsb _ (h1 hv), fun hv => hsb _ (h2 hv)⟩

-- The invariant determines `sb` from the pipeline queues.
theorem sb_eq_of_inv {s t : state} (hs : SBInv s) (ht : SBInv t) (hd : s.d2e = t.d2e) (he : s.e2w = t.e2w) :
    s.sb = t.sb := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  apply Array.ext (by rw [hs1, ht1])
  intro r h1 h2
  have e1 := hs2 r (hs1 ▸ h1)
  have e2 := ht2 r (ht1 ▸ h2)
  unfold inflight at e1 e2
  rw [hd, he, ← e2] at e1
  unfold arr_get at e1
  simpa [getElem!_pos, h1, h2] using e1

-- If decode's operand-bypass test fails, the operand really is read from `rf`, so it is valid.
theorem valid_of_bypass_false (e : Bool) (v l : t_bool) {u}
    (h : bitvec1_to_bool (bit_or (bit_or (bool_to_bitvec1 (if e = true then BTrue Unit_ else BFalse Unit_))
      (bit_not (bool_to_bitvec1 v))) (bit_not (bool_to_bitvec1 l))) = BFalse u) : v = BTrue Unit_ := by
  rcases v with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases l with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> cases e <;>
    simp (config := {decide := true}) [bitvec1_to_bool, bit_or, bit_not, bool_to_bitvec1] at h ⊢

theorem decode_d2e_rf (s : state) (rf' : Array (BitVec 32))
    (hrf : (if ((M_mkFIFO.meth_first s.f2d).iEp == s.ep) then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ →
      ((decodeInst (M_mkFIFO.meth_first s.fromImem).data).valid_rs1 = BTrue Unit_ →
          arr_get rf' (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs1.toNat =
          arr_get s.rf (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs1.toNat) ∧
      ((decodeInst (M_mkFIFO.meth_first s.fromImem).data).valid_rs2 = BTrue Unit_ →
          arr_get rf' (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs2.toNat =
          arr_get s.rf (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rs2.toNat)) :
    (rule_RL_decode { s with rf := rf' }).2.d2e = (rule_RL_decode s).2.d2e := by
  dsimp only [rule_RL_decode]
  congr
  funext u hF
  congr
  all_goals funext u' hD
  all_goals cases u
  · exact (hrf hF).1 (valid_of_bypass_false _ _ _ hD)
  · exact (hrf hF).2 (valid_of_bypass_false _ _ _ hD)

-- An instruction at the head of `e2w` does not write a register whose `sb` entry is 0.
theorem e2w_head_not_writes (s : state) (hinv : SBInv s) (hne : s.e2w.queue ≠ []) (j : Nat) (hj : j < 32)
    (h0 : arr_get s.sb j = 0) : writes j (M_mkFIFO.meth_first s.e2w).dInst = false := by
  have := hinv.2 j hj
  rw [h0] at this
  unfold inflight at this
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, ⟨_ | ⟨w, ws⟩⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  · simp only [M_mkFIFO.meth_first, List.headD_cons, List.map_cons, List.countP_cons] at this ⊢
    clear hinv h0
    by_cases hw : writes j w.dInst
    · simp only [hw, ↓reduceIte] at this; omega
    · simpa using hw

theorem decode_writeback_core (a : state) (hinv : SBInv a)
    (hc1 : (rule_RL_decode a).1 = BTrue Unit_) (hb1 : (rule_RL_writeback a).1 = BTrue Unit_) :
    (rule_RL_writeback (rule_RL_decode a).2).1 = BTrue Unit_ ∧
    (rule_RL_decode (rule_RL_writeback a).2).1 = BTrue Unit_ ∧
    (rule_RL_writeback (rule_RL_decode a).2).2 = (rule_RL_decode (rule_RL_writeback a).2).2 := by
  have g1 : (rule_RL_writeback (rule_RL_decode a).2).1 = BTrue Unit_ := hb1
  -- writeback only lowers `sb`, so zero entries stay zero and decode stays enabled
  have hsb : ∀ r, arr_get a.sb r = 0 → arr_get (rule_RL_writeback a).2.sb r = 0 := by
    intro r hr
    dsimp only [rule_RL_writeback]
    by_cases hrd : (getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd.toNat = r
    · subst hrd
      rw [arr_get_set _ _ _ _ (by rw [hinv.1]; exact rd_lt _)]
      simp [hr]
    · rw [arr_get_set_ne _ _ _ _ hrd]; exact hr
  have g2 : (rule_RL_decode (rule_RL_writeback a).2).1 = BTrue Unit_ := decode_guard_mono a _ hc1 hsb
  refine ⟨g1, g2, ?_⟩
  -- the operands decode reads are not written by writeback's instruction
  have hne := writeback_e2w_ne a hb1
  have hrf := fun hF => And.intro
    (fun hv => writeback_rf_get a _ (e2w_head_not_writes a hinv hne _ (getInstFields _).rs1.isLt
      ((decode_reads a hc1 hF).1 hv)))
    (fun hv => writeback_rf_get a _ (e2w_head_not_writes a hinv hne _ (getInstFields _).rs2.isLt
      ((decode_reads a hc1 hF).2 hv)))
  have hd2e : (rule_RL_writeback (rule_RL_decode a).2).2.d2e = (rule_RL_decode (rule_RL_writeback a).2).2.d2e :=
    (decode_d2e_rf a (rule_RL_writeback a).2.rf hrf).symm
  have he2w : (rule_RL_writeback (rule_RL_decode a).2).2.e2w = (rule_RL_decode (rule_RL_writeback a).2).2.e2w := rfl
  apply state_ext <;> try rfl
  · exact hd2e
  · exact sb_eq_of_inv (sbinv_writeback _ (sbinv_decode a hinv hc1) g1)
      (sbinv_decode _ (sbinv_writeback a hinv hb1) g2) hd2e he2w

-- ── Epoch invariant ───────────────────────────────────────────────────────
-- In program order, once an instruction carries the current epoch, all younger ones do too.
def EpOrdered (ep : BitVec 1) : List (BitVec 1) → Prop
  | [] => True
  | x :: xs => (x = ep → ∀ y ∈ xs, y = ep) ∧ EpOrdered ep xs

def epochs (s : state) : List (BitVec 1) := s.d2e.queue.map (·.iEp) ++ s.f2d.queue.map (·.iEp)

def EpInv (s : state) : Prop := EpOrdered s.ep (epochs s)

theorem EpOrdered.of_all_ne {ep : BitVec 1} : ∀ {l : List (BitVec 1)}, (∀ y ∈ l, y ≠ ep) → EpOrdered ep l
  | [], _ => trivial
  | x :: xs, h => ⟨fun hx => absurd hx (h x (by simp)), of_all_ne fun y hy => h y (by simp [hy])⟩

theorem EpOrdered.append_fresh {ep : BitVec 1} : ∀ {l : List (BitVec 1)}, EpOrdered ep l → EpOrdered ep (l ++ [ep])
  | [], _ => ⟨fun _ y hy => by simp_all, trivial⟩
  | x :: xs, ⟨h1, h2⟩ => ⟨fun hx y hy => by
      have hy : y ∈ xs ++ [ep] := hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact h1 hx y hy
      · exact hy, append_fresh h2⟩

-- Dropping any element keeps the order.
theorem EpOrdered.sublist {ep : BitVec 1} : ∀ {l l' : List (BitVec 1)}, List.Sublist l' l → EpOrdered ep l → EpOrdered ep l'
  | _, _, .slnil, h => h
  | _ :: _, _, .cons _ hs, ⟨_, h2⟩ => sublist hs h2
  | _ :: _, _ :: _, .cons₂ _ hs, ⟨h1, h2⟩ => ⟨fun hx y hy => h1 hx y (hs.subset hy), sublist hs h2⟩

theorem epinv_doFetch (s : state) (h : EpInv s) : EpInv (meth_doFetch s).avAction_ := by
  unfold EpInv epochs at *
  simp only [meth_doFetch, M_mkFIFO.meth_enq, List.map_append, List.map_cons, List.map_nil,
    ← List.append_assoc]
  exact EpOrdered.append_fresh h

theorem decode_f2d_ne (s : state) (h : (rule_RL_decode s).1 = BTrue Unit_) : s.f2d.queue ≠ [] := by
  simp only [rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff] at h
  casesm* _ ∧ _
  assumption

theorem epinv_decode (s : state) (h : EpInv s) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    EpInv (rule_RL_decode s).2 := by
  have hne := decode_f2d_ne s hg
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, ⟨_ | ⟨g, gs⟩⟩, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  unfold EpInv epochs at *
  dsimp only [rule_RL_decode]
  split
  · simpa [M_mkFIFO.meth_enq, M_mkFIFO.meth_deq, M_mkFIFO.meth_first] using h
  · simp only [M_mkFIFO.meth_deq, M_mkFIFO.meth_first, List.tail_cons] at h ⊢
    exact EpOrdered.sublist (by simp) h

-- A squashed (stale) instruction does not change the epoch.
theorem execute_ep_stale (s : state) (hne : s.d2e.queue ≠ []) (hst : (M_mkFIFO.meth_first s.d2e).iEp ≠ s.ep) :
    (rule_RL_execute s).2.ep = s.ep := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨_ | ⟨w, ws⟩⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  obtain ⟨dInst, wpc, ppc, iEp, rv1, rv2⟩ := w
  rcases bv1_cases iEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl
  all_goals first | rfl | exact absurd rfl hst

theorem epinv_execute (s : state) (h : EpInv s) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    EpInv (rule_RL_execute s).2 := by
  have hne := execute_d2e_ne s hg
  have hstale := execute_ep_stale s hne
  unfold EpInv epochs at *
  generalize hE : (rule_RL_execute s).2 = E at hstale ⊢
  have hd : E.d2e = (M_mkFIFO.meth_deq s.d2e).avAction_ := by rw [← hE]; rfl
  have hf : E.f2d = s.f2d := by rw [← hE]; rfl
  rw [hd, hf]
  obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
  have hw : M_mkFIFO.meth_first s.d2e = w := by simp [M_mkFIFO.meth_first, hq]
  rw [hw] at hstale
  simp only [M_mkFIFO.meth_deq, hq, List.tail_cons, List.map_cons, List.cons_append] at h ⊢
  obtain ⟨h1, h2⟩ := h
  by_cases hep : E.ep = s.ep
  · rw [hep]; exact h2
  · -- `ep` changed, which only happens on a redirect by a fresh instruction: everything younger is stale now
    have hfresh : w.iEp = s.ep := by
      by_contra hc; exact hep (hstale hc)
    exact EpOrdered.of_all_ne fun y hy => by rw [h1 hfresh y hy]; exact Ne.symm hep

def Fires (f : state → t_bool × state) (s s' : state) : Prop := f s = (BTrue Unit_, s')

-- Decode only sees `ep` through its value.
theorem decode_congr_ep (t : state) (e : BitVec 1) (h : t.ep = e) :
    rule_RL_decode t = rule_RL_decode { t with ep := e } := by
  subst h; rfl

-- The state after execute squashes the head of `d2e`: only `d2e` and `sb` change.
def squashed (s : state) : state :=
  { s with d2e := (M_mkFIFO.meth_deq s.d2e).avAction_, sb := (rule_RL_execute s).2.sb }

theorem execute_stale (s : state) (hne : s.d2e.queue ≠ []) (hst : (M_mkFIFO.meth_first s.d2e).iEp ≠ s.ep) :
    Fires rule_RL_execute s (squashed s) := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨_ | ⟨w, ws⟩⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  obtain ⟨dInst, wpc, ppc, iEp, rv1, rv2⟩ := w
  rcases bv1_cases iEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl
  all_goals first | rfl | exact absurd rfl hst

-- Execute can squash a `d2e` made only of stale entries until it is empty.
theorem drain : ∀ (l : List t_d2e) (s : state), s.d2e.queue = l → (∀ x ∈ l, x.iEp ≠ s.ep) → SBInv s →
    ∃ sb', Relation.ReflTransGen (Fires rule_RL_execute) s { s with d2e := ⟨[]⟩, sb := sb' } ∧
      SBInv { s with d2e := ⟨[]⟩, sb := sb' }
  | [], s, hl, _, hinv => by
    have e : { s with d2e := ⟨[]⟩, sb := s.sb } = s := by
      obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨q⟩, e2w,
        retiredInst, pc, ep, rf, sb⟩ := s
      simp only at hl; subst hl; rfl
    exact ⟨s.sb, e ▸ .refl, e ▸ hinv⟩
  | x :: l, s, hl, hst, hinv => by
    have hne : s.d2e.queue ≠ [] := by simp [hl]
    have hx : M_mkFIFO.meth_first s.d2e = x := by simp [M_mkFIFO.meth_first, hl]
    have hf := execute_stale s hne (hx ▸ hst x (by simp))
    have hinv1 : SBInv (squashed s) := by
      have := sbinv_execute s hinv (by rw [hf])
      rwa [hf] at this
    obtain ⟨sb', hsteps, hinv'⟩ :=
      drain l (squashed s) (by simp [squashed, M_mkFIFO.meth_deq, hl]) (fun y hy => hst y (by simp [hy])) hinv1
    exact ⟨sb', .head hf hsteps, hinv'⟩

-- Execute only lowers `sb`.
theorem execute_sb_zero (s : state) (hsz : s.sb.size = 32) :
    ∀ r, arr_get s.sb r = 0 → arr_get (rule_RL_execute s).2.sb r = 0 := by
  intro r hr
  dsimp only [rule_RL_execute]
  split
  · by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.d2e).dInst.inst).rd.toNat = r
    · subst hrd
      rw [arr_get_set _ _ _ _ (by rw [hsz]; exact rd_lt _)]
      simp [hr]
    · rw [arr_get_set_ne _ _ _ _ hrd]; exact hr
  · exact hr

-- A more flexible form of `decode_guard_mono`: decode's guard only reads `f2d`, `fromImem`, `ep`, `sb`.
theorem decode_guard_mono' (s t : state) (h : (rule_RL_decode s).1 = BTrue Unit_)
    (h1 : t.f2d = s.f2d) (h2 : t.fromImem = s.fromImem) (h3 : t.ep = s.ep)
    (hsb : ∀ r, arr_get s.sb r = 0 → arr_get t.sb r = 0) : (rule_RL_decode t).1 = BTrue Unit_ := by
  have := decode_guard_mono s t.sb h hsb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := s
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := t
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact this

-- Decode on a stale instruction: it fires and just drops it.
theorem decode_stale (t : state) (g : t_f2d) (gs : List t_f2d) (y : t_mem) (ys : List t_mem)
    (hf : t.f2d = ⟨g :: gs⟩) (hi : t.fromImem = ⟨y :: ys⟩) (hst : g.iEp ≠ t.ep) :
    Fires rule_RL_decode t { t with f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := t
  simp only at hf hi hst
  subst hf hi
  obtain ⟨gpc, gppc, giEp⟩ := g
  simp only at hst
  rcases bv1_cases giEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl
  all_goals first
    | exact absurd rfl hst
    | exact Prod.ext ((bool_and_true_iff _ _).mpr ⟨(decode_ready_iff _ _ _ _ _).mpr (fun hF => nomatch hF), rfl⟩) rfl

def DEStep (s s' : state) : Prop := Fires rule_RL_decode s s' ∨ Fires rule_RL_execute s s'

-- Redirect: decode-then-execute leaves the decoded instruction (now stale) in `d2e`, while
-- execute-then-decode drops it. Squashing everything left in `d2e` on both sides joins them.
theorem redirect_join (a : state) (sbD : SBInv (rule_RL_decode a).2) (sbE : SBInv (rule_RL_execute a).2)
    (e' : BitVec 1) (hE : (rule_RL_execute a).2.ep = e')
    (g : t_f2d) (gs : List t_f2d) (y : t_mem) (ys : List t_mem)
    (hf : a.f2d = ⟨g :: gs⟩) (hi : a.fromImem = ⟨y :: ys⟩) (hgst : g.iEp ≠ e')
    (hb1' : (rule_RL_execute (rule_RL_decode a).2).1 = BTrue Unit_)
    (hA2ep : (rule_RL_execute (rule_RL_decode a).2).2.ep = e')
    (hstA : ∀ x ∈ (rule_RL_execute (rule_RL_decode a).2).2.d2e.queue, x.iEp ≠ e')
    (hstB : ∀ x ∈ (rule_RL_execute a).2.d2e.queue, x.iEp ≠ e')
    (hfields : ∀ sb', { (rule_RL_execute (rule_RL_decode a).2).2 with d2e := ⟨[]⟩, sb := sb' } =
      { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩, d2e := ⟨[]⟩, sb := sb' }) :
    ∃ d, Relation.ReflTransGen DEStep (rule_RL_decode a).2 d ∧
      Relation.ReflTransGen DEStep (rule_RL_execute a).2 d := by
  -- execute-first side: decode now sees a stale instruction and drops it
  have hB : Fires rule_RL_decode (rule_RL_execute a).2
      { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } := by
    unfold Fires
    rw [decode_congr_ep _ _ hE]
    exact decode_stale _ g gs y ys hf hi hgst
  have sbB : SBInv { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } := by
    have := sbinv_decode _ sbE (by rw [hB])
    rwa [hB] at this
  -- decode-first side: execute fires on the same (fresh) head
  have hA : Fires rule_RL_execute (rule_RL_decode a).2 (rule_RL_execute (rule_RL_decode a).2).2 :=
    Prod.ext hb1' rfl
  have sbA := sbinv_execute _ sbD hb1'
  obtain ⟨sbA', stA, invA⟩ := drain _ _ rfl (by rw [hA2ep]; exact hstA) sbA
  obtain ⟨sbB', stB, invB⟩ :=
    drain _ { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } rfl hstB sbB
  rw [hfields sbA'] at stA invA
  have hsbeq : sbA' = sbB' := sb_eq_of_inv invA invB rfl rfl
  subst hsbeq
  exact ⟨_, .head (Or.inr hA) (stA.mono fun _ _ h => Or.inr h), .head (Or.inl hB) (stB.mono fun _ _ h => Or.inr h)⟩

-- Consequences of the epoch invariant when the oldest in-flight instruction is fresh.
theorem epinv_fresh (s : state) (h : EpInv s) (w : t_d2e) (ws : List t_d2e) (hd : s.d2e.queue = w :: ws)
    (hw : w.iEp = s.ep) : (∀ x ∈ ws, x.iEp = s.ep) ∧ (∀ g ∈ s.f2d.queue, g.iEp = s.ep) := by
  unfold EpInv epochs at h
  rw [hd] at h
  obtain ⟨h1, -⟩ := h
  have h1 := h1 hw
  exact ⟨fun x hx => h1 _ (by simp; exact Or.inl ⟨x, hx, rfl⟩),
    fun g hg => h1 _ (by simp; exact Or.inr ⟨g, hg, rfl⟩)⟩

theorem decode_execute_core (a : state) (hsb : SBInv a) (hep : EpInv a)
    (hc1 : (rule_RL_decode a).1 = BTrue Unit_) (hb1 : (rule_RL_execute a).1 = BTrue Unit_) :
    ∃ d, Relation.ReflTransGen DEStep (rule_RL_decode a).2 d ∧
      Relation.ReflTransGen DEStep (rule_RL_execute a).2 d := by
  have sbD := sbinv_decode a hsb hc1
  have sbE := sbinv_execute a hsb hb1
  have hnd := execute_d2e_ne a hb1
  have hnf := decode_f2d_ne a hc1
  have hni := decode_fromImem_ne a hc1
  have hszero := execute_sb_zero a hsb.1
  have hfr := epinv_fresh a hep
  clear hep
  rcases bv1_cases (rule_RL_execute a).2.ep with hE | hE
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, ⟨_ | ⟨y, ys⟩⟩, toDmem, fromDmem, ⟨_ | ⟨⟨gpc, gppc, giEp⟩, gs⟩⟩,
      ⟨_ | ⟨⟨hdInst, hpc, hppc, hiEp, hrv1, hrv2⟩, hs⟩⟩, e2w, retiredInst, pc, ep, rf, sb⟩ := a
  all_goals try (first | (simp at hni; done) | (simp at hnf; done) | (simp at hnd; done))
  all_goals
    have hfr := hfr _ _ rfl
    rcases bv1_cases hiEp with rfl | rfl <;> rcases bv1_cases giEp with rfl | rfl <;>
      rcases bv1_cases ep with rfl | rfl
  all_goals first
    -- the head of `d2e` is stale: execute squashes it, and the two orders form a diamond
    | exact ⟨_, .single (Or.inr (Prod.ext hb1 rfl)),
        .single (Or.inl (Prod.ext (decode_guard_mono' _ _ hc1 rfl rfl rfl hszero)
          (state_ext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            (sb_eq_of_inv (sbinv_decode _ sbE (decode_guard_mono' _ _ hc1 rfl rfl rfl hszero))
              (sbinv_execute _ sbD hb1) rfl rfl))))⟩
    -- fresh `d2e` head but stale `f2d` head: impossible by the epoch invariant
    | (have := (hfr rfl).2 _ (List.mem_cons_self ..); simp at this; done)
    -- fresh, no redirect: decode sees the same epoch either way
    | (refine ⟨_, .single (Or.inr (Prod.ext hb1 rfl)), .single (Or.inl ?_)⟩
       unfold Fires
       rw [decode_congr_ep _ _ hE]
       exact Prod.ext hc1 (state_ext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hE.symm rfl rfl))
    -- fresh, redirect: drain the now-stale `d2e` on both sides
    | exact redirect_join _ sbD sbE _ hE _ _ _ _ rfl rfl (by simp) hb1 hE
        (by
          intro x hx
          rcases List.mem_append.mp (show x ∈ hs ++ [_] from hx) with hx | hx
          · rw [(hfr rfl).1 x hx]; simp
          · rw [List.mem_singleton.mp hx]; simp [M_mkFIFO.meth_first])
        (by
          intro x hx
          rw [(hfr rfl).1 x hx]; simp)
        (fun _ => by apply state_ext <;> first | rfl | exact hE)

-- ── The invariants hold in every reachable state ──────────────────────────
theorem inv_init (s : ImplModule.State) (h : ImplModule.init s) : SBInv s ∧ EpInv s := by
  obtain ⟨-, -, -, -, -, -, hf, hd, he, -, hsb, -, -, -⟩ := h
  refine ⟨⟨by rw [hsb]; simp, fun r hr => ?_⟩, ?_⟩
  · simp [inflight, hd, he, hsb, arr_get, hr]
  · simp [EpInv, epochs, hf, hd, EpOrdered]

theorem inv_step (s s' : ImplModule.State) (h : SBInv s ∧ EpInv s) (hs : ImplModule.atrans s s') :
    SBInv s' ∧ EpInv s' := by
  rcases hs with ⟨r, hr⟩ | ⟨⟨name, fp⟩, he⟩
  · cases r <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
      obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
    all_goals first
      | exact h
      | exact ⟨sbinv_decode _ h.1 hg, epinv_decode _ h.2 hg⟩
      | exact ⟨sbinv_execute _ h.1 hg, epinv_execute _ h.2 hg⟩
      | exact ⟨sbinv_writeback _ h.1 hg, h.2⟩
  · cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0] at he <;>
      obtain ⟨v, hv, -, -⟩ := he
    · have : s' = (meth_doFetch s).avAction_ := by rw [hv]
      subst this
      exact ⟨h.1, epinv_doFetch _ h.2⟩
    · have : s' = (meth_getCommitInst s).avAction_ := by rw [hv]
      subst this
      exact h

theorem reachable_inv (s : ImplModule.State) (h : ImplModule.reachable s) : SBInv s ∧ EpInv s := by
  obtain ⟨s0, h0, hst⟩ := h
  induction hst with
  | refl => exact inv_init _ h0
  | tail _ hstep ih => exact inv_step _ _ ih hstep

theorem DEStep.toARule {s s' : ImplModule.State} (h : DEStep s s') : ImplModule.getARule s s' :=
  h.elim (fun h => ⟨.RL_decode, h⟩) (fun h => ⟨.RL_execute, h⟩)

-- ── Termination of the rules ──────────────────────────────────────────────
-- Every rule consumes an item from a queue and produces less weight downstream.
def weight (s : state) : Nat :=
  20 * s.toImem.queue.length + 9 * s.ireq.queue.length + 9 * s.iMem.readResult.length +
  17 * s.fromImem.queue.length + 16 * s.d2e.queue.length + 5 * s.e2w.queue.length +
  10 * s.toDmem.queue.length + 4 * s.dreq.queue.length + 4 * s.dMem.readResult.length +
  7 * s.fromDmem.queue.length

theorem strongly_normalising_of_weight {A} (r : A → A → Prop) (μ : A → Nat)
    (h : ∀ a b, r a b → μ b < μ a) : ∀ a, ReachingStar.strongly_normalising' r a := by
  intro a
  induction hn : μ a using Nat.strong_induction_on generalizing a with
  | _ n ih => exact .step fun b hb => ih _ (hn ▸ h a b hb) b rfl

@[simp] theorem deq_length [Inhabited α] (q : M_mkFIFO.state α) :
    (M_mkFIFO.meth_deq q).avAction_.queue.length = q.queue.length - 1 := by
  simp [M_mkFIFO.meth_deq]

@[simp] theorem enq_length [Inhabited α] (q : M_mkFIFO.state α) (x : α) :
    (M_mkFIFO.meth_enq q x).avAction_.queue.length = q.queue.length + 1 := by
  simp [M_mkFIFO.meth_enq]

theorem decode_d2e_le (s : state) : (rule_RL_decode s).2.d2e.queue.length ≤ s.d2e.queue.length + 1 := by
  dsimp only [rule_RL_decode]; split <;> simp

theorem execute_e2w_le (s : state) : (rule_RL_execute s).2.e2w.queue.length ≤ s.e2w.queue.length + 1 := by
  dsimp only [rule_RL_execute]; split <;> simp

theorem execute_toDmem_le (s : state) :
    (rule_RL_execute s).2.toDmem.queue.length ≤ s.toDmem.queue.length + 1 := by
  dsimp only [rule_RL_execute]; split <;> (try split) <;> simp

theorem writeback_fromDmem_le (s : state) :
    (rule_RL_writeback s).2.fromDmem.queue.length ≤ s.fromDmem.queue.length := by
  dsimp only [rule_RL_writeback]; split <;> simp

theorem weight_RL_decode (s : state) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    weight (rule_RL_decode s).2 < weight s := by
  have hne := decode_fromImem_ne s hg
  have h1 := decode_d2e_le s
  have h2 : (rule_RL_decode s).2.fromImem = (M_mkFIFO.meth_deq s.fromImem).avAction_ := rfl
  unfold weight
  simp only [show (rule_RL_decode s).2.toImem = s.toImem from rfl, show (rule_RL_decode s).2.ireq = s.ireq from rfl, show (rule_RL_decode s).2.iMem = s.iMem from rfl, show (rule_RL_decode s).2.e2w = s.e2w from rfl, show (rule_RL_decode s).2.toDmem = s.toDmem from rfl, show (rule_RL_decode s).2.dreq = s.dreq from rfl, show (rule_RL_decode s).2.dMem = s.dMem from rfl, show (rule_RL_decode s).2.fromDmem = s.fromDmem from rfl, h2, deq_length] at *
  have := List.length_pos_iff.mpr hne
  omega

theorem weight_RL_execute (s : state) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    weight (rule_RL_execute s).2 < weight s := by
  have hne := execute_d2e_ne s hg
  have h1 := execute_e2w_le s
  have h2 := execute_toDmem_le s
  have h3 : (rule_RL_execute s).2.d2e = (M_mkFIFO.meth_deq s.d2e).avAction_ := rfl
  unfold weight
  simp only [show (rule_RL_execute s).2.toImem = s.toImem from rfl, show (rule_RL_execute s).2.ireq = s.ireq from rfl, show (rule_RL_execute s).2.iMem = s.iMem from rfl, show (rule_RL_execute s).2.fromImem = s.fromImem from rfl, show (rule_RL_execute s).2.dreq = s.dreq from rfl, show (rule_RL_execute s).2.dMem = s.dMem from rfl, show (rule_RL_execute s).2.fromDmem = s.fromDmem from rfl, h3, deq_length] at *
  have := List.length_pos_iff.mpr hne
  omega

theorem weight_RL_writeback (s : state) (hg : (rule_RL_writeback s).1 = BTrue Unit_) :
    weight (rule_RL_writeback s).2 < weight s := by
  have hne := writeback_e2w_ne s hg
  have h1 := writeback_fromDmem_le s
  have h2 : (rule_RL_writeback s).2.e2w = (M_mkFIFO.meth_deq s.e2w).avAction_ := rfl
  unfold weight
  simp only [show (rule_RL_writeback s).2.toImem = s.toImem from rfl, show (rule_RL_writeback s).2.ireq = s.ireq from rfl, show (rule_RL_writeback s).2.iMem = s.iMem from rfl, show (rule_RL_writeback s).2.fromImem = s.fromImem from rfl, show (rule_RL_writeback s).2.d2e = s.d2e from rfl, show (rule_RL_writeback s).2.toDmem = s.toDmem from rfl, show (rule_RL_writeback s).2.dreq = s.dreq from rfl, show (rule_RL_writeback s).2.dMem = s.dMem from rfl, h2, deq_length] at *
  have := List.length_pos_iff.mpr hne
  omega

theorem weight_RL_requestI (s : state) (hg : (rule_RL_requestI s).1 = BTrue Unit_) :
    weight (rule_RL_requestI s).2 < weight s := by
  simp only [rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
    mkSimpleBRAM_RDY_read_iff] at hg
  casesm* _ ∧ _
  unfold weight
  simp only [rule_RL_requestI, deq_length, enq_length, M_mkSimpleBRAM.meth_put, M_mkSimpleBRAM.meth_read,
    List.length_append, List.length_singleton, List.length_tail]
  have := List.length_pos_iff.mpr (‹s.toImem.queue ≠ []›)
  omega

theorem weight_RL_responseI (s : state) (hg : (rule_RL_responseI s).1 = BTrue Unit_) :
    weight (rule_RL_responseI s).2 < weight s := by
  simp only [rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
    mkSimpleBRAM_RDY_read_iff] at hg
  casesm* _ ∧ _
  unfold weight
  simp only [rule_RL_responseI, deq_length, enq_length, M_mkSimpleBRAM.meth_put, M_mkSimpleBRAM.meth_read,
    List.length_append, List.length_singleton, List.length_tail]
  have := List.length_pos_iff.mpr (‹s.ireq.queue ≠ []›)
  have := List.length_pos_iff.mpr (‹s.iMem.readResult ≠ []›)
  omega

theorem weight_RL_requestD (s : state) (hg : (rule_RL_requestD s).1 = BTrue Unit_) :
    weight (rule_RL_requestD s).2 < weight s := by
  simp only [rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
    mkSimpleBRAM_RDY_read_iff] at hg
  casesm* _ ∧ _
  unfold weight
  simp only [rule_RL_requestD, deq_length, enq_length, M_mkSimpleBRAM.meth_put, M_mkSimpleBRAM.meth_read,
    List.length_append, List.length_singleton, List.length_tail]
  have := List.length_pos_iff.mpr (‹s.toDmem.queue ≠ []›)
  omega

theorem weight_RL_responseD (s : state) (hg : (rule_RL_responseD s).1 = BTrue Unit_) :
    weight (rule_RL_responseD s).2 < weight s := by
  simp only [rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
    mkSimpleBRAM_RDY_read_iff] at hg
  casesm* _ ∧ _
  unfold weight
  simp only [rule_RL_responseD, deq_length, enq_length, M_mkSimpleBRAM.meth_put, M_mkSimpleBRAM.meth_read,
    List.length_append, List.length_singleton, List.length_tail]
  have := List.length_pos_iff.mpr (‹s.dreq.queue ≠ []›)
  have := List.length_pos_iff.mpr (‹s.dMem.readResult ≠ []›)
  omega

-- ── Fetch pipeline ───────────────────────────────────────────────────────
-- Every fetch in flight has one entry in `f2d` and one request/response somewhere in the I-side
-- queues; fetch requests never write memory.
def FetchInv (s : state) : Prop :=
  s.f2d.queue.length = s.toImem.queue.length + s.ireq.queue.length + s.fromImem.queue.length ∧
  s.iMem.readResult.length = s.ireq.queue.length ∧
  ∀ x ∈ s.toImem.queue, x.byte_en = 0

theorem fetchinv_doFetch (s : state) (h : FetchInv s) : FetchInv (meth_doFetch s).avAction_ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [meth_doFetch, M_mkFIFO.meth_enq] at * <;> try omega
  intro x hx; rcases hx with hx | rfl
  · exact h3 x hx
  · rfl

theorem fetchinv_requestI (s : state) (h : FetchInv s) (hg : (rule_RL_requestI s).1 = BTrue Unit_) :
    FetchInv (rule_RL_requestI s).2 := by
  simp only [rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hg
  obtain ⟨h1, h2, h3⟩ := h
  have := List.length_pos_iff.mpr hg.2.1
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rule_RL_requestI, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq, M_mkSimpleBRAM.meth_put] at * <;> try omega
  intro x hx; exact h3 x (List.mem_of_mem_tail hx)

theorem fetchinv_responseI (s : state) (h : FetchInv s) (hg : (rule_RL_responseI s).1 = BTrue Unit_) :
    FetchInv (rule_RL_responseI s).2 := by
  simp only [rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
    mkSimpleBRAM_RDY_read_iff] at hg
  obtain ⟨h1, h2, h3⟩ := h
  casesm* _ ∧ _
  have := List.length_pos_iff.mpr ‹s.ireq.queue ≠ []›
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rule_RL_responseI, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq, M_mkSimpleBRAM.meth_read] at * <;> omega

theorem fetchinv_decode (s : state) (h : FetchInv s) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    FetchInv (rule_RL_decode s).2 := by
  have hf := decode_f2d_ne s hg
  have hi := decode_fromImem_ne s hg
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : (rule_RL_decode s).2.f2d = (M_mkFIFO.meth_deq s.f2d).avAction_ := rfl
  have e2 : (rule_RL_decode s).2.fromImem = (M_mkFIFO.meth_deq s.fromImem).avAction_ := rfl
  have e3 : (rule_RL_decode s).2.toImem = s.toImem := rfl
  have e4 : (rule_RL_decode s).2.ireq = s.ireq := rfl
  have e5 : (rule_RL_decode s).2.iMem = s.iMem := rfl
  have := List.length_pos_iff.mpr hf
  have := List.length_pos_iff.mpr hi
  refine ⟨?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, e5, deq_length] <;> first | omega | assumption

-- The state with the whole fetch pipeline emptied.
def flushF (s : state) : state :=
  { s with toImem := ⟨[]⟩, ireq := ⟨[]⟩, fromImem := ⟨[]⟩, f2d := ⟨[]⟩,
           iMem := { s.iMem with readResult := [] } }

theorem flushF_self (s : state) (hf : FetchInv s) (ht : s.toImem.queue = []) (hi : s.ireq.queue = [])
    (hm : s.fromImem.queue = []) : flushF s = s := by
  obtain ⟨h1, h2, -⟩ := hf
  obtain ⟨⟨mem, rr⟩, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  simp only [flushF]
  congr <;> simp_all

-- If every fetched instruction is stale, rules can drain the fetch pipeline without other effects.
theorem fetch_drain : ∀ (n : Nat) (s : state),
    3 * s.toImem.queue.length + 2 * s.ireq.queue.length + s.fromImem.queue.length ≤ n →
    FetchInv s → (∀ g ∈ s.f2d.queue, g.iEp ≠ s.ep) →
    Relation.ReflTransGen ImplModule.getARule s (flushF s) := by
  intro n
  induction n with
  | zero =>
    intro s hn hf hst
    rw [flushF_self s hf (by simp_all) (by simp_all) (by simp_all)]
  | succ n ih =>
    intro s hn hf hst
    rcases ht : s.toImem.queue with _ | ⟨x, xs⟩
    · rcases hi : s.ireq.queue with _ | ⟨y, ys⟩
      · rcases hm : s.fromImem.queue with _ | ⟨z, zs⟩
        · rw [flushF_self s hf ht hi hm]
        · -- a stale instruction and its response are both at the front: decode drops them
          obtain ⟨g, gs, hg⟩ : ∃ g gs, s.f2d.queue = g :: gs := by
            have := hf.1; rw [ht, hi, hm] at this
            exact List.exists_cons_of_ne_nil (by intro h; simp [h] at this)
          have hstep := decode_stale s g gs z zs (by rw [← hg]) (by rw [← hm]) (hst g (by simp [hg]))
          have hf1 : FetchInv { s with f2d := ⟨gs⟩, fromImem := ⟨zs⟩ } := by
            obtain ⟨h1, h2, h3⟩ := hf
            refine ⟨?_, h2, h3⟩; simp_all
          have := ih { s with f2d := ⟨gs⟩, fromImem := ⟨zs⟩ } (by simp_all <;> omega) hf1
            (fun g' hg' => hst g' (by simp [hg]; exact .inr hg'))
          exact .head ⟨.RL_decode, hstep⟩ this
      · -- a response is ready: `responseI` moves it to `fromImem`
        have hr : s.iMem.readResult ≠ [] := by
          have := hf.2.1; rw [hi] at this; intro h; simp [h] at this
        have hg : (rule_RL_responseI s).1 = BTrue Unit_ := by simp [rule_RL_responseI, hi, hr]
        have := ih _ (by simp [rule_RL_responseI, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq] at hn ⊢; simp [ht, hi] at hn ⊢; omega)
          (fetchinv_responseI s hf hg) hst
        exact .head ⟨.RL_responseI, Prod.ext hg rfl⟩ this
    · -- a request is waiting: `requestI` sends it to the BRAM (a fetch request never writes)
      have hg : (rule_RL_requestI s).1 = BTrue Unit_ := by simp [rule_RL_requestI, ht]
      have hx0 : x.byte_en = 0 := hf.2.2 x (by simp [ht])
      have e : flushF (rule_RL_requestI s).2 = flushF s := by
        simp [flushF, rule_RL_requestI, M_mkSimpleBRAM.meth_put, M_mkFIFO.meth_first, ht, hx0, bool_not]
      have := ih _ (by simp [rule_RL_requestI, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq] at hn ⊢; simp [ht] at hn ⊢; omega)
        (fetchinv_requestI s hf hg) hst
      rw [e] at this
      exact .head ⟨.RL_requestI, Prod.ext hg rfl⟩ this

-- Execute either keeps `ep` and `pc`, or redirects: flips `ep` and jumps to the head's `nextPC`.
theorem execute_pc_ep (t : state) (hne : t.d2e.queue ≠ []) :
    ((rule_RL_execute t).2.ep = t.ep ∧ (rule_RL_execute t).2.pc = t.pc) ∨
    ((rule_RL_execute t).2.ep ≠ t.ep ∧ (rule_RL_execute t).2.pc =
      (execControl32 (M_mkFIFO.meth_first t.d2e).dInst.inst (M_mkFIFO.meth_first t.d2e).rv1
        (M_mkFIFO.meth_first t.d2e).rv2 (getImmediate (M_mkFIFO.meth_first t.d2e).dInst)
        (M_mkFIFO.meth_first t.d2e).pc).nextPC) := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨_ | ⟨w, ws⟩⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := t
  · simp at hne
  obtain ⟨⟨legal, v1, v2, vrd, ity, inst⟩, wpc, ppc, iEp, rv1, rv2⟩ := w
  dsimp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons]
  rcases bv1_cases iEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl <;>
  rcases legal with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  all_goals (repeat' split) <;> simp_all [bool_to_bitvec1, bool_not]

-- Execute and a fetch: one-step commutation without a redirect; with a redirect, the wrong-path
-- fetch is absorbed by draining the (stale) fetch pipeline.
theorem execute_doFetch_core (s : state) (v : unit_)
    (hsb : SBInv s) (hep : EpInv s) (hf : FetchInv s)
    (hg : (rule_RL_execute s).1 = BTrue Unit_) (hfp : Footprint.arg0 v = Footprint.arg0 (meth_doFetch s).avValue_)
    (hrdy : meth_RDY_doFetch s = BTrue Unit_) :
    (∃ s₃, ImplModule.getMethod (rule_RL_execute s).2 ⟨.doFetch, Footprint.arg0 v⟩ s₃ ∧
        ImplModule.getRule .RL_execute (meth_doFetch s).avAction_ s₃) ∨
    (∃ d, Relation.ReflTransGen ImplModule.getARule (rule_RL_execute s).2 d ∧
        Relation.ReflTransGen ImplModule.getARule (meth_doFetch s).avAction_ d) := by
  have hne := execute_d2e_ne s hg
  have hne' : (meth_doFetch s).avAction_.d2e.queue ≠ [] := hne
  rcases execute_pc_ep s hne with ⟨hE, hP⟩ | ⟨hE, hP⟩
  · -- no redirect: the fetch commutes with execute in one step
    left
    refine ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg ?_⟩
    have hP' : (rule_RL_execute (meth_doFetch s).avAction_).2.pc = (meth_doFetch s).avAction_.pc := by
      rcases execute_pc_ep _ hne' with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hE h
    apply state_ext <;> try rfl
    · show (meth_doFetch s).avAction_.toImem = (meth_doFetch (rule_RL_execute s).2).avAction_.toImem
      simp only [meth_doFetch, hP]; rfl
    · show (meth_doFetch s).avAction_.f2d = (meth_doFetch (rule_RL_execute s).2).avAction_.f2d
      simp only [meth_doFetch, hP, hE]; rfl
    · rw [hP']
      show (meth_doFetch s).avAction_.pc = (meth_doFetch (rule_RL_execute s).2).avAction_.pc
      simp only [meth_doFetch, hP]
  · -- redirect: the fetch is on the wrong path; draining the fetch pipeline absorbs it
    right
    have hfresh : (M_mkFIFO.meth_first s.d2e).iEp = s.ep := by
      by_contra hc; exact hE (execute_ep_stale s hne hc)
    obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
    have hw : M_mkFIFO.meth_first s.d2e = w := by simp [M_mkFIFO.meth_first, hq]
    have hall := (epinv_fresh s hep w ws hq (hw ▸ hfresh)).2
    -- after fetching, execute still fires and redirects to the same target
    have hgB : (rule_RL_execute (meth_doFetch s).avAction_).1 = BTrue Unit_ := hg
    have hEB : (rule_RL_execute (meth_doFetch s).avAction_).2.ep = (rule_RL_execute s).2.ep := rfl
    have hPB : (rule_RL_execute (meth_doFetch s).avAction_).2.pc = (rule_RL_execute s).2.pc := by
      rcases execute_pc_ep _ hne' with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd (hEB.symm.trans h) hE
      · exact h.trans hP.symm
    -- once the (now stale) fetch pipelines are drained, the two sides agree
    have e : flushF (rule_RL_execute (meth_doFetch s).avAction_).2 = flushF (rule_RL_execute s).2 := by
      apply state_ext <;> first | rfl | exact hPB
    refine ⟨flushF (rule_RL_execute s).2, fetch_drain _ _ le_rfl hf ?_, ?_⟩
    · intro g hg'
      change g ∈ s.f2d.queue at hg'
      rw [hall g hg']; exact Ne.symm hE
    · rw [← e]
      refine .head ⟨.RL_execute, Prod.ext hgB rfl⟩ (fetch_drain _ _ le_rfl (fetchinv_doFetch s hf) ?_)
      intro g hg'
      change g ∈ (meth_doFetch s).avAction_.f2d.queue at hg'
      have : g.iEp = s.ep := by
        simp only [meth_doFetch, M_mkFIFO.meth_enq, List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hall g hg'
        · rfl
      rw [this]; exact Ne.symm hE

theorem fetchinv_init (s : ImplModule.State) (h : ImplModule.init s) : FetchInv s := by
  obtain ⟨hi, -, ht, hm, -, -, hf, -, -, -, -, -, hr, -⟩ := h
  simp [FetchInv, hi, ht, hm, hf, hr]

theorem fetchinv_step (s s' : ImplModule.State) (h : FetchInv s) (hs : ImplModule.atrans s s') :
    FetchInv s' := by
  rcases hs with ⟨r, hr⟩ | ⟨⟨name, fp⟩, he⟩
  · cases r <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
      obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
    all_goals first
      | exact h
      | exact fetchinv_requestI _ h hg
      | exact fetchinv_responseI _ h hg
      | exact fetchinv_decode _ h hg
  · cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0] at he <;>
      obtain ⟨v, hv, -, -⟩ := he
    · have : s' = (meth_doFetch s).avAction_ := by rw [hv]
      subst this
      exact fetchinv_doFetch _ h
    · have : s' = (meth_getCommitInst s).avAction_ := by rw [hv]
      subst this
      exact h

theorem fetchinv_reachable (s : ImplModule.State) (h : ImplModule.reachable s) : FetchInv s := by
  obtain ⟨s0, h0, hst⟩ := h
  induction hst with
  | refl => exact fetchinv_init _ h0
  | tail _ hstep ih => exact fetchinv_step _ _ ih hstep

end Invariants

@[local grind →] theorem commutes_RL_requestI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_requestI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := ireq <;> obtain ⟨memory, _ | ⟨r, rs⟩⟩ := iMem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, .single ⟨.RL_responseD, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, .single ⟨.RL_decode, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, .single ⟨.RL_execute, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, .single ⟨.RL_writeback, ?_⟩, .single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := ireq <;> obtain ⟨memory, _ | ⟨r, rs⟩⟩ := iMem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_responseI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, .single ⟨.RL_responseD, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, .single ⟨.RL_decode, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := fromImem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, .single ⟨.RL_execute, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, .single ⟨.RL_writeback, ?_⟩, .single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_requestD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, .single ⟨.RL_responseD, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := dreq <;> obtain ⟨memory, _ | ⟨r, rs⟩⟩ := dMem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, .single ⟨.RL_decode, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_requestD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, .single ⟨.RL_execute, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := toDmem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip
  -- remaining: guard of the consumer after the producer, and the final states
  all_goals
    clear hc hb
    first
      | (apply state_ext <;> clear hc1 hb1 <;>
          first
            | rfl
            | (dsimp only [M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_execute]
               (repeat' split) <;> simp_all [M_mkFIFO.meth_first, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq]))
      | (clear hc1 hb1
         simp only [M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff]
         (repeat' split) <;> simp_all)

@[local grind →] theorem commutes_RL_requestD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, .single ⟨.RL_writeback, ?_⟩, .single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := dreq <;> obtain ⟨memory, _ | ⟨r, rs⟩⟩ := dMem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           mkSimpleBRAM_RDY_read_iff, ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_responseD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, .single ⟨.RL_decode, ?_⟩, .single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, .single ⟨.RL_execute, ?_⟩, .single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_execute, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_responseD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := responseD_writeback_core _ hc1 hb1
  exact ⟨_, .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩,
    .single ⟨.RL_responseD, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩⟩

@[local grind →] theorem commutes_RL_decode_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_decode_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := fromImem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_decode_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_decode_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, .single ⟨.RL_responseD, ?_⟩, .single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_decode_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_decode_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb
  by_cases hr : ImplModule.reachable a
  swap; · exact .inr hr
  left
  obtain ⟨hsb, hep⟩ := reachable_inv a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨d, h1, h2⟩ := decode_execute_core _ hsb hep hc1 hb1
  exact ⟨d, h1.mono fun _ _ => DEStep.toARule, h2.mono fun _ _ => DEStep.toARule⟩

@[local grind →] theorem commutes_RL_decode_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb
  by_cases hr : ImplModule.reachable a
  swap; · exact .inr hr
  left
  obtain ⟨hsb, hep⟩ := reachable_inv a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := decode_writeback_core _ hsb hc1 hb1
  exact ⟨_, .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩,
    .single ⟨.RL_decode, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩⟩

@[local grind →] theorem commutes_RL_execute_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_execute_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_execute_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := a
    obtain ⟨_ | ⟨y, ys⟩⟩ := toDmem
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip
  -- remaining: guard of the consumer after the producer, and the final states
  all_goals
    clear hc hb
    first
      | (apply state_ext <;> clear hc1 hb1 <;>
          first
            | rfl
            | (dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_requestD]
               (repeat' split) <;> simp_all [M_mkFIFO.meth_first, M_mkFIFO.meth_enq, M_mkFIFO.meth_deq]))
      | (clear hc1 hb1
         simp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff]
         (repeat' split) <;> simp_all)

@[local grind →] theorem commutes_RL_execute_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, .single ⟨.RL_responseD, ?_⟩, .single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_execute_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb
  by_cases hr : ImplModule.reachable a
  swap; · exact .inr hr
  left
  obtain ⟨hsb, hep⟩ := reachable_inv a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨d, h1, h2⟩ := decode_execute_core _ hsb hep hb1 hc1
  exact ⟨d, h2.mono fun _ _ => DEStep.toARule, h1.mono fun _ _ => DEStep.toARule⟩

@[local grind →] theorem commutes_RL_execute_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem commutes_RL_execute_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := execute_writeback_core _ hc1 hb1
  exact ⟨_, .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩,
    .single ⟨.RL_execute, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩⟩

@[local grind →] theorem commutes_RL_writeback_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, .single ⟨.RL_requestI, ?_⟩, .single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_writeback_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseI a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, .single ⟨.RL_responseI, ?_⟩, .single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_writeback_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, .single ⟨.RL_requestD, ?_⟩, .single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp only [ImplModule, Module.getRule, ofRule] at hc hb ⊢
  all_goals
    obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
    obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
    refine Prod.ext ?_ ?_
  all_goals
    first
      | exact hb1
      | exact hc1
      | rfl
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hc1; done)
      | (simp only [M_mktop_pipelined.rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
           ne_eq, eq_self_iff_true, not_true_eq_false, and_false, false_and] at hb1; done)
      | skip

@[local grind →] theorem commutes_RL_writeback_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseD a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := responseD_writeback_core _ hb1 hc1
  exact ⟨_, .single ⟨.RL_responseD, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩,
    .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩⟩

@[local grind →] theorem commutes_RL_writeback_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_decode a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb
  by_cases hr : ImplModule.reachable a
  swap; · exact .inr hr
  left
  obtain ⟨hsb, hep⟩ := reachable_inv a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := decode_writeback_core _ hsb hb1 hc1
  exact ⟨_, .single ⟨.RL_decode, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩,
    .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩⟩

@[local grind →] theorem commutes_RL_writeback_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_execute a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := execute_writeback_core _ hb1 hc1
  exact ⟨_, .single ⟨.RL_execute, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g2 hst.symm⟩,
    .single ⟨.RL_writeback, by dsimp only [ImplModule, Module.getRule, ofRule]; exact Prod.ext g1 rfl⟩⟩

@[local grind →] theorem commutes_RL_writeback_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_writeback a b →
  (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d)
  ∨
    ¬ ImplModule.reachable a := by
  intro hc hb; left
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, .refl, hbc ▸ .refl⟩

@[local grind →] theorem reconverge_RL_requestI_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_requestI s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestI s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨_ | ⟨x, xs⟩⟩ := toImem
  · first
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hg; done)
      | (simp only [M_mktop_pipelined.meth_RDY_doFetch, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hrdy; done)
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_requestI_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_requestI s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestI s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_responseI_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_responseI s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseI s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_responseI_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_responseI s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseI s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_requestD_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_requestD s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestD s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_requestD_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_requestD s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_requestD s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_responseD_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_responseD s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseD s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_responseD_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_responseD s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_responseD s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_decode_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_decode s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_decode s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨_ | ⟨x, xs⟩⟩ := f2d
  · first
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hg; done)
      | (simp only [M_mktop_pipelined.meth_RDY_doFetch, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hrdy; done)
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_decode_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_decode s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_decode s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

-- Weak commutation. Without a redirect, execute and the fetch commute in one step. When execute
-- redirects, a fetch done before it is on the wrong path: its `pc` and fetched instruction differ
-- from fetching after the redirect, and no rule sequence can reconcile that with the other side
-- taking the method as well. Instead the wrong-path fetch is absorbed: it becomes stale and is
-- drained by `RL_requestI`/`RL_responseI`/`RL_decode`, after which both sides agree without the
-- execute-first side taking the method (`execute_doFetch_core`).
theorem reconverge_RL_execute_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_execute s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  (∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_execute s'' s''')
  ∨
    (∃ d, Relation.ReflTransGen ImplModule.getARule s' d ∧ Relation.ReflTransGen ImplModule.getARule s'' d)
  ∨
    ¬ ImplModule.reachable s := by
  intro hr hm
  by_cases hreach : ImplModule.reachable s
  swap; · exact .inr (.inr hreach)
  obtain ⟨hsb, hep⟩ := reachable_inv s hreach
  have hf := fetchinv_reachable s hreach
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  rcases execute_doFetch_core s v hsb hep hf hg hfp hrdy with h | h
  · exact .inl h
  · exact .inr (.inl h)

@[local grind →] theorem reconverge_RL_execute_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_execute s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_execute s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_writeback_doFetch (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .RL_writeback s s' →
  ImplModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.doFetch, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_writeback s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

@[local grind →] theorem reconverge_RL_writeback_getCommitInst (s s' s'' : ImplModule.State) (v : t_commitinst) :
  ImplModule.getRule .RL_writeback s s' →
  ImplModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getCommitInst, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_writeback s'' s''' := by
  intro hr hm
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : s'' = (M_mktop_pipelined.meth_getCommitInst s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst s).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨_ | ⟨x, xs⟩⟩ := retiredInst
  · first
      | (simp only [M_mktop_pipelined.rule_RL_writeback, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hg; done)
      | (simp only [M_mktop_pipelined.meth_RDY_getCommitInst, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hrdy; done)
  exact ⟨_, ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule :=
  strongly_normalising_of_weight _ weight fun a b ⟨r, h⟩ => by
    cases r <;> dsimp only [ImplModule, Module.getRule, ofRule] at h <;>
      obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp h
    · exact weight_RL_requestI _ hg
    · exact weight_RL_responseI _ hg
    · exact weight_RL_requestD _ hg
    · exact weight_RL_responseD _ hg
    · exact weight_RL_decode _ hg
    · exact weight_RL_execute _ hg
    · exact weight_RL_writeback _ hg

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
  -- `RL_execute`/`doFetch` only commute weakly (`reconverge_RL_execute_doFetch`): a fetch before a
  -- redirect is absorbed rather than replayed, which this (strong) field cannot express.
  method_rule_commute := by
    intro a b c e h hm; obtain ⟨r, hr⟩ := h
    cases r
    case RL_execute => sorry
    all_goals grind
  -- The commute lemmas now carry a `¬ ImplModule.reachable a` disjunct, so they no longer
  -- give unconditional weak commutation.
  rules_commute_weakly := sorry

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mktop_pipelined_refinement

#print axioms refines

end M_mktop_pipelined.Refines
