import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Processor.Params_types
import Star.Bluespec.Processor.RVUtil
import Star.Bluespec.Lib.mkSimpleBRAM
import Star.Bluespec.Lib.mkFIFO
import Star.Bluespec.Processor.mktop_pipelined
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Lib.BackwardCheck
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
  else if combined == (0b010 : BitVec 3) then memDataShifted -- word
  -- other combinations only come from illegal instructions (which still report the value in their
  -- commit record); as in `RL_writeback`, they load 0
  else 0

-- One instruction, mirroring what the pipeline does with it (decode, execute, memory, writeback):
--   * operands read as 0 when the register is x0, unused by the instruction, or the instruction is
--     illegal (as in `RL_decode`);
--   * memories are indexed like the BRAMs: word address `(addr >> 2)[29:0]`;
--   * illegal instructions still perform their memory access and produce a commit record, but do
--     not write `rf` and fall through to `pc + 4`;
--   * the commit record's `data` is reported whenever `valid_rd` (as in `RL_writeback`), while `rf`
--     is only written for legal instructions with `rd ≠ x0`;
--   * commit records are appended, so `getCommitInst` returns them oldest first.
def stepOne (s : State) : State :=
  let pc := s.pc
  let instr := s.imem.getD (extract_bits (shift_right_logical pc 2) 29 0).toNat default
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
  let addrMem : BitVec 30 :=
    extract_bits (shift_right_logical (concat_bits (extract_bits addr0 31 2) 2 (0 : BitVec 2)) 2) 29 0
  let isUnsignedMem := extract_bit funct3 2
  let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_) byteEn (0 : BitVec 4)
  let isStore := if typeMem != (0 : BitVec 4) then BTrue Unit_ else BFalse Unit_
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm pc).nextPC
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool (ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)), size := size, offset := offset }
  let finalData : BitVec 32 :=
    ite_bsv isMemInst (processMem memBusinessVal (s.dmem.getD addrMem.toNat default)) dataCtrl
  let newDmem : Array (BitVec 32) :=
    ite_bsv (bool_and isMemInst isStore) (s.dmem.setIfInBounds addrMem.toNat dataMem) s.dmem
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
    | .doFetch => orStutter0 <| ofAVMethod0 M_mktop_pipelined.Spec.meth_doFetch M_mktop_pipelined.Spec.meth_RDY_doFecth
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.state
  methods
    | .doFetch => orStutter0 <| ofAVMethod0 M_mktop_pipelined.meth_doFetch M_mktop_pipelined.meth_RDY_doFetch
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules
    | .RL_requestI => ofRule M_mktop_pipelined.rule_RL_requestI
    | .RL_responseI => ofRule M_mktop_pipelined.rule_RL_responseI
    | .RL_requestD => ofRule M_mktop_pipelined.rule_RL_requestD
    | .RL_responseD => ofRule M_mktop_pipelined.rule_RL_responseD
    | .RL_decode => ofRule M_mktop_pipelined.rule_RL_decode
    | .RL_execute => ofRule M_mktop_pipelined.rule_RL_execute
    | .RL_writeback => ofRule M_mktop_pipelined.rule_RL_writeback

-- The abstraction relation, on *flushed* states: the pipeline is empty (every FIFO, both BRAMs'
-- pending read results, and the scoreboard), and the architectural state (`pc`, register file,
-- memories, retired-but-unread commit records) agrees with the spec. The epoch is free, and so is
-- the spec's `halted` flag, which no method observes.
def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop :=
  si.ireq.queue = [] ∧ si.dreq.queue = [] ∧ si.toImem.queue = [] ∧ si.fromImem.queue = [] ∧
  si.toDmem.queue = [] ∧ si.fromDmem.queue = [] ∧
  si.f2d.queue = [] ∧ si.d2e.queue = [] ∧ si.e2w.queue = [] ∧
  si.iMem.readResult = [] ∧ si.dMem.readResult = [] ∧
  si.sb = Array.replicate 32 0 ∧
  si.pc = ss.pc ∧ si.rf = ss.rf ∧ si.iMem.memory = ss.imem ∧ si.dMem.memory = ss.dmem ∧
  si.retiredInst.queue = ss.output

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
  cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0, orStutter0] at h
  · rcases h with ⟨v, -, rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl ⟨v, rfl, rfl⟩
    · exact .inl ⟨Unit_, rfl, rfl⟩
  · obtain ⟨v, -, rfl, -⟩ := h
    exact .inr ⟨v, rfl, rfl⟩

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : unit_), e.1 = .doFetch ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (v : t_commitinst), e.1 = .getCommitInst ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, fp⟩ := e
  cases name <;> dsimp only [SpecModule, Module.getMethod, ofAVMethod0, orStutter0] at h
  · rcases h with ⟨v, -, rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl ⟨v, rfl, rfl⟩
    · exact .inl ⟨Unit_, rfl, rfl⟩
  · obtain ⟨v, -, rfl, -⟩ := h
    exact .inr ⟨v, rfl, rfl⟩

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
-- Reachability: the configurations that break commutation are unreachable.
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

-- ── Epochs ────────────────────────────────────────────────────────────────
-- Epoch tags of the in-flight instructions, oldest first.
def epochs (s : state) : List (BitVec 1) := s.d2e.queue.map (·.iEp) ++ s.f2d.queue.map (·.iEp)

theorem decode_f2d_ne (s : state) (h : (rule_RL_decode s).1 = BTrue Unit_) : s.f2d.queue ≠ [] := by
  simp only [rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff] at h
  casesm* _ ∧ _
  assumption

-- A squashed (stale) instruction does not change the epoch.
theorem execute_ep_stale (s : state) (hne : s.d2e.queue ≠ []) (hst : (M_mkFIFO.meth_first s.d2e).iEp ≠ s.ep) :
    (rule_RL_execute s).2.ep = s.ep := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨_ | ⟨w, ws⟩⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  obtain ⟨dInst, wpc, ppc, iEp, rv1, rv2⟩ := w
  rcases bv1_cases iEp with rfl | rfl <;> rcases bv1_cases ep with rfl | rfl
  all_goals first | rfl | exact absurd rfl hst


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

-- ── Size-agnostic array facts ─────────────────────────────────────────────
theorem arr_get_oob [Inhabited α] (a : Array α) (j : Nat) (h : ¬ j < a.size) : arr_get a j = default := by
  unfold arr_get; simp [h]

theorem arr_get_set' [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    arr_get (arr_set a i v) j = if i = j ∧ i < a.size then v else arr_get a j := by
  by_cases hi : i < a.size
  · rw [arr_get_set _ _ _ _ hi]; simp [hi]
  · have : arr_set a i v = a := by
      unfold arr_set; simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hi]
    rw [this]; simp [hi]

theorem arr_ext_get (a b : Array Nat) (hs : a.size = b.size) (h : ∀ k, arr_get a k = arr_get b k) :
    a = b := by
  apply Array.ext hs
  intro k h1 h2
  have := h k
  unfold arr_get at this
  simpa [getElem!_pos, h1, h2] using this

-- An increment and a decrement of scoreboard entries commute unless the decrement would truncate.
theorem arr_add_sub_comm (a : Array Nat) (i j u v : Nat) (h : i = j → j < a.size → v ≤ arr_get a j) :
    arr_set (arr_set a i (arr_get a i + u)) j (arr_get (arr_set a i (arr_get a i + u)) j - v) =
    arr_set (arr_set a j (arr_get a j - v)) i (arr_get (arr_set a j (arr_get a j - v)) i + u) := by
  apply arr_ext_get _ _ (by simp)
  intro k
  simp only [arr_get_set', arr_set_size]
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk
    by_cases hj : j < a.size
    · have := h rfl hj; simp [hj]; omega
    · simp [hj]
  · subst hik; simp [hjk]
  · subst hjk; simp [hik]
  · simp [hik, hjk]


theorem if_bool_eq_BTrue' (p : Prop) [Decidable p] (u : unit_) :
    ((if p then BTrue Unit_ else BFalse Unit_) = BTrue u) ↔ p := by split <;> simp_all
theorem if_bool_eq_BFalse' (p : Prop) [Decidable p] (u : unit_) :
    ((if p then BTrue Unit_ else BFalse Unit_) = BFalse u) ↔ ¬ p := by split <;> simp_all

theorem bool_not_eq_BTrue_iff (x : t_bool) (u : unit_) : bool_not x = BTrue u ↔ x = BFalse Unit_ := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> cases u <;> simp [bool_not]
theorem bool_not_eq_BFalse_iff (x : t_bool) (u : unit_) : bool_not x = BFalse u ↔ x = BTrue Unit_ := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> cases u <;> simp [bool_not]

-- ── The counterexamples to commutation ────────────────────────────────────
-- Exactly the configurations in which two rules (or a rule and `doFetch`) fail to commute.

/-- decode ∥ writeback: writeback's instruction writes a register whose scoreboard entry is 0
(decode may read it, and `(s+1)-1 ≠ (s-1)+1` at `s = 0`). -/
def CE_wb (s : state) : Prop :=
  ∃ x xs r, s.e2w.queue = x :: xs ∧ writes r x.dInst = true ∧ arr_get s.sb r = 0

/-- decode ∥ execute on a stale head: the squashed instruction writes a register whose scoreboard
entry is 0. -/
def CE_sq (s : state) : Prop :=
  ∃ w ws r, s.d2e.queue = w :: ws ∧ w.iEp ≠ s.ep ∧ writes r w.dInst = true ∧ arr_get s.sb r = 0

/-- decode ∥ execute and doFetch ∥ execute on a fresh head: a stale record behind it, which a
redirect would revive instead of squash. -/
def CE_ep (s : state) : Prop :=
  ∃ w ws, s.d2e.queue = w :: ws ∧ w.iEp = s.ep ∧ ((∃ x ∈ ws, x.iEp ≠ s.ep) ∨ ∃ g ∈ s.f2d.queue, g.iEp ≠ s.ep)

/-- No counterexample. This conjunction is *not* inductive on its own:
* `e2w = [x, x]` both writing `r` with `sb[r] = 1`: after writeback `x` writes `r` and `sb[r] = 0`;
* `d2e = [stale, fresh, stale]`: squashing the head leaves a fresh head with a stale record behind;
* `d2e = [y, z]` both stale and writing `r` with `sb[r] = 1`: after squashing `y`, `CE_sq` holds.
Its backward closure nevertheless misses every reset state (`reachable_noce`). -/
def NoCE (s : state) : Prop := ¬ CE_wb s ∧ ¬ CE_sq s ∧ ¬ CE_ep s

-- ── Unreachability by backward closure ────────────────────────────────────
-- The counterexamples are shown unreachable mechanically (`BwdCheck`): each concrete state is
-- abstracted into a small finite state, every concrete step into an abstract transition, and the
-- backward closure of the abstract counterexamples is computed by evaluation and checked to miss
-- the abstract reset state. Two independent abstractions are used: one per register for the
-- scoreboard counterexamples (`SBA`), one for the epoch counterexample (`EpA`).

theorem writes_rd {r : Nat} {d : t_decodedinst} (h : writes r d = true) :
    (getInstFields d.inst).rd.toNat = r ∧ wr d = BTrue Unit_ := by
  unfold writes at h
  split at h
  · rename_i hw; simp only [beq_iff_eq] at h; exact ⟨h, by rw [hw]⟩
  · simp at h

theorem writes_lt {r : Nat} {d : t_decodedinst} (h : writes r d = true) : r < 32 := by
  rw [← (writes_rd h).1]; exact rd_lt _

-- ── Scoreboard updates, entry by entry ────────────────────────────────────

theorem rmw_get (a : Array Nat) (i r : Nat) (f : Nat → Nat) (hr : r < a.size) :
    arr_get (arr_set a i (f (arr_get a i))) r = if i = r then f (arr_get a r) else arr_get a r := by
  rw [arr_get_set']; by_cases h : i = r <;> simp_all

@[simp] theorem decode_sb_size (s : state) : (rule_RL_decode s).2.sb.size = s.sb.size := by
  dsimp only [rule_RL_decode]; split <;> simp
@[simp] theorem execute_sb_size (s : state) : (rule_RL_execute s).2.sb.size = s.sb.size := by
  dsimp only [rule_RL_execute]; split <;> simp
@[simp] theorem writeback_sb_size (s : state) : (rule_RL_writeback s).2.sb.size = s.sb.size := by
  dsimp only [rule_RL_writeback]; simp

theorem decode_sb_get (s : state) (r : Nat) (hr : r < s.sb.size) :
    arr_get (rule_RL_decode s).2.sb r = arr_get s.sb r +
      (if (M_mkFIFO.meth_first s.f2d).iEp = s.ep ∧
          writes r (decodeInst (M_mkFIFO.meth_first s.fromImem).data) = true then 1 else 0) := by
  dsimp only [rule_RL_decode]
  split
  · rename_i hF
    simp only [if_bool_eq_BTrue', beq_iff_eq] at hF
    rw [rmw_get _ _ _ (fun x => x + _) hr]
    by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.fromImem).data).rd.toNat = r
    · subst hrd
      simp only [if_true, hF, true_and]
      split <;> rename_i hw
      · rw [writes_of_wr_true _ hw]; simp
      · rw [writes_of_wr_false _ hw]; simp
    · simp only [hrd, if_false, hF, true_and]
      split
      · rename_i h; exact absurd (writes_rd h).1 hrd
      · rfl
  · rename_i hF
    simp only [if_bool_eq_BFalse', beq_iff_eq] at hF
    simp [hF]

theorem writeback_sb_get (s : state) (r : Nat) (hr : r < s.sb.size) :
    arr_get (rule_RL_writeback s).2.sb r = arr_get s.sb r -
      (if writes r (M_mkFIFO.meth_first s.e2w).dInst = true then 1 else 0) := by
  dsimp only [rule_RL_writeback]
  rw [rmw_get _ _ _ (fun x => x - _) hr]
  by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.e2w).dInst.inst).rd.toNat = r
  · subst hrd
    simp only [if_true]
    split <;> rename_i hw
    · rw [writes_of_wr_true _ hw]; simp
    · rw [writes_of_wr_false _ hw]; simp
  · simp only [hrd, if_false]
    split
    · rename_i h; exact absurd (writes_rd h).1 hrd
    · rfl

theorem execute_sb_get (s : state) (r : Nat) (hr : r < s.sb.size) :
    arr_get (rule_RL_execute s).2.sb r = arr_get s.sb r -
      (if (M_mkFIFO.meth_first s.d2e).iEp ≠ s.ep ∧
          writes r (M_mkFIFO.meth_first s.d2e).dInst = true then 1 else 0) := by
  dsimp only [rule_RL_execute]
  split
  · rename_i hF
    simp only [bool_not_eq_BTrue_iff, if_bool_eq_BFalse', beq_iff_eq] at hF
    rw [rmw_get _ _ _ (fun x => x - _) hr]
    by_cases hrd : (getInstFields (M_mkFIFO.meth_first s.d2e).dInst.inst).rd.toNat = r
    · subst hrd
      simp only [if_true, hF, ne_eq, not_false_eq_true, true_and]
      split <;> rename_i hw
      · rw [writes_of_wr_true _ hw]; simp
      · rw [writes_of_wr_false _ hw]; simp
    · simp only [hrd, if_false]
      split
      · rename_i h; exact absurd (writes_rd h.2).1 hrd
      · rfl
  · rename_i hF
    simp only [bool_not_eq_BFalse_iff, if_bool_eq_BTrue', beq_iff_eq] at hF
    simp [hF]

-- ── Decode keeps or drops epoch tags ─────────────────────────────────────

theorem decode_epochs (s : state) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    (rule_RL_decode s).2.ep = s.ep ∧ List.Sublist (epochs (rule_RL_decode s).2) (epochs s) := by
  have hne := decode_f2d_ne s hg
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, ⟨_ | ⟨g, gs⟩⟩, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  · simp at hne
  unfold epochs
  dsimp only [rule_RL_decode]
  split <;> simp [M_mkFIFO.meth_enq, M_mkFIFO.meth_deq, M_mkFIFO.meth_first]

-- ── The abstract domains ──────────────────────────────────────────────────

inductive Sgn | neg | zero | pos
deriving DecidableEq

def sgn (v : Int) : Sgn := if v < 0 then .neg else if v = 0 then .zero else .pos

/-- What one register `r` looks like to the scoreboard counterexamples. -/
structure SBA where
  /-- `r` is inside the scoreboard. -/
  sz : Bool
  /-- `sb[r] = 0`. -/
  z : Bool
  /-- The sign of `sb[r]` minus the number of in-flight writers of `r`. -/
  d : Sgn
  /-- The head of `e2w` writes `r`. -/
  hw : Bool
  /-- The head of `d2e` is stale and writes `r`. -/
  hsq : Bool
deriving DecidableEq

namespace SBA

def univ : List SBA := Id.run do
  let mut l := []
  for sz in [false, true] do for z in [false, true] do for d in [Sgn.neg, .zero, .pos] do
    for hw in [false, true] do for hsq in [false, true] do l := ⟨sz, z, d, hw, hsq⟩ :: l
  return l

theorem mem_univ (a : SBA) : a ∈ univ := by
  obtain ⟨sz, z, d, hw, hsq⟩ := a
  cases sz <;> cases z <;> cases d <;> cases hw <;> cases hsq <;> decide

def sgnIdx : Sgn → Nat | .neg => 0 | .zero => 1 | .pos => 2

def enc (a : SBA) : Nat :=
  (((a.sz.toNat * 2 + a.z.toNat) * 3 + sgnIdx a.d) * 2 + a.hw.toNat) * 2 + a.hsq.toNat

/-- The sign of `v + 1` given the sign of `v`. -/
def up : Sgn → Sgn → Bool
  | .neg, .neg | .neg, .zero | .zero, .pos | .pos, .pos => true
  | _, _ => false

/-- Facts true of every abstracted state (not reachability facts). -/
def cons (b : SBA) : Bool :=
  (b.sz || b.z) && (!b.z || b.d != .pos) && (!(b.z && (b.hw || b.hsq)) || b.d == .neg)

/-- Removing one in-flight instruction that writes `r` iff `w`, with a matching decrement. -/
def dec1 (w : Bool) (a b : SBA) : Bool :=
  if w then (if a.z then b.z && up a.d b.d else b.d == a.d) else b.z == a.z && b.d == a.d

/-- The abstract transitions: no change; anything outside the scoreboard; decode; execute;
writeback. -/
def rel (a b : SBA) : Bool := cons b && (
  b == a || (!a.sz && !b.sz) ||
  (a.sz && b.sz && b.d == a.d && b.hw == a.hw && b.hsq == a.hsq && (b.z == a.z || !b.z)) ||
  (a.sz && b.sz && dec1 a.hsq a b) ||
  (a.sz && b.sz && b.hsq == a.hsq && dec1 a.hw a b))

/-- `CE_wb` or `CE_sq` at `r`. -/
def bad (a : SBA) : Bool := a.z && (a.hw || a.hsq)

def init : SBA := ⟨true, true, .zero, false, false⟩

/-- The backward closure of `bad`, computed. -/
def C : Nat := BwdCheck.closure univ enc rel 100 (BwdCheck.mask univ enc bad)

theorem closed : BwdCheck.isClosed univ enc rel C = true := by decide +kernel
theorem covers_bad : BwdCheck.covers univ enc bad C = true := by decide +kernel
theorem init_out : C.testBit (enc init) = false := by decide +kernel

theorem cons_of (b : SBA) (x i : Nat) (hz : b.z = decide (x = 0)) (hd : b.d = sgn ((x : Int) - i))
    (hsz : b.sz = false → x = 0) (hw : b.hw = true → 1 ≤ i) (hq : b.hsq = true → 1 ≤ i) :
    b.cons = true := by
  obtain ⟨sz, z, d, w, q⟩ := b
  simp only at hz hd hsz hw hq
  subst hz hd
  unfold cons sgn
  by_cases hx : x = 0
  · subst hx
    have : (((0 : Nat) : Int) - i < 0) ∨ i = 0 := by omega
    cases w <;> cases q <;> rcases this with h | h <;> simp_all
  · cases sz <;> simp_all

theorem rel_refl (b : SBA) (hb : b.cons = true) : rel b b = true := by simp [rel, hb]

theorem rel_oob (a b : SBA) (hb : b.cons = true) (ha : a.sz = false) (hb' : b.sz = false) :
    rel a b = true := by simp [rel, hb, ha, hb']

theorem rel_decode (a b : SBA) (hb : b.cons = true) (ha : a.sz = true) (hb' : b.sz = true)
    (hd : b.d = a.d) (hw : b.hw = a.hw) (hsq : b.hsq = a.hsq) (hz : b.z = a.z ∨ b.z = false) :
    rel a b = true := by
  rcases hz with hz | hz <;> simp [rel, hb, ha, hb', hd, hw, hsq, hz]

theorem rel_execute (a b : SBA) (hb : b.cons = true) (ha : a.sz = true) (hb' : b.sz = true)
    (h : dec1 a.hsq a b = true) : rel a b = true := by simp [rel, hb, ha, hb', h]

theorem rel_writeback (a b : SBA) (hb : b.cons = true) (ha : a.sz = true) (hb' : b.sz = true)
    (hsq : b.hsq = a.hsq) (h : dec1 a.hw a b = true) : rel a b = true := by
  simp [rel, hb, ha, hb', hsq, h]

theorem sgn_neg {v : Int} (h : v < 0) : sgn v = .neg := by simp [sgn, h]

theorem up_neg_sgn {v : Int} (h : v ≤ 0) : up .neg (sgn v) = true := by
  unfold sgn
  by_cases h1 : v < 0
  · simp [h1, up]
  · simp [show v = 0 by omega, up]

/-- `dec1` holds when an in-flight writer (if `w`) leaves and the scoreboard entry is decremented. -/
theorem dec1_of (w : Bool) (a b : SBA) (x i x' i' : Nat) (hx : x' = x - w.toNat) (hi : i' + w.toNat = i)
    (haz : a.z = decide (x = 0)) (had : a.d = sgn (x - i))
    (hbz : b.z = decide (x' = 0)) (hbd : b.d = sgn (x' - i')) : dec1 w a b = true := by
  cases w
  · simp only [Bool.toNat_false, Nat.sub_zero, Nat.add_zero] at hx hi
    subst hx hi
    simp [dec1, haz, had, hbz, hbd]
  · simp only [Bool.toNat_true] at hx hi
    subst hx hi
    by_cases h0 : x = 0
    · subst h0
      simp only [dec1, haz, had, hbz, hbd, decide_true, if_true, Nat.zero_sub, Bool.true_and]
      rw [sgn_neg (by omega)]
      exact up_neg_sgn (by omega)
    · simp only [dec1, haz, had, hbz, hbd, h0, decide_false, Bool.false_eq_true, if_false, if_true]
      rw [show ((x - 1 : Nat) : Int) - i' = x - (i' + 1 : Nat) by omega]
      simp

end SBA

/-- What the epoch counterexample sees: the in-flight epoch tags, `true` for fresh and `false` for
stale, abstracted to the head of `d2e` and which tags and ordered pairs of tags occur. -/
structure EpA where
  dh : Option Bool
  oF : Bool
  oS : Bool
  pFF : Bool
  pFS : Bool
  pSF : Bool
  pSS : Bool
deriving DecidableEq

namespace EpA

def univ : List EpA := Id.run do
  let mut l := []
  for dh in [none, some false, some true] do for oF in [false, true] do for oS in [false, true] do
    for pFF in [false, true] do for pFS in [false, true] do for pSF in [false, true] do
      for pSS in [false, true] do l := ⟨dh, oF, oS, pFF, pFS, pSF, pSS⟩ :: l
  return l

theorem mem_univ (a : EpA) : a ∈ univ := by
  obtain ⟨dh, oF, oS, pFF, pFS, pSF, pSS⟩ := a
  rcases dh with _ | _ | _ <;> cases oF <;> cases oS <;> cases pFF <;> cases pFS <;> cases pSF <;>
    cases pSS <;> decide

def dhIdx : Option Bool → Nat | none => 0 | some false => 1 | some true => 2

def enc (a : EpA) : Nat :=
  ((((((dhIdx a.dh * 2 + a.oF.toNat) * 2 + a.oS.toNat) * 2 + a.pFF.toNat) * 2 + a.pFS.toNat) * 2
    + a.pSF.toNat) * 2 + a.pSS.toNat)

def occ (a : EpA) : Bool → Bool | true => a.oF | false => a.oS

def pair (a : EpA) : Bool → Bool → Bool
  | true, true => a.pFF | true, false => a.pFS | false, true => a.pSF | false, false => a.pSS

/-- Facts true of every abstracted state: the head occurs and precedes every other tag; a pair's
tags occur. -/
def cons (b : EpA) : Bool :=
  (match b.dh with
    | none => true
    | some x => b.occ x && (!b.occ (!x) || b.pair x (!x))) &&
  [true, false].all fun x => [true, false].all fun y => !b.pair x y || (b.occ x && b.occ y)

/-- Every tag and pair of `b` occurs in `a`. -/
def sub (a b : EpA) : Bool :=
  [true, false].all fun x => (!b.occ x || a.occ x) &&
    [true, false].all fun y => !b.pair x y || a.pair x y

/-- Every tag and pair of `b` occurs, flipped, in `a`. -/
def subFlip (a b : EpA) : Bool :=
  [true, false].all fun x => (!b.occ x || a.occ (!x)) &&
    [true, false].all fun y => !b.pair x y || a.pair (!x) (!y)

/-- Append a fresh tag. -/
def fetch (a : EpA) : EpA := { a with oF := true, pFF := a.pFF || a.oF, pSF := a.pSF || a.oS }

/-- The abstract transitions: `doFetch`; decode (drop a tag, maybe start `d2e`); execute (drop the
head); execute with a redirect (drop a fresh head, flip every tag). -/
def rel (a b : EpA) : Bool := cons b && (
  (sub (fetch a) b && b.dh == a.dh) ||
  (sub a b && (b.dh == a.dh || (a.dh == none && b.dh == some true))) ||
  (a.dh != none && sub a b) ||
  (a.dh == some true && subFlip a b))

/-- `CE_ep`. -/
def bad (a : EpA) : Bool := a.dh == some true && a.pFS

def init : EpA := ⟨none, false, false, false, false, false, false⟩

def C : Nat := BwdCheck.closure univ enc rel 100 (BwdCheck.mask univ enc bad)

theorem closed : BwdCheck.isClosed univ enc rel C = true := by decide +kernel
theorem covers_bad : BwdCheck.covers univ enc bad C = true := by decide +kernel
theorem init_out : C.testBit (enc init) = false := by decide +kernel

theorem sub_of (a b : EpA) (h1 : ∀ x, b.occ x = true → a.occ x = true)
    (h2 : ∀ x y, b.pair x y = true → a.pair x y = true) : sub a b = true := by
  simp only [sub, List.all_eq_true, Bool.and_eq_true]
  intro x _
  refine ⟨?_, fun y _ => ?_⟩
  · cases h : b.occ x <;> simp [h, h1 x]
  · cases h : b.pair x y <;> simp [h, h2 x y]

theorem subFlip_of (a b : EpA) (h1 : ∀ x, b.occ x = true → a.occ (!x) = true)
    (h2 : ∀ x y, b.pair x y = true → a.pair (!x) (!y) = true) : subFlip a b = true := by
  simp only [subFlip, List.all_eq_true, Bool.and_eq_true]
  intro x _
  refine ⟨?_, fun y _ => ?_⟩
  · cases h : b.occ x <;> simp [h, h1 x]
  · cases h : b.pair x y <;> simp [h, h2 x y]

/-- The abstraction of a tag list with head `dh`. -/
def ofList (dh : Option Bool) (l : List Bool) : EpA :=
  ⟨dh, decide (true ∈ l), decide (false ∈ l), decide (List.Sublist [true, true] l),
    decide (List.Sublist [true, false] l), decide (List.Sublist [false, true] l),
    decide (List.Sublist [false, false] l)⟩

@[simp] theorem ofList_dh (dh : Option Bool) (l : List Bool) : (ofList dh l).dh = dh := rfl

@[simp] theorem occ_ofList (dh : Option Bool) (l : List Bool) (x : Bool) :
    (ofList dh l).occ x = decide (x ∈ l) := by cases x <;> rfl

@[simp] theorem pair_ofList (dh : Option Bool) (l : List Bool) (x y : Bool) :
    (ofList dh l).pair x y = decide (List.Sublist [x, y] l) := by cases x <;> cases y <;> rfl

theorem cons_ofList (dh : Option Bool) (l : List Bool) (h : ∀ x, dh = some x → ∃ t, l = x :: t) :
    (ofList dh l).cons = true := by
  simp only [cons, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun x _ y _ => ?_⟩
  · rcases hd : dh with _ | x
    · rfl
    · obtain ⟨t, rfl⟩ := h x hd
      simp only [ofList_dh, occ_ofList, pair_ofList, List.mem_cons, true_or, decide_true,
        Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      by_cases hx : (!x) ∈ t
      · exact .inr (.cons₂ _ (List.singleton_sublist.mpr hx))
      · left; simp [hx]
  · simp only [pair_ofList, occ_ofList, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.and_eq_true, decide_eq_true_eq]
    by_cases hp : List.Sublist [x, y] l
    · exact .inr ⟨hp.subset (by simp), hp.subset (by simp)⟩
    · exact .inl hp

theorem sub_ofList (dh dh' : Option Bool) (l l' : List Bool) (h : List.Sublist l' l) :
    sub (ofList dh l) (ofList dh' l') = true :=
  sub_of _ _ (fun x hx => by simp at hx ⊢; exact h.subset hx)
    (fun x y hx => by simp at hx ⊢; exact hx.trans h)

theorem subFlip_ofList (dh dh' : Option Bool) (l l' : List Bool) (h : List.Sublist l' (l.map not)) :
    subFlip (ofList dh l) (ofList dh' l') = true := by
  have hl : (l.map not).map not = l := by simp [List.map_map, Function.comp_def]
  refine subFlip_of _ _ (fun x hx => ?_) (fun x y hx => ?_)
  · simp only [occ_ofList, decide_eq_true_eq] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (h.subset hx)
    simpa using hy
  · simp only [pair_ofList, decide_eq_true_eq] at hx ⊢
    have := (hx.trans h).map not
    rwa [hl] at this

/-- A pair in `l ++ [z]` is a pair in `l` or ends at `z`. -/
theorem pair_append_single {x y z : Bool} {l : List Bool} (h : List.Sublist [x, y] (l ++ [z])) :
    List.Sublist [x, y] l ∨ (y = z ∧ x ∈ l) := by
  obtain ⟨l₁, l₂, he, h1, h2⟩ := List.sublist_append_iff.mp h
  rcases l₂ with _ | ⟨b, _ | ⟨c, l₂⟩⟩
  · simp at he; subst he; exact .inl h1
  · rcases l₁ with _ | ⟨a, _ | ⟨a', l₁⟩⟩
    · simp at he
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact .inr ⟨by simpa using h2.subset (by simp), h1.subset (by simp)⟩
    · simp at he
  · exact absurd h2.length_le (by simp)

theorem sub_fetch_ofList (dh dh' : Option Bool) (l : List Bool) :
    sub (fetch (ofList dh l)) (ofList dh' (l ++ [true])) = true := by
  refine sub_of _ _ (fun x hx => ?_) (fun x y hx => ?_)
  · cases x
    · simpa [fetch, occ, ofList] using hx
    · rfl
  · simp only [pair_ofList, decide_eq_true_eq] at hx
    rcases pair_append_single hx with hp | ⟨rfl, hx⟩
    · cases x <;> cases y <;> simp_all [fetch, pair, ofList]
    · cases x <;> simp_all [fetch, pair, ofList]

theorem rel_fetch (a b : EpA) (hb : b.cons = true) (h : sub (fetch a) b = true) (hd : b.dh = a.dh) :
    rel a b = true := by simp [rel, hb, h, hd]

theorem rel_decode (a b : EpA) (hb : b.cons = true) (h : sub a b = true)
    (hd : b.dh = a.dh ∨ (a.dh = none ∧ b.dh = some true)) : rel a b = true := by
  rcases hd with hd | ⟨ha, hd⟩
  · simp [rel, hb, h, hd]
  · simp [rel, hb, h, hd, ha]

theorem rel_execute (a b : EpA) (hb : b.cons = true) (ha : a.dh ≠ none) (h : sub a b = true) :
    rel a b = true := by simp [rel, hb, h, ha]

theorem rel_flip (a b : EpA) (hb : b.cons = true) (ha : a.dh = some true) (h : subFlip a b = true) :
    rel a b = true := by simp [rel, hb, h, ha]

end EpA

-- ── Abstracting the pipeline ──────────────────────────────────────────────

/-- The scoreboard abstraction of register `r`. -/
def absSB (r : Nat) (s : state) : SBA where
  sz := decide (r < s.sb.size)
  z := decide (arr_get s.sb r = 0)
  d := sgn (((arr_get s.sb r : Nat) : Int) - inflight s r)
  hw := (s.e2w.queue.head?.map fun x => writes r x.dInst).getD false
  hsq := (s.d2e.queue.head?.map fun w => decide (w.iEp ≠ s.ep) && writes r w.dInst).getD false

/-- Epoch tags relative to `ep`: `true` for fresh. -/
def tagsOf (ep : BitVec 1) (l : List (BitVec 1)) : List Bool := l.map fun x => decide (x = ep)

/-- The epoch abstraction. -/
def absEp (s : state) : EpA :=
  EpA.ofList (tagsOf s.ep (s.d2e.queue.map (·.iEp))).head? (tagsOf s.ep (epochs s))

theorem absSB_cons (r : Nat) (s : state) : (absSB r s).cons = true := by
  have hhw : (absSB r s).hw = true → 1 ≤ inflight s r := by
    rcases he : s.e2w.queue with _ | ⟨x, xs⟩
    · simp [absSB, he]
    · simp only [absSB, he, List.head?_cons, Option.map_some, Option.getD_some]
      intro hw; simp [inflight, he, hw]; omega
  have hhsq : (absSB r s).hsq = true → 1 ≤ inflight s r := by
    rcases hd : s.d2e.queue with _ | ⟨w, ws⟩
    · simp [absSB, hd]
    · simp only [absSB, hd, List.head?_cons, Option.map_some, Option.getD_some, Bool.and_eq_true]
      rintro ⟨-, hw⟩; simp [inflight, hd, hw]; omega
  refine SBA.cons_of _ (arr_get s.sb r) (inflight s r) rfl rfl (fun h => ?_) hhw hhsq
  exact arr_get_oob s.sb r (by simpa [absSB] using h)

theorem absSB_init (r : Nat) (hr : r < 32) (s : ImplModule.State) (h : ImplModule.init s) :
    absSB r s = SBA.init := by
  obtain ⟨-, -, -, -, -, -, -, hd, he, -, hsb, -, -, -⟩ := h
  simp [absSB, SBA.init, hsb, hd, he, inflight, arr_get, hr, sgn]

theorem absEp_cons (s : state) : (absEp s).cons = true := by
  apply EpA.cons_ofList
  intro x hx
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hx
  exact ⟨t ++ tagsOf s.ep (s.f2d.queue.map (·.iEp)), by
    rw [epochs, tagsOf, List.map_append, ← tagsOf, ht]; rfl⟩

theorem absEp_init (s : ImplModule.State) (h : ImplModule.init s) : absEp s = EpA.init := by
  obtain ⟨-, -, -, -, -, -, hf, hd, -, -, -, -, -, -⟩ := h
  simp [absEp, EpA.ofList, EpA.init, epochs, tagsOf, hd, hf]

-- ── Every step is an abstract transition ──────────────────────────────────

theorem decode_d2e (s : state) : ∃ ext : List t_d2e,
    (rule_RL_decode s).2.d2e.queue = s.d2e.queue ++ ext ∧ ∀ w ∈ ext, w.iEp = s.ep := by
  dsimp only [rule_RL_decode]
  split <;> rename_i hF <;> simp only [if_bool_eq_BTrue', if_bool_eq_BFalse', beq_iff_eq] at hF
  · exact ⟨_, rfl, by simpa using hF⟩
  · exact ⟨[], by simp, by simp⟩

theorem decode_ep (s : state) : (rule_RL_decode s).2.ep = s.ep := by
  dsimp only [rule_RL_decode]

theorem decode_e2w (s : state) : (rule_RL_decode s).2.e2w = s.e2w := by
  dsimp only [rule_RL_decode]

theorem absSB_decode (r : Nat) (s : state) :
    SBA.rel (absSB r s) (absSB r (rule_RL_decode s).2) = true := by
  have hcons := absSB_cons r (rule_RL_decode s).2
  by_cases hsz : r < s.sb.size
  swap
  · exact SBA.rel_oob _ _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz])
  have hd : (rule_RL_decode s).2.d2e.queue.map (·.dInst) = s.d2e.queue.map (·.dInst) ++
      (if (M_mkFIFO.meth_first s.f2d).iEp = s.ep then [decodeInst (M_mkFIFO.meth_first s.fromImem).data]
        else []) := by
    dsimp only [rule_RL_decode]
    split <;> rename_i hF <;> simp only [if_bool_eq_BTrue', if_bool_eq_BFalse', beq_iff_eq] at hF <;>
      simp [hF, M_mkFIFO.meth_enq]
  have hx := decode_sb_get s r hsz
  generalize hc : (if (M_mkFIFO.meth_first s.f2d).iEp = s.ep ∧
      writes r (decodeInst (M_mkFIFO.meth_first s.fromImem).data) = true then 1 else 0) = c at hx
  have hi : inflight (rule_RL_decode s).2 r = inflight s r + c := by
    unfold inflight
    rw [hd, decode_e2w, ← hc]
    by_cases hF : (M_mkFIFO.meth_first s.f2d).iEp = s.ep <;>
      by_cases hw : writes r (decodeInst (M_mkFIFO.meth_first s.fromImem).data) = true <;>
      (simp [hF, hw]; try omega)
  apply SBA.rel_decode (absSB r s) _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz])
  · simp only [absSB, hx, hi]
    rw [show ((arr_get s.sb r + c : Nat) : Int) - ((inflight s r + c : Nat) : Int) =
      ((arr_get s.sb r : Nat) : Int) - inflight s r by omega]
  · simp only [absSB, decode_e2w]
  · obtain ⟨ext, hext, hfresh⟩ := decode_d2e s
    simp only [absSB, hext, decode_ep]
    rcases s.d2e.queue with _ | ⟨w, ws⟩
    · rcases ext with _ | ⟨y, ys⟩
      · rfl
      · simp [hfresh y (by simp)]
    · simp
  · simp only [absSB, hx]
    by_cases hc0 : c = 0
    · left; simp [hc0]
    · right; simp; omega

theorem absSB_execute (r : Nat) (s : state) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    SBA.rel (absSB r s) (absSB r (rule_RL_execute s).2) = true := by
  have hcons := absSB_cons r (rule_RL_execute s).2
  by_cases hsz : r < s.sb.size
  swap
  · exact SBA.rel_oob _ _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz])
  have hne := execute_d2e_ne s hg
  obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
  have hw : M_mkFIFO.meth_first s.d2e = w := by simp [M_mkFIFO.meth_first, hq]
  have hd : (rule_RL_execute s).2.d2e.queue = ws := by
    show (M_mkFIFO.meth_deq s.d2e).avAction_.queue = ws; simp [M_mkFIFO.meth_deq, hq]
  have he : (rule_RL_execute s).2.e2w.queue.map (·.dInst) = s.e2w.queue.map (·.dInst) ++
      (if w.iEp = s.ep then [w.dInst] else []) := by
    dsimp only [rule_RL_execute]
    rw [hw]
    split <;> rename_i hF <;> simp only [bool_not_eq_BTrue_iff, bool_not_eq_BFalse_iff, if_bool_eq_BTrue',
      if_bool_eq_BFalse', beq_iff_eq] at hF <;> simp [hF, M_mkFIFO.meth_enq]
  have hx := execute_sb_get s r hsz
  rw [hw] at hx
  have hsq : (absSB r s).hsq = (decide (w.iEp ≠ s.ep) && writes r w.dInst) := by simp [absSB, hq]
  apply SBA.rel_execute (absSB r s) _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz])
  rw [hsq]
  apply SBA.dec1_of _ _ _ (arr_get s.sb r) (inflight s r) (arr_get (rule_RL_execute s).2.sb r)
    (inflight (rule_RL_execute s).2 r) _ _ rfl rfl rfl rfl
  · rw [hx]
    by_cases hF : w.iEp = s.ep <;> by_cases hwr : writes r w.dInst = true <;> simp [hF, hwr]
  · unfold inflight
    rw [hd, he, hq]
    by_cases hF : w.iEp = s.ep <;> by_cases hwr : writes r w.dInst = true <;> simp [hF, hwr] <;> omega

theorem absSB_writeback (r : Nat) (s : state) (hg : (rule_RL_writeback s).1 = BTrue Unit_) :
    SBA.rel (absSB r s) (absSB r (rule_RL_writeback s).2) = true := by
  have hcons := absSB_cons r (rule_RL_writeback s).2
  by_cases hsz : r < s.sb.size
  swap
  · exact SBA.rel_oob _ _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz])
  have hne := writeback_e2w_ne s hg
  obtain ⟨x, xs, hq⟩ := List.exists_cons_of_ne_nil hne
  have hx : M_mkFIFO.meth_first s.e2w = x := by simp [M_mkFIFO.meth_first, hq]
  have he : (rule_RL_writeback s).2.e2w.queue = xs := by
    show (M_mkFIFO.meth_deq s.e2w).avAction_.queue = xs; simp [M_mkFIFO.meth_deq, hq]
  have hsb := writeback_sb_get s r hsz
  rw [hx] at hsb
  have hhw : (absSB r s).hw = writes r x.dInst := by simp [absSB, hq]
  apply SBA.rel_writeback (absSB r s) _ hcons (by simp [absSB, hsz]) (by simp [absSB, hsz]) rfl
  rw [hhw]
  apply SBA.dec1_of _ _ _ (arr_get s.sb r) (inflight s r) (arr_get (rule_RL_writeback s).2.sb r)
    (inflight (rule_RL_writeback s).2 r) _ _ rfl rfl rfl rfl
  · rw [hsb]; by_cases hwr : writes r x.dInst = true <;> simp [hwr]
  · unfold inflight
    rw [he, hq]
    show (s.d2e.queue.map (·.dInst)).countP (writes r) + _ + _ = _
    by_cases hwr : writes r x.dInst = true <;> (simp [hwr]; try omega)

theorem absSB_step (r : Nat) (s s' : ImplModule.State) (hs : ImplModule.atrans s s') :
    SBA.rel (absSB r s) (absSB r s') = true := by
  rcases hs with ⟨rl, hr⟩ | ⟨⟨name, fp⟩, he⟩
  · cases rl <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
      obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
    all_goals first
      | exact SBA.rel_refl _ (absSB_cons _ _)
      | exact absSB_decode r s
      | exact absSB_execute r s hg
      | exact absSB_writeback r s hg
  · cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0, orStutter0] at he
    · rcases he with ⟨v, hv, -, -⟩ | ⟨-, rfl⟩
      · have : s' = (meth_doFetch s).avAction_ := by rw [hv]
        subst this
        exact SBA.rel_refl _ (absSB_cons _ _)
      · exact SBA.rel_refl _ (absSB_cons _ _)
    · obtain ⟨v, hv, -, -⟩ := he
      have : s' = (meth_getCommitInst s).avAction_ := by rw [hv]
      subst this
      exact SBA.rel_refl _ (absSB_cons _ _)

theorem tagsOf_flip {e e' : BitVec 1} (h : e' ≠ e) (l : List (BitVec 1)) :
    tagsOf e' l = (tagsOf e l).map not := by
  simp only [tagsOf, List.map_map]
  congr 1
  funext x
  simp only [Function.comp]
  rcases bv1_cases e with rfl | rfl <;> rcases bv1_cases e' with rfl | rfl <;>
    rcases bv1_cases x with rfl | rfl <;> first | exact absurd rfl h | decide

theorem absEp_doFetch (s : state) : EpA.rel (absEp s) (absEp (meth_doFetch s).avAction_) = true := by
  refine EpA.rel_fetch (absEp s) (absEp (meth_doFetch s).avAction_) (absEp_cons _) ?_ rfl
  have hE : tagsOf (meth_doFetch s).avAction_.ep (epochs (meth_doFetch s).avAction_) =
      tagsOf s.ep (epochs s) ++ [true] := by
    simp [tagsOf, epochs, meth_doFetch, M_mkFIFO.meth_enq]; rfl
  unfold absEp
  rw [hE]
  exact EpA.sub_fetch_ofList _ _ _

theorem absEp_decode (s : state) (hg : (rule_RL_decode s).1 = BTrue Unit_) :
    EpA.rel (absEp s) (absEp (rule_RL_decode s).2) = true := by
  obtain ⟨hep, hsl⟩ := decode_epochs s hg
  obtain ⟨ext, hext, hfresh⟩ := decode_d2e s
  apply EpA.rel_decode (absEp s) _ (absEp_cons _)
  · unfold absEp; rw [hep]; exact EpA.sub_ofList _ _ _ _ (hsl.map _)
  · simp only [absEp, EpA.ofList_dh, hext, hep]
    rcases s.d2e.queue with _ | ⟨w, ws⟩
    · rcases ext with _ | ⟨y, ys⟩
      · left; rfl
      · right; simp [tagsOf, hfresh y (by simp)]
    · left; simp [tagsOf]

theorem absEp_execute (s : state) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    EpA.rel (absEp s) (absEp (rule_RL_execute s).2) = true := by
  have hne := execute_d2e_ne s hg
  obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
  have hw : M_mkFIFO.meth_first s.d2e = w := by simp [M_mkFIFO.meth_first, hq]
  have hd : (rule_RL_execute s).2.d2e.queue = ws := by
    show (M_mkFIFO.meth_deq s.d2e).avAction_.queue = ws; simp [M_mkFIFO.meth_deq, hq]
  have hf : (rule_RL_execute s).2.f2d = s.f2d := rfl
  have hE : epochs (rule_RL_execute s).2 = (epochs s).tail := by simp [epochs, hd, hf, hq]
  have hdh : (absEp s).dh = some (decide (w.iEp = s.ep)) := by simp [absEp, tagsOf, hq]
  have hT : tagsOf s.ep (epochs s).tail = (tagsOf s.ep (epochs s)).tail := by
    simp [tagsOf, List.map_tail]
  by_cases hep : (rule_RL_execute s).2.ep = s.ep
  · apply EpA.rel_execute (absEp s) _ (absEp_cons _) (by simp [hdh])
    unfold absEp
    rw [hE, hep, hT]
    exact EpA.sub_ofList _ _ _ _ (List.tail_sublist _)
  · have hfresh : w.iEp = s.ep := by
      by_contra hc; exact hep (execute_ep_stale s hne (hw ▸ hc))
    apply EpA.rel_flip (absEp s) _ (absEp_cons _) (by simp [hdh, hfresh])
    unfold absEp
    rw [hE, tagsOf_flip hep (epochs s).tail, hT, List.map_tail]
    exact EpA.subFlip_ofList _ _ _ _ (List.tail_sublist _)

theorem absEp_step (s s' : ImplModule.State) (hs : ImplModule.atrans s s') :
    EpA.rel (absEp s) (absEp s') = true := by
  have hrefl := EpA.rel_decode _ _ (absEp_cons s) (EpA.sub_ofList _ _ _ _ (List.Sublist.refl _)) (.inl rfl)
  rcases hs with ⟨rl, hr⟩ | ⟨⟨name, fp⟩, he⟩
  · cases rl <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
      obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
    all_goals first
      | exact hrefl
      | exact absEp_decode s hg
      | exact absEp_execute s hg
  · cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0, orStutter0] at he
    · rcases he with ⟨v, hv, -, -⟩ | ⟨-, rfl⟩
      · have : s' = (meth_doFetch s).avAction_ := by rw [hv]
        subst this
        exact absEp_doFetch s
      · exact hrefl
    · obtain ⟨v, hv, -, -⟩ := he
      have : s' = (meth_getCommitInst s).avAction_ := by rw [hv]
      subst this
      exact hrefl

-- ── The counterexamples are unreachable ───────────────────────────────────

theorem reachable_noce (s : ImplModule.State) (h : ImplModule.reachable s) : NoCE s := by
  obtain ⟨s0, h0, hst⟩ := h
  have hsb : ∀ r < 32, SBA.bad (absSB r s) = true → False := fun r hr hb => by
    have hout := BwdCheck.unreachable (S := ImplModule.State) (absSB r) (absSB_step r)
      SBA.mem_univ SBA.closed hst (by rw [absSB_init r hr s0 h0]; exact SBA.init_out)
    rw [BwdCheck.covers_mem SBA.mem_univ SBA.covers_bad hb] at hout
    exact absurd hout (by simp)
  have hep : EpA.bad (absEp s) = true → False := fun hb => by
    have hout := BwdCheck.unreachable (S := ImplModule.State) absEp absEp_step
      EpA.mem_univ EpA.closed hst (by rw [absEp_init s0 h0]; exact EpA.init_out)
    rw [BwdCheck.covers_mem EpA.mem_univ EpA.covers_bad hb] at hout
    exact absurd hout (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, xs, r, he, hw, h0⟩
    exact hsb r (writes_lt hw) (by simp [SBA.bad, absSB, he, hw, h0])
  · rintro ⟨w, ws, r, hd, hst', hw, h0⟩
    exact hsb r (writes_lt hw) (by simp [SBA.bad, absSB, hd, hw, h0, hst'])
  · rintro ⟨w, ws, hd, hw, hx⟩
    apply hep
    simp only [EpA.bad, absEp, EpA.ofList, tagsOf, epochs, hd, hw, List.map_cons, List.head?_cons,
      decide_true, List.cons_append, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
    refine .cons₂ _ (List.singleton_sublist.mpr ?_)
    simp only [List.mem_append, List.mem_map]
    rcases hx with ⟨x, hx, hne⟩ | ⟨g, hg, hne⟩
    · exact ⟨x.iEp, .inl ⟨x, hx, rfl⟩, by simpa using hne⟩
    · exact ⟨g.iEp, .inr ⟨g, hg, rfl⟩, by simpa using hne⟩

-- ── Commutation, using only the absence of counterexamples ───────────────

theorem arr_get_oob' (a : Array Nat) (j : Nat) (h : ¬ j < a.size) : arr_get a j = 0 := arr_get_oob a j h

/-- A rule that only lowers scoreboard entries keeps zero entries zero. -/
theorem zero_stays (a b : Array Nat) (hs : b.size = a.size)
    (h : ∀ r < a.size, arr_get b r = arr_get a r - 0 ∨ arr_get b r = arr_get a r - 1) :
    ∀ r, arr_get a r = 0 → arr_get b r = 0 := by
  intro r hr
  by_cases hlt : r < a.size
  · rcases h r hlt with h | h <;> rw [h, hr]
  · exact arr_get_oob' _ _ (by omega)

theorem writeback_sb_zero (s : state) : ∀ r, arr_get s.sb r = 0 → arr_get (rule_RL_writeback s).2.sb r = 0 :=
  zero_stays _ _ (by simp) fun r hr => by rw [writeback_sb_get _ _ hr]; split <;> simp

theorem execute_sb_zero (s : state) : ∀ r, arr_get s.sb r = 0 → arr_get (rule_RL_execute s).2.sb r = 0 :=
  zero_stays _ _ (by simp) fun r hr => by rw [execute_sb_get _ _ hr]; split <;> simp

theorem not_writes_of_noce_wb (s : state) (hn : ¬ CE_wb s) (hne : s.e2w.queue ≠ []) (j : Nat)
    (h0 : arr_get s.sb j = 0) : writes j (M_mkFIFO.meth_first s.e2w).dInst = false := by
  obtain ⟨x, xs, hq⟩ := List.exists_cons_of_ne_nil hne
  have hx : M_mkFIFO.meth_first s.e2w = x := by simp [M_mkFIFO.meth_first, hq]
  rw [hx]
  by_contra hw
  exact hn ⟨x, xs, j, hq, by simpa using hw, h0⟩

theorem decode_writeback_core (a : state) (hn : ¬ CE_wb a)
    (hc1 : (rule_RL_decode a).1 = BTrue Unit_) (hb1 : (rule_RL_writeback a).1 = BTrue Unit_) :
    (rule_RL_writeback (rule_RL_decode a).2).1 = BTrue Unit_ ∧
    (rule_RL_decode (rule_RL_writeback a).2).1 = BTrue Unit_ ∧
    (rule_RL_writeback (rule_RL_decode a).2).2 = (rule_RL_decode (rule_RL_writeback a).2).2 := by
  have g1 : (rule_RL_writeback (rule_RL_decode a).2).1 = BTrue Unit_ := hb1
  have g2 : (rule_RL_decode (rule_RL_writeback a).2).1 = BTrue Unit_ :=
    decode_guard_mono a _ hc1 (writeback_sb_zero a)
  refine ⟨g1, g2, ?_⟩
  have hne := writeback_e2w_ne a hb1
  -- the operands decode reads are not written by writeback's instruction (`CE_wb`)
  have hrf := fun hF => And.intro
    (fun hv => writeback_rf_get a _ (not_writes_of_noce_wb a hn hne _ ((decode_reads a hc1 hF).1 hv)))
    (fun hv => writeback_rf_get a _ (not_writes_of_noce_wb a hn hne _ ((decode_reads a hc1 hF).2 hv)))
  have hd2e : (rule_RL_writeback (rule_RL_decode a).2).2.d2e = (rule_RL_decode (rule_RL_writeback a).2).2.d2e :=
    (decode_d2e_rf a (rule_RL_writeback a).2.rf hrf).symm
  apply state_ext <;> try rfl
  · exact hd2e
  · -- the increment and the decrement commute: no truncation (`CE_wb`)
    apply arr_ext_get _ _ (by simp)
    intro k
    by_cases hk : k < a.sb.size
    · rw [writeback_sb_get _ _ (by simpa using hk), decode_sb_get _ _ hk,
        decode_sb_get _ _ (by simpa using hk), writeback_sb_get _ _ hk]
      show _ - (if writes k (M_mkFIFO.meth_first a.e2w).dInst = true then 1 else 0) =
        (_ - (if writes k (M_mkFIFO.meth_first a.e2w).dInst = true then 1 else 0)) +
        (if (M_mkFIFO.meth_first a.f2d).iEp = a.ep ∧
          writes k (decodeInst (M_mkFIFO.meth_first a.fromImem).data) = true then 1 else 0)
      by_cases hw : writes k (M_mkFIFO.meth_first a.e2w).dInst = true
      · have : arr_get a.sb k ≠ 0 := fun h0 => by
          rw [not_writes_of_noce_wb a hn hne k h0] at hw; simp at hw
        simp only [hw, if_true]; split <;> omega
      · simp only [hw]; simp
    · rw [arr_get_oob' _ _ (by simpa using hk), arr_get_oob' _ _ (by simpa using hk)]

theorem fresh_of_noce (s : state) (h : ¬ CE_ep s) (w : t_d2e) (ws : List t_d2e) (hd : s.d2e.queue = w :: ws)
    (hw : w.iEp = s.ep) : (∀ x ∈ ws, x.iEp = s.ep) ∧ (∀ g ∈ s.f2d.queue, g.iEp = s.ep) := by
  refine ⟨fun x hx => ?_, fun g hg => ?_⟩ <;> by_contra hne
  · exact h ⟨w, ws, hd, hw, .inl ⟨x, hx, hne⟩⟩
  · exact h ⟨w, ws, hd, hw, .inr ⟨g, hg, hne⟩⟩

theorem decode_d2e_dInst (s : state) : (rule_RL_decode s).2.d2e.queue.map (·.dInst) = s.d2e.queue.map (·.dInst) ++
    (if (M_mkFIFO.meth_first s.f2d).iEp = s.ep then [decodeInst (M_mkFIFO.meth_first s.fromImem).data] else []) := by
  dsimp only [rule_RL_decode]
  split <;> rename_i hF <;> simp only [if_bool_eq_BTrue', if_bool_eq_BFalse', beq_iff_eq] at hF <;>
    simp [hF, M_mkFIFO.meth_enq]

theorem decode_d2e_head (s : state) (hne : s.d2e.queue ≠ []) :
    M_mkFIFO.meth_first (rule_RL_decode s).2.d2e = M_mkFIFO.meth_first s.d2e := by
  obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
  dsimp only [rule_RL_decode]
  split <;> simp [M_mkFIFO.meth_first, M_mkFIFO.meth_enq, hq]

/-- decode ∥ squash: the increment and the decrement commute (`CE_sq`). -/
theorem squash_sb_comm (a : state) (hsq : ¬ CE_sq a) (hne : a.d2e.queue ≠ [])
    (hst : (M_mkFIFO.meth_first a.d2e).iEp ≠ a.ep) :
    (rule_RL_decode (rule_RL_execute a).2).2.sb = (rule_RL_execute (rule_RL_decode a).2).2.sb := by
  obtain ⟨w, ws, hq⟩ := List.exists_cons_of_ne_nil hne
  have hmf : M_mkFIFO.meth_first a.d2e = w := by simp [M_mkFIFO.meth_first, hq]
  rw [hmf] at hst
  have hep : (rule_RL_execute a).2.ep = a.ep := execute_ep_stale a hne (hmf ▸ hst)
  apply arr_ext_get _ _ (by simp)
  intro k
  by_cases hk : k < a.sb.size
  · rw [decode_sb_get _ _ (by simpa using hk), execute_sb_get _ _ hk, execute_sb_get _ _ (by simpa using hk),
      decode_d2e_head _ hne, decode_sb_get _ _ hk, hep, hmf]
    simp only [show (rule_RL_execute a).2.fromImem = a.fromImem from rfl,
      show (rule_RL_execute a).2.f2d = a.f2d from rfl, show (rule_RL_decode a).2.ep = a.ep from rfl]
    by_cases hw : writes k w.dInst = true
    · have : arr_get a.sb k ≠ 0 := fun h0 => hsq ⟨w, ws, k, hq, hst, hw, h0⟩
      split_ifs <;> (simp_all; try omega)
    · split_ifs <;> simp_all
  · rw [arr_get_oob' _ _ (by simpa using hk), arr_get_oob' _ _ (by simpa using hk)]

theorem drain : ∀ (l : List t_d2e) (s : state), s.d2e.queue = l → (∀ x ∈ l, x.iEp ≠ s.ep) →
    ∃ sb', Relation.ReflTransGen (Fires rule_RL_execute) s { s with d2e := ⟨[]⟩, sb := sb' } ∧
      sb'.size = s.sb.size ∧
      ∀ k < s.sb.size, arr_get sb' k = arr_get s.sb k - (l.map (·.dInst)).countP (writes k)
  | [], s, hl, _ => by
    have e : { s with d2e := ⟨[]⟩, sb := s.sb } = s := by
      obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, ⟨q⟩, e2w,
        retiredInst, pc, ep, rf, sb⟩ := s
      simp only at hl; subst hl; rfl
    exact ⟨s.sb, e ▸ .refl, rfl, fun k _ => by simp⟩
  | x :: l, s, hl, hst => by
    have hne : s.d2e.queue ≠ [] := by simp [hl]
    have hx : M_mkFIFO.meth_first s.d2e = x := by simp [M_mkFIFO.meth_first, hl]
    have hxs : x.iEp ≠ s.ep := hst x (by simp)
    have hf := execute_stale s hne (hx ▸ hxs)
    have hsq : (squashed s).sb = (rule_RL_execute s).2.sb := rfl
    obtain ⟨sb', hsteps, hsz, hget⟩ :=
      drain l (squashed s) (by simp [squashed, M_mkFIFO.meth_deq, hl]) (fun y hy => hst y (by simp [hy]))
    refine ⟨sb', .head hf hsteps, by rw [hsz, hsq]; simp, fun k hk => ?_⟩
    rw [hget k (by rw [hsq]; simpa using hk), hsq, execute_sb_get _ _ hk, hx]
    simp only [hxs, ne_eq, not_false_eq_true, true_and, List.map_cons, List.countP_cons]
    split <;> omega

theorem redirect_join (a : state) (w : t_d2e) (ws : List t_d2e) (hd : a.d2e = ⟨w :: ws⟩) (hw : w.iEp = a.ep)
    (e' : BitVec 1) (hE : (rule_RL_execute a).2.ep = e')
    (g : t_f2d) (gs : List t_f2d) (y : t_mem) (ys : List t_mem)
    (hf : a.f2d = ⟨g :: gs⟩) (hi : a.fromImem = ⟨y :: ys⟩) (hg : g.iEp = a.ep) (hgst : g.iEp ≠ e')
    (hb1' : (rule_RL_execute (rule_RL_decode a).2).1 = BTrue Unit_)
    (hA2ep : (rule_RL_execute (rule_RL_decode a).2).2.ep = e')
    (hstA : ∀ x ∈ (rule_RL_execute (rule_RL_decode a).2).2.d2e.queue, x.iEp ≠ e')
    (hstB : ∀ x ∈ (rule_RL_execute a).2.d2e.queue, x.iEp ≠ e')
    (hfields : ∀ sb', { (rule_RL_execute (rule_RL_decode a).2).2 with d2e := ⟨[]⟩, sb := sb' } =
      { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩, d2e := ⟨[]⟩, sb := sb' }) :
    ∃ d, Relation.ReflTransGen DEStep (rule_RL_decode a).2 d ∧
      Relation.ReflTransGen DEStep (rule_RL_execute a).2 d := by
  -- decode-first side: execute fires on the same (fresh) head
  have hA : Fires rule_RL_execute (rule_RL_decode a).2 (rule_RL_execute (rule_RL_decode a).2).2 :=
    Prod.ext hb1' rfl
  obtain ⟨sbA', stA, szA, fA⟩ := drain _ _ rfl (by rw [hA2ep]; exact hstA)
  obtain ⟨sbB', stB, szB, fB⟩ :=
    drain _ { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } rfl hstB
  rw [hfields sbA'] at stA
  -- both sides end with the same scoreboard: decode's increment is undone by the extra squash
  have hsbeq : sbA' = sbB' := by
    have hmf : M_mkFIFO.meth_first a.d2e = w := by simp [M_mkFIFO.meth_first, hd]
    have hgf : M_mkFIFO.meth_first a.f2d = g := by simp [M_mkFIFO.meth_first, hf]
    have hyf : M_mkFIFO.meth_first a.fromImem = y := by simp [M_mkFIFO.meth_first, hi]
    have hDd := decode_d2e_dInst a
    rw [hgf, hyf, if_pos hg] at hDd
    have hDh := decode_d2e_head a (by simp [hd])
    rw [hmf] at hDh
    apply arr_ext_get _ _ (by simp at szA szB; rw [szA, szB])
    intro k
    by_cases hk : k < a.sb.size
    · have e1 := fA k (by simpa using hk)
      have e2 := fB k (by simpa using hk)
      rw [e1, e2]
      have hA1 : arr_get (rule_RL_execute (rule_RL_decode a).2).2.sb k = arr_get a.sb k +
          (if writes k (decodeInst y.data) = true then 1 else 0) := by
        rw [execute_sb_get _ _ (by simpa using hk), hDh, decode_sb_get _ _ hk, hgf, hyf]
        show _ - (if w.iEp ≠ a.ep ∧ _ then 1 else 0) = _
        simp [hw, hg]
      have hB1 : arr_get ({ (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ }).sb k =
          arr_get a.sb k := by
        show arr_get (rule_RL_execute a).2.sb k = _
        rw [execute_sb_get _ _ hk, hmf]; simp [hw]
      have hA2 : ((rule_RL_execute (rule_RL_decode a).2).2.d2e.queue.map (·.dInst)) =
          ws.map (·.dInst) ++ [decodeInst y.data] := by
        show ((rule_RL_decode a).2.d2e.queue.tail.map (·.dInst)) = _
        rw [List.map_tail, hDd]; simp [hd]
      have hB2 : ({ (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ }).d2e.queue = ws := by
        show a.d2e.queue.tail = ws; simp [hd]
      rw [hA1, hB1, hA2, hB2, List.countP_append]
      split <;> simp_all <;> omega
    · rw [arr_get_oob' _ _ (by simp at szA; rw [szA]; simpa using hk),
        arr_get_oob' _ _ (by simp at szB; rw [szB]; simpa using hk)]
  subst hsbeq
  -- execute-first side: decode now sees a stale instruction and drops it
  have hB : Fires rule_RL_decode (rule_RL_execute a).2
      { (rule_RL_execute a).2 with ep := e', f2d := ⟨gs⟩, fromImem := ⟨ys⟩ } := by
    unfold Fires
    rw [decode_congr_ep _ _ hE]
    exact decode_stale _ g gs y ys hf hi hgst
  exact ⟨_, .head (Or.inr hA) (stA.mono fun _ _ h => Or.inr h), .head (Or.inl hB) (stB.mono fun _ _ h => Or.inr h)⟩

theorem decode_execute_core (a : state) (hsq : ¬ CE_sq a) (hep : ¬ CE_ep a)
    (hc1 : (rule_RL_decode a).1 = BTrue Unit_) (hb1 : (rule_RL_execute a).1 = BTrue Unit_) :
    ∃ d, Relation.ReflTransGen DEStep (rule_RL_decode a).2 d ∧
      Relation.ReflTransGen DEStep (rule_RL_execute a).2 d := by
  have hnd := execute_d2e_ne a hb1
  have hnf := decode_f2d_ne a hc1
  have hni := decode_fromImem_ne a hc1
  have hszero := execute_sb_zero a
  have hsbc := squash_sb_comm a hsq hnd
  have hfr := fresh_of_noce a hep
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
            (hsbc (by simp [M_mkFIFO.meth_first])))))⟩
    -- fresh `d2e` head but stale `f2d` head: impossible by the epoch invariant
    | (have := (hfr rfl).2 _ (List.mem_cons_self ..); simp at this; done)
    -- fresh, no redirect: decode sees the same epoch either way
    | (refine ⟨_, .single (Or.inr (Prod.ext hb1 rfl)), .single (Or.inl ?_)⟩
       unfold Fires
       rw [decode_congr_ep _ _ hE]
       exact Prod.ext hc1 (state_ext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hE.symm rfl rfl))
    -- fresh, redirect: drain the now-stale `d2e` on both sides
    | exact redirect_join _ _ _ rfl rfl _ hE _ _ _ _ rfl rfl rfl (by simp) hb1 hE
        (by
          intro x hx
          rcases List.mem_append.mp (show x ∈ hs ++ [_] from hx) with hx | hx
          · rw [(hfr rfl).1 x hx]; simp
          · rw [List.mem_singleton.mp hx]; simp [M_mkFIFO.meth_first])
        (by
          intro x hx
          rw [(hfr rfl).1 x hx]; simp)
        (fun _ => by apply state_ext <;> first | rfl | exact hE)

theorem execute_doFetch_core (s : state) (v : unit_)
    (hep : ¬ CE_ep s) (hf : FetchInv s)
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
    refine ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg ?_⟩
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
    have hall := (fresh_of_noce s hep w ws hq (hw ▸ hfresh)).2
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
  · cases name <;> dsimp only [ImplModule, Module.getMethod, ofAVMethod0, orStutter0] at he
    · rcases he with ⟨v, hv, -, -⟩ | ⟨-, rfl⟩
      · have : s' = (meth_doFetch s).avAction_ := by rw [hv]
        subst this
        exact fetchinv_doFetch _ h
      · exact h
    · obtain ⟨v, hv, -, -⟩ := he
      have : s' = (meth_getCommitInst s).avAction_ := by rw [hv]
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
  obtain ⟨hwb, hsq, hep⟩ := reachable_noce a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨d, h1, h2⟩ := decode_execute_core _ hsq hep hc1 hb1
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
  obtain ⟨hwb, hsq, hep⟩ := reachable_noce a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := decode_writeback_core _ hwb hc1 hb1
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
  obtain ⟨hwb, hsq, hep⟩ := reachable_noce a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨d, h1, h2⟩ := decode_execute_core _ hsq hep hb1 hc1
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
  obtain ⟨hwb, hsq, hep⟩ := reachable_noce a hr
  dsimp only [ImplModule, Module.getRule, ofRule] at hc hb
  obtain ⟨hc1, rfl⟩ := Prod.ext_iff.mp hc
  obtain ⟨hb1, rfl⟩ := Prod.ext_iff.mp hb
  obtain ⟨g1, g2, hst⟩ := decode_writeback_core _ hwb hb1 hc1
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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨_ | ⟨x, xs⟩⟩ := toImem
  · first
      | (simp only [M_mktop_pipelined.rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hg; done)
      | (simp only [M_mktop_pipelined.meth_RDY_doFetch, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hrdy; done)
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨_ | ⟨x, xs⟩⟩ := f2d
  · first
      | (simp only [M_mktop_pipelined.rule_RL_decode, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hg; done)
      | (simp only [M_mktop_pipelined.meth_RDY_doFetch, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
          ne_eq, not_true_eq_false, and_false, false_and] at hrdy; done)
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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
  obtain ⟨-, -, hep⟩ := reachable_noce s hreach
  have hf := fetchinv_reachable s hreach
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact .inl ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  rcases execute_doFetch_core s v hep hf hg hfp hrdy with h | h
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
  dsimp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, orStutter0] at hr hm
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  rcases hm with ⟨v', hv, hfp, hrdy⟩ | ⟨-, rfl⟩
  swap; · -- stutter: replay it after the rule
    exact ⟨_, Or.inr ⟨by cases v; rfl, rfl⟩, Prod.ext hg rfl⟩
  obtain rfl : s'' = (M_mktop_pipelined.meth_doFetch s).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_doFetch s).avValue_ := (congrArg (·.avValue_) hv).symm
  exact ⟨_, Or.inl ⟨_, rfl, hfp, hrdy⟩, Prod.ext hg rfl⟩

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

-- ── One instruction through an empty pipeline ─────────────────────────────
-- From a flushed state, a real `doFetch` followed by the pipeline rules (`requestI`, `responseI`,
-- `decode`, `execute`, then `requestD`/`responseD` for a memory instruction, and `writeback`) reaches
-- a flushed state related to `stepOne` of the spec (`doFetch_run`). Each stage lemma restates what a
-- rule does to a single in-flight instruction, with the generated code's dependent `match`es turned
-- into `ite_bsv`, so that the stages compose by rewriting.
section FlushedRun
open RVUtil M_mktop_pipelined
set_option maxHeartbeats 4000000

@[local simp] theorem arr_get_replicate_zero (n k : Nat) : arr_get (Array.replicate n (0 : Nat)) k = 0 := by
  unfold arr_get; by_cases h : k < n <;> simp [h]
@[local simp] theorem unit_eq (a : unit_) : a = Unit_ := by cases a; rfl
@[local simp] theorem b2v_not (a : t_bool) : bit_not (bool_to_bitvec1 a) = bool_to_bitvec1 (bool_not a) := by
  rcases a with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> decide
@[local simp] theorem b2v_or (a b : t_bool) :
    bit_or (bool_to_bitvec1 a) (bool_to_bitvec1 b) = bool_to_bitvec1 (bool_or a b) := by
  rcases a with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> decide
@[local simp] theorem b2v_and (a b : t_bool) :
    bit_and (bool_to_bitvec1 a) (bool_to_bitvec1 b) = bool_to_bitvec1 (bool_and a b) := by
  rcases a with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> decide
@[local simp] theorem bool_and_BTrue_l (u) (x : t_bool) : bool_and (BTrue u) x = x := rfl
@[local simp] theorem bool_and_BFalse_l (u) (x : t_bool) : bool_and (BFalse u) x = BFalse Unit_ := rfl
@[local simp] theorem bool_and_BTrue_r (u) (x : t_bool) : bool_and x (BTrue u) = x := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> cases u <;> rfl
@[local simp] theorem bool_or_BTrue_l (u) (x : t_bool) : bool_or (BTrue u) x = BTrue Unit_ := rfl
@[local simp] theorem bool_or_BFalse_l (u) (x : t_bool) : bool_or (BFalse u) x = x := rfl
@[local simp] theorem bool_or_not_self (x : t_bool) : bool_or x (bool_not x) = BTrue Unit_ := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl
@[local simp] theorem bool_not_BTrue (u) : bool_not (BTrue u) = BFalse Unit_ := rfl
@[local simp] theorem bool_not_BFalse (u) : bool_not (BFalse u) = BTrue Unit_ := rfl
@[local simp] theorem ite_BTrue (u) (a b : α) : ite_bsv (BTrue u) a b = a := rfl
@[local simp] theorem ite_BFalse (u) (a b : α) : ite_bsv (BFalse u) a b = b := rfl
@[local simp] theorem if_bool_eq_BTrue (p : Prop) [Decidable p] (u) :
    ((if p then BTrue Unit_ else BFalse Unit_) = BTrue u) ↔ p := by split <;> simp_all
@[local simp] theorem if_bool_eq_BFalse (p : Prop) [Decidable p] (u) :
    ((if p then BTrue Unit_ else BFalse Unit_) = BFalse u) ↔ ¬ p := by split <;> simp_all
@[local simp] theorem BTrue_ne_BFalse (u v) : (BTrue u = BFalse v) ↔ False := by simp
@[local simp] theorem BFalse_ne_BTrue (u v) : (BFalse u = BTrue v) ↔ False := by simp

attribute [local simp] M_mkFIFO.meth_enq M_mkFIFO.meth_deq M_mkFIFO.meth_first M_mkFIFO.meth_RDY_enq
  M_mkFIFO.meth_RDY_deq M_mkFIFO.meth_RDY_first M_mkSimpleBRAM.meth_put M_mkSimpleBRAM.meth_read
  M_mkSimpleBRAM.meth_RDY_put M_mkSimpleBRAM.meth_RDY_read

def readOp (d : t_decodedinst) (r : BitVec 5) (v : t_bool) (rf : Array (BitVec 32)) : BitVec 32 :=
  ite_bsv (bool_or (bool_or (if r == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_) (bool_not v))
    (bool_not d.legal)) 0 (arr_get rf r.toNat)

def decOut (f : t_f2d) (instr : BitVec 32) (rf : Array (BitVec 32)) : t_d2e :=
  { dInst := decodeInst instr, pc := f.pc, ppc := f.ppc, iEp := f.iEp,
    rv1 := readOp (decodeInst instr) (getInstFields instr).rs1 (decodeInst instr).valid_rs1 rf,
    rv2 := readOp (decodeInst instr) (getInstFields instr).rs2 (decodeInst instr).valid_rs2 rf }

theorem decode_fresh (s : state) (f : t_f2d) (m : t_mem)
    (hf : s.f2d.queue = [f]) (hm : s.fromImem.queue = [m]) (hd : s.d2e.queue = [])
    (hep : f.iEp = s.ep) (hsb : s.sb = Array.replicate 32 0) :
    (rule_RL_decode s).1 = BTrue Unit_ ∧
    (rule_RL_decode s).2 =
      { s with
        d2e := { queue := [decOut f m.data s.rf] }
        f2d := { queue := [] }
        fromImem := { queue := [] }
        sb := arr_set s.sb (getInstFields m.data).rd.toNat (ite_bsv (wr (decodeInst m.data)) 1 0) } := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem, ⟨f2d⟩, ⟨d2e⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  obtain ⟨fromImem⟩ := fromImem
  dsimp only at hf hm hd hep hsb
  subst hf hm hd hep hsb
  have hfr : (f.iEp == f.iEp) = true := beq_self_eq_true _
  constructor
  · simp only [rule_RL_decode, M_mkFIFO.meth_first, List.headD_cons, b2v_not, b2v_or, b2v_and,
      bitvec1_roundtrip, hfr, arr_get_replicate_zero]
    split
    · repeat' split
      all_goals simp_all
    · simp_all
  · apply state_ext <;> try rfl
    · -- d2e
      simp only [rule_RL_decode, M_mkFIFO.meth_first, List.headD_cons]
      split
      · simp only [M_mkFIFO.meth_enq, List.nil_append, decOut, readOp]
        repeat' split
        all_goals simp_all
      · simp_all
    · -- sb
      simp only [rule_RL_decode, M_mkFIFO.meth_first, List.headD_cons, wr, b2v_not, b2v_or, b2v_and,
        bitvec1_roundtrip]
      split
      · split <;> rename_i h <;> simp only [b2v_not, b2v_or, b2v_and, bitvec1_roundtrip] at h <;>
          simp at h ⊢ <;> simp [h]
      · simp_all

theorem requestI_one (s : state) (q : t_mem) (hq : s.toImem.queue = [q]) (hr : s.ireq.queue = []) :
    (rule_RL_requestI s).1 = BTrue Unit_ ∧
    (rule_RL_requestI s).2 =
      { s with
        toImem := { queue := [] }
        ireq := { queue := [q] }
        iMem := (M_mkSimpleBRAM.meth_put s.iMem
          (bool_not (if q.byte_en == (0 : BitVec 4) then BTrue Unit_ else BFalse Unit_))
          (extract_bits (shift_right_logical q.addr 2) 29 0) q.data).avAction_ } := by
  obtain ⟨iMem, dMem, ⟨ireq⟩, dreq, ⟨toImem⟩, fromImem, toDmem, fromDmem, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hq hr; subst hq hr
  constructor
  · simp [rule_RL_requestI]
  · rfl

theorem responseI_one (s : state) (q : t_mem) (v : BitVec 32) (hq : s.ireq.queue = [q])
    (hv : s.iMem.readResult = [v]) (hf : s.fromImem.queue = []) :
    (rule_RL_responseI s).1 = BTrue Unit_ ∧
    (rule_RL_responseI s).2 =
      { s with
        iMem := { s.iMem with readResult := [] }
        ireq := { queue := [] }
        fromImem := { queue := [{ byte_en := q.byte_en, addr := q.addr, data := v }] } } := by
  obtain ⟨⟨imem, rr⟩, dMem, ⟨ireq⟩, dreq, toImem, ⟨fromImem⟩, toDmem, fromDmem, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hq hv hf; subst hq hv hf
  constructor
  · simp [rule_RL_responseI]
  · rfl

theorem requestD_one (s : state) (q : t_mem) (hq : s.toDmem.queue = [q]) (hr : s.dreq.queue = []) :
    (rule_RL_requestD s).1 = BTrue Unit_ ∧
    (rule_RL_requestD s).2 =
      { s with
        toDmem := { queue := [] }
        dreq := { queue := [q] }
        dMem := (M_mkSimpleBRAM.meth_put s.dMem
          (bool_not (if q.byte_en == (0 : BitVec 4) then BTrue Unit_ else BFalse Unit_))
          (extract_bits (shift_right_logical q.addr 2) 29 0) q.data).avAction_ } := by
  obtain ⟨iMem, dMem, ireq, ⟨dreq⟩, toImem, fromImem, ⟨toDmem⟩, fromDmem, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hq hr; subst hq hr
  constructor
  · simp [rule_RL_requestD]
  · rfl

theorem responseD_one (s : state) (q : t_mem) (v : BitVec 32) (hq : s.dreq.queue = [q])
    (hv : s.dMem.readResult = [v]) (hf : s.fromDmem.queue = []) :
    (rule_RL_responseD s).1 = BTrue Unit_ ∧
    (rule_RL_responseD s).2 =
      { s with
        dMem := { s.dMem with readResult := [] }
        dreq := { queue := [] }
        fromDmem := { queue := [{ byte_en := q.byte_en, addr := q.addr, data := v }] } } := by
  obtain ⟨iMem, ⟨dmem, rr⟩, ireq, ⟨dreq⟩, toImem, fromImem, toDmem, ⟨fromDmem⟩, f2d, d2e, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hq hv hf; subst hq hv hf
  constructor
  · simp [rule_RL_responseD]
  · rfl

-- ── execute on a fresh instruction ──
section Exec
variable (w : t_d2e)
def exOff : BitVec 2 := extract_bits (w.rv1 + getImmediate w.dInst) 1 0
def exByteEn : BitVec 4 :=
  ite_bsv (if extract_bits w.dInst.inst 5 5 == 1 then BTrue Unit_ else BFalse Unit_)
    (ite_bsv (if extract_bits (getInstFields w.dInst.inst).funct3 1 0 == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_)
      (shift_left (1 : BitVec 4) (exOff w))
      (ite_bsv (if extract_bits (getInstFields w.dInst.inst).funct3 1 0 == (1 : BitVec 2) then BTrue Unit_ else BFalse Unit_)
        (shift_left (3 : BitVec 4) (exOff w))
        (ite_bsv (if extract_bits (getInstFields w.dInst.inst).funct3 1 0 == (2 : BitVec 2) then BTrue Unit_ else BFalse Unit_)
          (shift_left (15 : BitVec 4) (exOff w)) default)))
    0
def exStData : BitVec 32 := shift_left w.rv2 (concat_bits (exOff w) 3 (0 : BitVec 3))
def exMem : t_mem :=
  { byte_en := exByteEn w,
    addr := concat_bits (extract_bits (w.rv1 + getImmediate w.dInst) 31 2) 2 (0 : BitVec 2),
    data := exStData w }
def exData : BitVec 32 :=
  ite_bsv (isMemoryInst w.dInst) (exStData w)
    (ite_bsv (isControlInst w.dInst) (w.pc + 4)
      (execALU32 w.dInst.inst w.rv1 w.rv2 (getImmediate w.dInst) w.pc))
def exOut : t_e2w :=
  { memBusiness :=
      { isUnsigned := bitvec1_to_bool (ite_bsv (isMemoryInst w.dInst)
          (extract_bits (getInstFields w.dInst.inst).funct3 2 2) 0),
        size := extract_bits (getInstFields w.dInst.inst).funct3 1 0,
        offset := exOff w },
    pc := w.pc, data := exData w, dInst := w.dInst }
def exNext : BitVec 32 :=
  (execControl32 w.dInst.inst w.rv1 w.rv2 (getImmediate w.dInst) w.pc).nextPC
def exPc (pc : BitVec 32) : BitVec 32 :=
  ite_bsv (isMemoryInst w.dInst) pc
    (ite_bsv w.dInst.legal
      (ite_bsv (bool_not (if exNext w == w.ppc then BTrue Unit_ else BFalse Unit_)) (exNext w) pc) pc)
end Exec

theorem execute_fresh (s : state) (w : t_d2e) (hd : s.d2e.queue = [w]) (hep : w.iEp = s.ep)
    (ht : s.toDmem.queue = []) (he : s.e2w.queue = []) :
    (rule_RL_execute s).1 = BTrue Unit_ ∧
    (rule_RL_execute s).2 =
      { s with
        d2e := { queue := [] }
        toDmem := { queue := ite_bsv (isMemoryInst w.dInst) [exMem w] [] }
        pc := exPc w s.pc
        ep := (rule_RL_execute s).2.ep
        e2w := { queue := [exOut w] } } := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, ⟨toDmem⟩, fromDmem, f2d, ⟨d2e⟩, ⟨e2w⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hd hep ht he
  subst hd hep ht he
  have hfr : (w.iEp == w.iEp) = true := beq_self_eq_true _
  constructor
  · simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, hfr]
    repeat' split
    all_goals simp_all
  · apply state_ext <;> try rfl
    · -- toDmem
      simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exMem, exByteEn, exStData, exOff]
      repeat' split
      all_goals simp_all
    · -- e2w
      simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exOut, exData, exStData, exOff]
      repeat' split
      all_goals simp_all [tuple2, exOut, exData, exStData, exOff]
    · -- pc
      simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exPc, exNext]
      repeat' split
      all_goals simp_all
    · -- sb (unchanged: the instruction is not stale)
      simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons]
      split <;> simp_all

-- ── writeback ──
def loadVal (mb : t_membusiness) (d : BitVec 32) : BitVec 32 :=
  let sh := shift_right_logical d (concat_bits mb.offset 3 (0 : BitVec 3))
  let c := concat_bits (bool_to_bitvec1 mb.isUnsigned) 2 mb.size
  ite_bsv (if c == (0 : BitVec 3) then BTrue Unit_ else BFalse Unit_) (sign_extend (extract_bits sh 7 0))
    (ite_bsv (if c == (1 : BitVec 3) then BTrue Unit_ else BFalse Unit_) (sign_extend (extract_bits sh 15 0))
      (ite_bsv (if c == (4 : BitVec 3) then BTrue Unit_ else BFalse Unit_)
        (concat_bits (0 : BitVec 24) 8 (extract_bits sh 7 0))
        (ite_bsv (if c == (5 : BitVec 3) then BTrue Unit_ else BFalse Unit_)
          (concat_bits (0 : BitVec 16) 16 (extract_bits sh 15 0))
          (ite_bsv (if c == (2 : BitVec 3) then BTrue Unit_ else BFalse Unit_) sh 0))))

def wbVal (x : t_e2w) (d : BitVec 32) : BitVec 32 :=
  ite_bsv (isMemoryInst x.dInst) (loadVal x.memBusiness d) x.data

def commitOf (x : t_e2w) (d : BitVec 32) : t_commitinst :=
  { pc := x.pc, inst := x.dInst.inst, rd := (getInstFields x.dInst.inst).rd,
    data := ite_bsv x.dInst.valid_rd (wbVal x d) 0 }

theorem writeback_one (s : state) (x : t_e2w) (y : t_mem) (he : s.e2w.queue = [x])
    (hf : s.fromDmem.queue = ite_bsv (isMemoryInst x.dInst) [y] []) :
    (rule_RL_writeback s).1 = BTrue Unit_ ∧
    (rule_RL_writeback s).2 =
      { s with
        e2w := { queue := [] }
        fromDmem := { queue := [] }
        sb := arr_set s.sb (getInstFields x.dInst.inst).rd.toNat
          (arr_get s.sb (getInstFields x.dInst.inst).rd.toNat - ite_bsv (wr x.dInst) 1 0)
        rf := arr_set s.rf (getInstFields x.dInst.inst).rd.toNat
          (ite_bsv (wr x.dInst) (wbVal x y.data) (arr_get s.rf (getInstFields x.dInst.inst).rd.toNat))
        retiredInst := { queue := s.retiredInst.queue ++ [commitOf x y.data] } } := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, ⟨fromDmem⟩, f2d, d2e, ⟨e2w⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at he hf
  subst he hf
  constructor
  · simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons]
    repeat' split
    all_goals simp_all [ite_bsv]
  · apply state_ext <;> try rfl
    · -- fromDmem
      simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons]
      repeat' split
      all_goals simp_all [ite_bsv]
    · -- retiredInst
      simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons, commitOf, wbVal, loadVal]
      repeat' split
      all_goals simp_all [ite_bsv]
    · -- rf
      simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons, wbVal, loadVal, wr]
      repeat' split
      all_goals simp_all [ite_bsv]
    · -- sb
      simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons, wr]
      repeat' split
      all_goals simp_all [ite_bsv]

-- ── helpers for comparing with the spec ──
@[local simp] theorem ite_bsv_if (p : Prop) [Decidable p] (a b : α) :
    ite_bsv (if p then BTrue Unit_ else BFalse Unit_) a b = if p then a else b := by
  split <;> rfl

theorem arr_set_set (a : Array α) (i : Nat) (u v : α) : arr_set (arr_set a i u) i v = arr_set a i v := by
  unfold arr_set; simp [Array.set!_eq_setIfInBounds]

theorem arr_set_replicate_zero (n i : Nat) : arr_set (Array.replicate n (0 : Nat)) i 0 = Array.replicate n 0 := by
  unfold arr_set
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext (by simp)
  intro j h1 h2
  rw [Array.getElem_setIfInBounds h2]
  split <;> simp

theorem arr_get_set_eq (a : Array α) [Inhabited α] (i : Nat) (v : α) (h : i < a.size) :
    arr_get (arr_set a i v) i = v := by
  unfold arr_get arr_set; simp [Array.set!_eq_setIfInBounds, h]

theorem ite_redirect (a b : BitVec 32) :
    ite_bsv (bool_not (if (a == b) = true then BTrue Unit_ else BFalse Unit_)) a b = a := by
  by_cases h : a = b <;> simp [h]

theorem zext_app (k w : Nat) (y : BitVec w) : (0#k ++ y) = BitVec.setWidth (k + w) y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem loadVal_eq (mb : t_membusiness) (d : BitVec 32) :
    loadVal mb d = M_mktop_pipelined.Spec.processMem mb d := by
  simp only [loadVal, M_mktop_pipelined.Spec.processMem, ite_bsv_if, zero_extend, concat_bits]
  repeat' split
  all_goals first | rfl | exact zext_app _ _ _

@[local simp] theorem bool_and_BFalse_r (u) (x : t_bool) : bool_and x (BFalse u) = BFalse Unit_ := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

theorem extract_bits_self (x : BitVec 3) : extract_bits x 2 2 = extract_bit x 2 := rfl

def specOf (i : state) (h : BitVec 1) : M_mktop_pipelined.Spec.State :=
  ⟨i.pc, h, i.rf, i.iMem.memory, i.dMem.memory, i.retiredInst.queue⟩
def wOf (i : state) (instr : BitVec 32) : t_d2e :=
  decOut { pc := i.pc, ppc := i.pc + 4, iEp := i.ep } instr i.rf

theorem pc_shape (m lg : t_bool) (next p4 : BitVec 32) :
    ite_bsv m p4 (ite_bsv lg (ite_bsv (bool_not (if (next == p4) = true then BTrue Unit_ else BFalse Unit_))
      next p4) p4) = ite_bsv (bool_and lg (bool_not m)) next p4 := by
  rcases m with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases lg with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> by_cases hn : next = p4 <;> simp [hn]

theorem val_shape (m : t_bool) (l l' st d : BitVec 32) (h : m = BTrue Unit_ → l = l') :
    ite_bsv m l (ite_bsv m st d) = ite_bsv m l' d := by
  rcases m with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · simp [h rfl]
  · rfl

section Fields
variable (i : state) (h : BitVec 1) (instr : BitVec 32)
  (hinstr : i.iMem.memory.getD (extract_bits (shift_right_logical i.pc 2) 29 0).toNat default = instr)

include hinstr in
theorem pc_field : exPc (wOf i instr) (i.pc + 4) = (M_mktop_pipelined.Spec.stepOne (specOf i h)).pc := by
  simp only [M_mktop_pipelined.Spec.stepOne, specOf, hinstr]
  exact pc_shape _ _ _ _
include hinstr in
theorem rf_field (y : BitVec 32)
    (hy : isMemoryInst (decodeInst instr) = BTrue Unit_ →
      y = i.dMem.memory.getD (extract_bits (shift_right_logical (exMem (wOf i instr)).addr 2) 29 0).toNat default) :
    arr_set i.rf (getInstFields instr).rd.toNat
      (ite_bsv (wr (decodeInst instr)) (wbVal (exOut (wOf i instr)) y) (arr_get i.rf (getInstFields instr).rd.toNat)) =
    (M_mktop_pipelined.Spec.stepOne (specOf i h)).rf := by
  simp only [M_mktop_pipelined.Spec.stepOne, specOf, hinstr]
  simp only [wr, b2v_not, b2v_or, b2v_and, bitvec1_roundtrip, decodeInst_inst]
  congr 2
  simp only [wbVal, exOut, exData, exStData, exOff, exMem, wOf, decOut, readOp]
  exact val_shape _ _ _ _ _ (fun hm => by rw [hy hm, loadVal_eq]; rfl)
include hinstr in
theorem output_field (y : BitVec 32)
    (hy : isMemoryInst (decodeInst instr) = BTrue Unit_ →
      y = i.dMem.memory.getD (extract_bits (shift_right_logical (exMem (wOf i instr)).addr 2) 29 0).toNat default) :
    i.retiredInst.queue ++ [commitOf (exOut (wOf i instr)) y] =
    (M_mktop_pipelined.Spec.stepOne (specOf i h)).output := by
  simp only [M_mktop_pipelined.Spec.stepOne, specOf, hinstr]
  simp only [commitOf, exOut, wOf, decOut, decodeInst_inst, List.append_cancel_left_eq, List.cons.injEq, and_true]
  congr 1; congr 1
  simp only [wbVal, exOut, exData, exStData, exOff, exMem, wOf, decOut, readOp]
  exact val_shape _ _ _ _ _ (fun hm => by rw [hy hm, loadVal_eq]; rfl)

theorem put_shape {n : Nat} (st : M_mkSimpleBRAM.state (BitVec 32)) (x : BitVec 4) (addr : BitVec n) (d : BitVec 32) :
    (M_mkSimpleBRAM.meth_put st (bool_not (if (x == 0) = true then BTrue Unit_ else BFalse Unit_)) addr d).avAction_.memory =
    ite_bsv (if (x != 0) = true then BTrue Unit_ else BFalse Unit_) (st.memory.setIfInBounds addr.toNat d) st.memory := by
  simp only [M_mkSimpleBRAM.meth_put]
  repeat' split
  all_goals simp_all

theorem bv_default (n : Nat) : (default : BitVec n) = 0 := rfl

include hinstr in
theorem dmem_field_mem (hm : isMemoryInst (decodeInst instr) = BTrue Unit_) :
    (M_mkSimpleBRAM.meth_put i.dMem (bool_not (if ((exMem (wOf i instr)).byte_en == 0) = true then BTrue Unit_
        else BFalse Unit_)) (extract_bits (shift_right_logical (exMem (wOf i instr)).addr 2) 29 0)
        (exMem (wOf i instr)).data).avAction_.memory =
    (M_mktop_pipelined.Spec.stepOne (specOf i h)).dmem := by
  rw [put_shape]
  simp only [M_mktop_pipelined.Spec.stepOne, specOf, hinstr, hm, bool_and_BTrue_l]
  simp only [exMem, exByteEn, exStData, exOff, wOf, decOut, readOp, decodeInst_inst, ite_bsv_if, bv_default]
  rfl

include hinstr in
theorem dmem_field_nomem (hm : isMemoryInst (decodeInst instr) = BFalse Unit_) :
    i.dMem.memory = (M_mktop_pipelined.Spec.stepOne (specOf i h)).dmem := by
  simp only [M_mktop_pipelined.Spec.stepOne, specOf, hinstr, hm, bool_and_BFalse_l, ite_BFalse]
end Fields

theorem doFetch_run (i : state) (ss : M_mktop_pipelined.Spec.State) (h : phi0 i ss) :
    ∃ i', Relation.ReflTransGen ImplModule.getARule (meth_doFetch i).avAction_ i' ∧
      phi0 i' (M_mktop_pipelined.Spec.stepOne ss) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨spc, shalted, srf, simem, sdmem, sout⟩ := ss
  dsimp only at h13 h14 h15 h16 h17
  subst h13 h14 h15 h16 h17
  -- the fetched instruction and the pipeline records it travels in
  generalize hinstr : i.iMem.memory.getD (extract_bits (shift_right_logical i.pc 2) 29 0).toNat default = instr
  let f : t_f2d := { pc := i.pc, ppc := i.pc + 4, iEp := i.ep }
  let q : t_mem := { byte_en := 0, addr := i.pc, data := 0 }
  let w := decOut f instr i.rf
  -- fetch
  obtain ⟨g2, e2⟩ := requestI_one (meth_doFetch i).avAction_ q (by simp [meth_doFetch, h3, q]) h1
  obtain ⟨g3, e3⟩ := responseI_one (rule_RL_requestI (meth_doFetch i).avAction_).2 q instr
    (by rw [e2]) (by rw [e2]; simp [meth_doFetch, h10, q, ← hinstr]) (by rw [e2]; exact h4)
  obtain ⟨g4, e4⟩ := decode_fresh (rule_RL_responseI (rule_RL_requestI (meth_doFetch i).avAction_).2).2 f
    { byte_en := q.byte_en, addr := q.addr, data := instr }
    (by rw [e3, e2]; simp [meth_doFetch, h7, f]) (by rw [e3]) (by rw [e3, e2]; exact h8)
    (by rw [e3, e2]; rfl) (by rw [e3, e2]; exact h12)
  -- execute
  obtain ⟨g5, e5⟩ := execute_fresh
    (rule_RL_decode (rule_RL_responseI (rule_RL_requestI (meth_doFetch i).avAction_).2).2).2 w
    (by rw [e4, e3, e2]; rfl) (by rw [e4, e3, e2]; rfl) (by rw [e4, e3, e2]; exact h5)
    (by rw [e4, e3, e2]; exact h9)
  generalize hs4 : (rule_RL_decode (rule_RL_responseI (rule_RL_requestI (meth_doFetch i).avAction_).2).2).2 = s4
    at e4 e5 g5
  have hwd : w.dInst = decodeInst instr := rfl
  rcases hmem : isMemoryInst (decodeInst instr) with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · -- a memory instruction goes through the data BRAM
    obtain ⟨g6, e6⟩ := requestD_one (rule_RL_execute s4).2 (exMem w)
      (by rw [e5]; simp [hwd, hmem]) (by rw [e5, e4, e3, e2]; exact h2)
    obtain ⟨g7, e7⟩ := responseD_one (rule_RL_requestD (rule_RL_execute s4).2).2 (exMem w)
      (i.dMem.memory.getD (extract_bits (shift_right_logical (exMem w).addr 2) 29 0).toNat default)
      (by rw [e6]) (by rw [e6, e5, e4, e3, e2]; simp [meth_doFetch, h11])
      (by rw [e6, e5, e4, e3, e2]; exact h6)
    obtain ⟨g8, e8⟩ := writeback_one (rule_RL_responseD (rule_RL_requestD (rule_RL_execute s4).2).2).2
      (exOut w) { byte_en := (exMem w).byte_en, addr := (exMem w).addr,
                  data := i.dMem.memory.getD (extract_bits (shift_right_logical (exMem w).addr 2) 29 0).toNat default }
      (by rw [e7, e6, e5]) (by rw [e7]; simp only [exOut, hwd, hmem, ite_BTrue])
    refine ⟨(rule_RL_writeback (rule_RL_responseD (rule_RL_requestD (rule_RL_execute s4).2).2).2).2, ?_, ?_⟩
    · have c1 : Relation.ReflTransGen ImplModule.getARule (meth_doFetch i).avAction_ s4 := by
        rw [← hs4]
        exact .head ⟨.RL_requestI, Prod.ext g2 rfl⟩ <| .head ⟨.RL_responseI, Prod.ext g3 rfl⟩ <|
          .single ⟨.RL_decode, Prod.ext g4 rfl⟩
      refine c1.trans ?_
      apply Relation.ReflTransGen.head ⟨.RL_execute, Prod.ext g5 rfl⟩
      apply Relation.ReflTransGen.head ⟨.RL_requestD, Prod.ext g6 rfl⟩
      apply Relation.ReflTransGen.head ⟨.RL_responseD, Prod.ext g7 rfl⟩
      exact .single ⟨.RL_writeback, Prod.ext g8 rfl⟩
    unfold phi0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      (try rw [e8]); (try dsimp only); (try rw [e7]); (try dsimp only); (try rw [e6]); (try dsimp only)
      (try rw [e5]); (try dsimp only); (try rw [e4]); (try dsimp only); (try rw [e3]); (try dsimp only)
      (try rw [e2]); (try dsimp only)
    · -- sb: decode's increment is undone by writeback's decrement
      have hrd := rd_lt instr
      show arr_set (arr_set i.sb (getInstFields instr).rd.toNat (ite_bsv (wr (decodeInst instr)) 1 0))
          (getInstFields instr).rd.toNat
          (arr_get (arr_set i.sb (getInstFields instr).rd.toNat (ite_bsv (wr (decodeInst instr)) 1 0))
            (getInstFields instr).rd.toNat - ite_bsv (wr (decodeInst instr)) 1 0) = Array.replicate 32 0
      rw [h12, arr_get_set_eq _ _ _ (by simp [hrd]), Nat.sub_self, arr_set_set, arr_set_replicate_zero]
    · exact pc_field i shalted instr hinstr
    · exact rf_field i shalted instr hinstr _ (fun _ => rfl)
    · simp [q, Spec.stepOne, specOf, meth_doFetch]
    · exact dmem_field_mem i shalted instr hinstr hmem
    · exact output_field i shalted instr hinstr _ (fun _ => rfl)
  · -- otherwise execute's result goes straight to writeback
    obtain ⟨g8, e8⟩ := writeback_one (rule_RL_execute s4).2 (exOut w) default
      (by rw [e5]) (by rw [e5, e4, e3, e2]; simp only [exOut, hwd, hmem, ite_BFalse]; exact h6)
    refine ⟨(rule_RL_writeback (rule_RL_execute s4).2).2, ?_, ?_⟩
    · have c1 : Relation.ReflTransGen ImplModule.getARule (meth_doFetch i).avAction_ s4 := by
        rw [← hs4]
        exact .head ⟨.RL_requestI, Prod.ext g2 rfl⟩ <| .head ⟨.RL_responseI, Prod.ext g3 rfl⟩ <|
          .single ⟨.RL_decode, Prod.ext g4 rfl⟩
      refine c1.trans ?_
      apply Relation.ReflTransGen.head ⟨.RL_execute, Prod.ext g5 rfl⟩
      exact .single ⟨.RL_writeback, Prod.ext g8 rfl⟩
    unfold phi0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      (try rw [e8]); (try dsimp only); (try rw [e5]); (try dsimp only); (try rw [e4]); (try dsimp only)
      (try rw [e3]); (try dsimp only); (try rw [e2]); (try dsimp only)
    all_goals try (simp [meth_doFetch, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hwd, hmem]; done)
    · -- sb: decode's increment is undone by writeback's decrement
      have hrd := rd_lt instr
      show arr_set (arr_set i.sb (getInstFields instr).rd.toNat (ite_bsv (wr (decodeInst instr)) 1 0))
          (getInstFields instr).rd.toNat
          (arr_get (arr_set i.sb (getInstFields instr).rd.toNat (ite_bsv (wr (decodeInst instr)) 1 0))
            (getInstFields instr).rd.toNat - ite_bsv (wr (decodeInst instr)) 1 0) = Array.replicate 32 0
      rw [h12, arr_get_set_eq _ _ _ (by simp [hrd]), Nat.sub_self, arr_set_set, arr_set_replicate_zero]
    · exact pc_field i shalted instr hinstr
    · exact rf_field i shalted instr hinstr _ (fun hm => nomatch hmem.symm.trans hm)
    · simp [q, Spec.stepOne, specOf, meth_doFetch]
    · exact dmem_field_nomem i shalted instr hinstr hmem
    · exact output_field i shalted instr hinstr _ (fun hm => nomatch hmem.symm.trans hm)

end FlushedRun

-- No rule is enabled in a flushed state.
theorem phi0_no_rule {i i' : ImplModule.State} {s : SpecModule.State} (h : phi0 i s) :
    ¬ ImplModule.getARule i i' := by
  rintro ⟨r, hr⟩
  obtain ⟨-, -, h3, -, h5, -, h7, h8, h9, h10, h11, -⟩ := h
  cases r <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
    have hg := (Prod.ext_iff.mp hr).1
  · simp [M_mktop_pipelined.rule_RL_requestI, h3] at hg
  · simp [M_mktop_pipelined.rule_RL_responseI, h10] at hg
  · simp [M_mktop_pipelined.rule_RL_requestD, h5] at hg
  · simp [M_mktop_pipelined.rule_RL_responseD, h11] at hg
  · exact decode_f2d_ne _ hg h7
  · exact execute_d2e_ne _ hg h8
  · exact writeback_e2w_ne _ hg h9

theorem phi0_rtg {i i' : ImplModule.State} {s : SpecModule.State} (h : phi0 i s)
    (hr : Relation.ReflTransGen ImplModule.getARule i i') : i' = i := by
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨c, hc, -⟩
  · rfl
  · exact absurd hc (phi0_no_rule h)

-- Simulation obligations, in `∃` form (`StructuredRefinementUpto.flushed_simulates`): from a state
-- reached by rules from a flushed one, the spec can take the same method (for `doFetch` it may pick
-- the real step or the stutter), and the implementation gets back to a flushed state by rules.
theorem phi0_simulates_doFetch (i i' i'' : ImplModule.State) (s : SpecModule.State) (v : unit_) :
  phi0 i s → Relation.ReflTransGen ImplModule.getARule i i' →
  ImplModule.getMethod i' ⟨.doFetch, Footprint.arg0 v⟩ i'' →
  ∃ s', SpecModule.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s' ∧
    ∃ i''', Relation.ReflTransGen ImplModule.getARule i'' i''' ∧ phi0 i''' s' := by
  intro h hr hm
  obtain rfl : i = i' := (phi0_rtg h hr).symm
  dsimp only [ImplModule, Module.getMethod, orStutter0, ofAVMethod0] at hm
  rcases hm with ⟨v', hv, -, -⟩ | ⟨hfp, hi⟩
  · -- a real fetch: the spec executes the instruction, the pipeline drains it
    obtain rfl : i'' = (M_mktop_pipelined.meth_doFetch i).avAction_ := (congrArg (·.avAction_) hv).symm
    obtain ⟨i3, h3, hφ⟩ := doFetch_run i s h
    exact ⟨M_mktop_pipelined.Spec.stepOne s, Or.inl ⟨Unit_, rfl, by cases v; rfl, rfl⟩, i3, h3, hφ⟩
  · -- a stutter
    exact ⟨s, Or.inr ⟨hfp, rfl⟩, i'', .refl, hi ▸ h⟩

theorem phi0_simulates_getCommitInst (i i' i'' : ImplModule.State) (s : SpecModule.State)
    (v : t_commitinst) :
  phi0 i s → Relation.ReflTransGen ImplModule.getARule i i' →
  ImplModule.getMethod i' ⟨.getCommitInst, Footprint.arg0 v⟩ i'' →
  ∃ s', SpecModule.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s' ∧
    ∃ i''', Relation.ReflTransGen ImplModule.getARule i'' i''' ∧ phi0 i''' s' := by
  intro h hr hm
  obtain rfl : i = i' := (phi0_rtg h hr).symm
  dsimp only [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨v', hv, hfp, hrdy⟩ := hm
  obtain rfl : i'' = (M_mktop_pipelined.meth_getCommitInst i).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v' = (M_mktop_pipelined.meth_getCommitInst i).avValue_ := (congrArg (·.avValue_) hv).symm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  rcases hq : i.retiredInst.queue with _ | ⟨c, cs⟩
  · simp [M_mktop_pipelined.meth_RDY_getCommitInst, hq] at hrdy
  · have ho : s.output = c :: cs := h17 ▸ hq
    refine ⟨M_mktop_pipelined.Spec.State.mk s.pc s.halted s.rf s.imem s.dmem cs, ⟨c, ?_, ?_, ?_⟩, _, .refl, ?_⟩
    · simp [M_mktop_pipelined.Spec.meth_getCommitInst, ho]
    · rw [hfp]; simp [M_mktop_pipelined.meth_getCommitInst, M_mkFIFO.meth_first, hq]
    · simp [M_mktop_pipelined.Spec.meth_RDY_getCommitInst, ho]
    · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        by simp [M_mktop_pipelined.meth_getCommitInst, M_mkFIFO.meth_deq, hq]⟩

@[local grind →] theorem phi0_reaches_phi0_RL_requestI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestI i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_responseI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseI i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_requestD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestD i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_responseD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseD i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_decode (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_decode i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_execute (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_execute i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

@[local grind →] theorem phi0_reaches_phi0_RL_writeback (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_writeback i i' → phi0 i' s :=
  fun h hr => absurd ⟨_, hr⟩ (phi0_no_rule h)

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

theorem ImplModule.reachable_rule {a b : ImplModule.State} :
    ImplModule.reachable a → ImplModule.getARule a b → ImplModule.reachable b := by
  rintro ⟨s0, h0, hst⟩ hab
  exact ⟨s0, h0, hst.tail (.inl hab)⟩

theorem ImplModule.reachable_method {a b : ImplModule.State} {e : Event Method} :
    ImplModule.reachable a → ImplModule.getMethod a e b → ImplModule.reachable b := by
  rintro ⟨s0, h0, hst⟩ hab
  exact ⟨s0, h0, hst.tail (.inr ⟨e, hab⟩)⟩

theorem rules_commute_weakly_reachable {a b c : ImplModule.State} :
    ImplModule.reachable a → ImplModule.getARule a c → ImplModule.getARule a b →
    ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  rintro hR ⟨r1, h1⟩ ⟨r2, h2⟩
  have key : (∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧
      Relation.ReflTransGen ImplModule.getARule b d) ∨ ¬ ImplModule.reachable a := by
    cases r1 <;> cases r2
    all_goals first
      | exact commutes_RL_requestI_RL_requestI h1 h2
      | exact commutes_RL_requestI_RL_responseI h1 h2
      | exact commutes_RL_requestI_RL_requestD h1 h2
      | exact commutes_RL_requestI_RL_responseD h1 h2
      | exact commutes_RL_requestI_RL_decode h1 h2
      | exact commutes_RL_requestI_RL_execute h1 h2
      | exact commutes_RL_requestI_RL_writeback h1 h2
      | exact commutes_RL_responseI_RL_requestI h1 h2
      | exact commutes_RL_responseI_RL_responseI h1 h2
      | exact commutes_RL_responseI_RL_requestD h1 h2
      | exact commutes_RL_responseI_RL_responseD h1 h2
      | exact commutes_RL_responseI_RL_decode h1 h2
      | exact commutes_RL_responseI_RL_execute h1 h2
      | exact commutes_RL_responseI_RL_writeback h1 h2
      | exact commutes_RL_requestD_RL_requestI h1 h2
      | exact commutes_RL_requestD_RL_responseI h1 h2
      | exact commutes_RL_requestD_RL_requestD h1 h2
      | exact commutes_RL_requestD_RL_responseD h1 h2
      | exact commutes_RL_requestD_RL_decode h1 h2
      | exact commutes_RL_requestD_RL_execute h1 h2
      | exact commutes_RL_requestD_RL_writeback h1 h2
      | exact commutes_RL_responseD_RL_requestI h1 h2
      | exact commutes_RL_responseD_RL_responseI h1 h2
      | exact commutes_RL_responseD_RL_requestD h1 h2
      | exact commutes_RL_responseD_RL_responseD h1 h2
      | exact commutes_RL_responseD_RL_decode h1 h2
      | exact commutes_RL_responseD_RL_execute h1 h2
      | exact commutes_RL_responseD_RL_writeback h1 h2
      | exact commutes_RL_decode_RL_requestI h1 h2
      | exact commutes_RL_decode_RL_responseI h1 h2
      | exact commutes_RL_decode_RL_requestD h1 h2
      | exact commutes_RL_decode_RL_responseD h1 h2
      | exact commutes_RL_decode_RL_decode h1 h2
      | exact commutes_RL_decode_RL_execute h1 h2
      | exact commutes_RL_decode_RL_writeback h1 h2
      | exact commutes_RL_execute_RL_requestI h1 h2
      | exact commutes_RL_execute_RL_responseI h1 h2
      | exact commutes_RL_execute_RL_requestD h1 h2
      | exact commutes_RL_execute_RL_responseD h1 h2
      | exact commutes_RL_execute_RL_decode h1 h2
      | exact commutes_RL_execute_RL_execute h1 h2
      | exact commutes_RL_execute_RL_writeback h1 h2
      | exact commutes_RL_writeback_RL_requestI h1 h2
      | exact commutes_RL_writeback_RL_responseI h1 h2
      | exact commutes_RL_writeback_RL_requestD h1 h2
      | exact commutes_RL_writeback_RL_responseD h1 h2
      | exact commutes_RL_writeback_RL_decode h1 h2
      | exact commutes_RL_writeback_RL_execute h1 h2
      | exact commutes_RL_writeback_RL_writeback h1 h2
  exact key.resolve_right (· hR)

-- Method/rule commutation up to rules. Every pair commutes strongly (a stuttering `doFetch` is
-- replayed as a stutter), except a real fetch against a redirecting `RL_execute`: there the
-- execute-first side drains its stale fetches and stutters, meeting the fetch-first side after it
-- has drained the wrong-path fetch (`reconverge_RL_execute_doFetch`).
theorem method_rule_commute_upto {a b c : ImplModule.State} {e : Event Method} :
    ImplModule.reachable a → ImplModule.getARule a b → ImplModule.getMethod a e c →
    ∃ b' d j, Relation.ReflTransGen ImplModule.getARule b b' ∧ ImplModule.getMethod b' e d ∧
      Relation.ReflTransGen ImplModule.getARule c j ∧ Relation.ReflTransGen ImplModule.getARule d j := by
  rintro hR ⟨r, hr⟩ hm
  obtain ⟨name, fp⟩ := e
  have strong : (∃ d, ImplModule.getMethod b ⟨name, fp⟩ d ∧ ImplModule.getRule r c d) →
      ∃ b' d j, Relation.ReflTransGen ImplModule.getARule b b' ∧
        ImplModule.getMethod b' ⟨name, fp⟩ d ∧
        Relation.ReflTransGen ImplModule.getARule c j ∧ Relation.ReflTransGen ImplModule.getARule d j :=
    fun ⟨d, hd, hcd⟩ => ⟨b, d, d, .refl, hd, .single ⟨r, hcd⟩, .refl⟩
  rcases ImplModule.get_method_cases hm with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ <;>
    dsimp only at h1 h2 <;> subst h1 h2
  · cases r
    case RL_execute =>
      rcases reconverge_RL_execute_doFetch _ _ _ v hr hm with h | ⟨d, hbd, hcd⟩ | h
      · exact strong h
      · exact ⟨d, d, d, hbd, Or.inr ⟨by cases v; rfl, rfl⟩, hcd, .refl⟩
      · exact absurd hR h
    all_goals first
      | exact strong (reconverge_RL_requestI_doFetch _ _ _ v hr hm)
      | exact strong (reconverge_RL_responseI_doFetch _ _ _ v hr hm)
      | exact strong (reconverge_RL_requestD_doFetch _ _ _ v hr hm)
      | exact strong (reconverge_RL_responseD_doFetch _ _ _ v hr hm)
      | exact strong (reconverge_RL_decode_doFetch _ _ _ v hr hm)
      | exact strong (reconverge_RL_writeback_doFetch _ _ _ v hr hm)
  · cases r
    all_goals first
      | exact strong (reconverge_RL_requestI_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_responseI_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_requestD_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_responseD_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_decode_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_execute_getCommitInst _ _ _ v hr hm)
      | exact strong (reconverge_RL_writeback_getCommitInst _ _ _ v hr hm)

-- ──────────────────────────────────────────────────────────────────────
-- Below: generic boilerplate (closes `refines` via enough_star_upto').
-- ──────────────────────────────────────────────────────────────────────

attribute [local grind →] Module.getARule
attribute [grind cases] Event

def mktop_pipelined_refinement : StructuredRefinementUpto where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := phi0
  reachable := ImplModule.reachable
  reachable_rule := ImplModule.reachable_rule
  reachable_method := ImplModule.reachable_method
  rules_strongly_normalising := rules_strongly_normalising
  rules_commute_weakly := rules_commute_weakly_reachable
  method_rule_commute := method_rule_commute_upto
  flushed_simulates := by
    intro i i' i'' s e hf h0 hm
    obtain ⟨name, fp⟩ := e
    rcases ImplModule.get_method_cases hm with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ <;>
      dsimp only at h1 h2 <;> subst h1 h2
    · exact phi0_simulates_doFetch _ _ _ _ v hf h0 hm
    · exact phi0_simulates_getCommitInst _ _ _ _ v hf h0 hm

-- Every reset state is flushed, relative to the spec state with the same architectural state.
theorem phi0_init (i : ImplModule.State) (h : ImplModule.init i) (halted : BitVec 1) :
    phi0 i ⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, h11, rfl, rfl, rfl, rfl, h10⟩

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  ImplModule.reachable i →
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star_upto' mktop_pipelined_refinement

-- Trace inclusion from reset: every trace of the pipeline started in a reset state is a trace of
-- the spec started with the same `pc`, registers and memories and no pending commit records.
theorem trace_inclusion (l : List (Event Method)) (i : ImplModule.State) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    spec_behaviour SpecModule.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SpecModule.State) :=
  trace_inclusion_upto mktop_pipelined_refinement l i _ ⟨i, h, .refl⟩ (phi0_init i h halted)

#print axioms refines
#print axioms trace_inclusion

end M_mktop_pipelined.Refines
