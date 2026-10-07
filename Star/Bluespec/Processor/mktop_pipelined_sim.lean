import Star.Bluespec.Processor.mktop_pipelined_refines
open BluespecPrelude Params_types RVUtil
open ReachingStar Bluespec

set_option maxHeartbeats 4000000

/-!
A direct forward simulation between `mktop_pipelined` and the ISA spec, with no draining, flushing,
confluence or commutation argument: a relation `R` between arbitrary pipeline states and ISA states
is shown to be preserved by every rule and method of the pipeline.

`R i s` describes every instruction in flight against a ghost ISA run `st σ j = stepOne^[j] σ`
from the architectural state `σ` (`rf`, `retiredInst`, instruction memory):

* `e2w` holds the executed instructions `0 .. a-1` (`Pipe.e2w`); the data-memory FIFOs hold their
  memory requests in order, and `dMem` has absorbed exactly the stores already sent (`MemP`);
* `d2e`/`f2d` hold stale records, then instructions `a ..` of the ISA run, then wrong-path records,
  which exist only behind a pending mispredicted instruction (`Front`); the I-memory FIFOs mirror
  `f2d` (`FetchP`);
* the spec is `k` ISA steps ahead of the last right-path instruction in flight, one per wrong-path or
  stuttering fetch so far.

Every fetch is matched by a real ISA step, so the simulation targets the stutter-free spec `SpecNS`.

Reused from `mktop_pipelined_refines`: the module definitions, the per-entry scoreboard updates
(`decode_sb_get`, ...), rule-guard facts (`decode_reads`, `execute_d2e_ne`, ...)
and the datapath equalities relating pipeline computations to `stepOne` (`rf_field`, `pc_field`, ...).
Nothing about flushing, draining, confluence or rule/method commutation is used.
-/

namespace M_mktop_pipelined.Refines.Sim

open M_mktop_pipelined.Spec (stepOne)
open M_mktop_pipelined (state rule_RL_requestI rule_RL_responseI rule_RL_requestD rule_RL_responseD
  rule_RL_decode rule_RL_execute rule_RL_writeback meth_doFetch meth_getCommitInst meth_RDY_doFetch
  meth_RDY_getCommitInst)

abbrev SState := M_mktop_pipelined.Spec.State

-- ─── ISA-side quantities ────────────────────────────────────────────────

/-- The ISA state after `j` steps from `σ`. -/
def st (σ : SState) (j : Nat) : SState := stepOne^[j] σ

def iIdx (a : BitVec 32) : Nat := (extract_bits (shift_right_logical a 2) 29 0).toNat
def instrOf (t : SState) : BitVec 32 := t.imem.getD (iIdx t.pc) default
/-- The fetch record of the instruction at `t`. -/
def fOf (e : BitVec 1) (t : SState) : t_f2d := { pc := t.pc, ppc := t.pc + 4, iEp := e }
/-- The decode record of the instruction at `t` (operands read from the architectural `rf`). -/
def dOf (e : BitVec 1) (t : SState) : t_d2e := decOut (fOf e t) (instrOf t) t.rf
def isMem (t : SState) : Bool := isMemoryInst (decodeInst (instrOf t)) matches BTrue _
/-- The word a memory instruction at `t` reads. -/
def dval (t : SState) : BitVec 32 := t.dmem.getD (iIdx (exMem (dOf 0 t)).addr) default
def dresp (t : SState) : t_mem :=
  { byte_en := (exMem (dOf 0 t)).byte_en, addr := (exMem (dOf 0 t)).addr, data := dval t }
/-- The instruction at `t` does not fall through to `pc + 4`. -/
def mispred (t : SState) : Prop := (stepOne t).pc ≠ t.pc + 4

def redirB (w : t_d2e) : Bool :=
  match isMemoryInst w.dInst, w.dInst.legal with
  | BFalse _, BTrue _ => exNext w != w.ppc
  | _, _ => false

theorem isMem_iff (t : SState) : isMem t = true ↔ isMemoryInst (decodeInst (instrOf t)) = BTrue Unit_ := by
  unfold isMem; rcases isMemoryInst (decodeInst (instrOf t)) with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp

theorem not_isMem_iff (t : SState) : isMem t = false ↔ isMemoryInst (decodeInst (instrOf t)) = BFalse Unit_ := by
  unfold isMem; rcases isMemoryInst (decodeInst (instrOf t)) with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp

theorem st_zero (σ : SState) : st σ 0 = σ := rfl
theorem st_succ (σ : SState) (j : Nat) : st σ (j + 1) = stepOne (st σ j) :=
  Function.iterate_succ_apply' _ _ _
theorem st_succ' (σ : SState) (j : Nat) : st σ (j + 1) = st (stepOne σ) j :=
  Function.iterate_succ_apply _ _ _

@[simp] theorem stepOne_imem (t : SState) : (stepOne t).imem = t.imem := rfl

theorem st_imem (σ : SState) (j : Nat) : (st σ j).imem = σ.imem := by
  induction j with
  | zero => rfl
  | succ j ih => rw [st_succ, stepOne_imem, ih]

-- An implementation state carrying exactly the architectural state of `t`, to reuse the
-- datapath equalities of `mktop_pipelined_refines` (`rf_field`, `output_field`, ...).
def toI (t : SState) : state where
  iMem := { memory := t.imem, readResult := [] }
  dMem := { memory := t.dmem, readResult := [] }
  ireq := default
  dreq := default
  toImem := default
  fromImem := default
  toDmem := default
  fromDmem := default
  f2d := default
  d2e := default
  e2w := default
  retiredInst := { queue := t.output }
  pc := t.pc
  ep := 0
  rf := t.rf
  sb := default

theorem specOf_toI (t : SState) : specOf (toI t) t.halted = t := by cases t; rfl

theorem isa_pc (t : SState) : (stepOne t).pc = exPc (dOf 0 t) (t.pc + 4) := by
  have := pc_field (toI t) t.halted (instrOf t) rfl
  rw [specOf_toI] at this; exact this.symm

theorem isa_rf (t : SState) (y : BitVec 32)
    (hy : isMemoryInst (decodeInst (instrOf t)) = BTrue Unit_ → y = dval t) :
    (stepOne t).rf = arr_set t.rf (getInstFields (instrOf t)).rd.toNat
      (ite_bsv (wr (decodeInst (instrOf t))) (wbVal (exOut (dOf 0 t)) y)
        (arr_get t.rf (getInstFields (instrOf t)).rd.toNat)) := by
  have := rf_field (toI t) t.halted (instrOf t) rfl y hy
  rw [specOf_toI] at this; exact this.symm

theorem isa_output (t : SState) (y : BitVec 32)
    (hy : isMemoryInst (decodeInst (instrOf t)) = BTrue Unit_ → y = dval t) :
    (stepOne t).output = t.output ++ [commitOf (exOut (dOf 0 t)) y] := by
  have := output_field (toI t) t.halted (instrOf t) rfl y hy
  rw [specOf_toI] at this; exact this.symm

theorem isa_dmem_mem (t : SState) (b : M_mkSimpleBRAM.state (BitVec 32)) (hb : b.memory = t.dmem)
    (hm : isMemoryInst (decodeInst (instrOf t)) = BTrue Unit_) :
    (M_mkSimpleBRAM.meth_put b (bool_not (if ((exMem (dOf 0 t)).byte_en == 0) = true then BTrue Unit_
        else BFalse Unit_)) (extract_bits (shift_right_logical (exMem (dOf 0 t)).addr 2) 29 0)
        (exMem (dOf 0 t)).data).avAction_.memory = (stepOne t).dmem := by
  have := dmem_field_mem (toI t) t.halted (instrOf t) rfl hm
  rw [specOf_toI] at this
  rw [← this]
  obtain ⟨mem, rr⟩ := b
  dsimp only at hb; subst hb
  rfl

theorem isa_dmem_nomem (t : SState) (hm : isMemoryInst (decodeInst (instrOf t)) = BFalse Unit_) :
    (stepOne t).dmem = t.dmem := by
  have := dmem_field_nomem (toI t) t.halted (instrOf t) rfl hm
  rw [specOf_toI] at this; exact this.symm

theorem exPc_eq (w : t_d2e) (X : BitVec 32) : exPc w X = if redirB w then exNext w else X := by
  unfold exPc redirB
  rcases isMemoryInst w.dInst with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases w.dInst.legal with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    by_cases h : exNext w = w.ppc <;> simp [h, ite_bsv, bool_not]

theorem mispred_iff (t : SState) : mispred t ↔ redirB (dOf 0 t) = true := by
  unfold mispred
  rw [isa_pc, exPc_eq]
  cases hr : redirB (dOf 0 t)
  · rw [if_neg (by simp)]; simp
  · rw [if_pos rfl]
    simp only [ne_eq, iff_true]
    unfold redirB at hr
    split at hr
    · simpa [dOf, decOut, fOf] using hr
    · simp at hr

-- ─── What each implementation rule does ─────────────────────────────────

section RuleSem
attribute [local simp] b2v_not b2v_or b2v_and bool_and_BTrue_l bool_and_BFalse_l bool_and_BTrue_r
  bool_or_BTrue_l bool_or_BFalse_l bool_or_not_self bool_not_BTrue bool_not_BFalse ite_BTrue ite_BFalse
  if_bool_eq_BTrue if_bool_eq_BFalse BTrue_ne_BFalse BFalse_ne_BTrue unit_eq bool_and_BFalse_r
attribute [local simp] M_mkFIFO.meth_enq M_mkFIFO.meth_deq M_mkFIFO.meth_first M_mkFIFO.meth_RDY_enq
  M_mkFIFO.meth_RDY_deq M_mkFIFO.meth_RDY_first M_mkSimpleBRAM.meth_put M_mkSimpleBRAM.meth_read
  M_mkSimpleBRAM.meth_RDY_put M_mkSimpleBRAM.meth_RDY_read

theorem requestI_ne (s : state) (hg : (rule_RL_requestI s).1 = BTrue Unit_) : s.toImem.queue ≠ [] := by
  simp only [rule_RL_requestI, bool_and_true_iff, mkFIFO_RDY_deq_iff] at hg; exact hg.2.1

theorem responseI_ne (s : state) (hg : (rule_RL_responseI s).1 = BTrue Unit_) :
    s.ireq.queue ≠ [] ∧ s.iMem.readResult ≠ [] := by
  simp only [rule_RL_responseI, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkSimpleBRAM_RDY_read_iff] at hg
  exact ⟨hg.2.2.1.1, hg.2.1⟩

theorem requestD_ne (s : state) (hg : (rule_RL_requestD s).1 = BTrue Unit_) : s.toDmem.queue ≠ [] := by
  simp only [rule_RL_requestD, bool_and_true_iff, mkFIFO_RDY_deq_iff] at hg; exact hg.2.1

theorem responseD_ne (s : state) (hg : (rule_RL_responseD s).1 = BTrue Unit_) :
    s.dreq.queue ≠ [] ∧ s.dMem.readResult ≠ [] := by
  simp only [rule_RL_responseD, bool_and_true_iff, mkFIFO_RDY_deq_iff, mkSimpleBRAM_RDY_read_iff] at hg
  exact ⟨hg.2.2.1.1, hg.2.1⟩

theorem requestI_sem (s : state) (x : t_mem) (xs : List t_mem) (h : s.toImem.queue = x :: xs)
    (hx : x.byte_en = 0) :
    (rule_RL_requestI s).2.toImem.queue = xs ∧ (rule_RL_requestI s).2.ireq.queue = s.ireq.queue ++ [x] ∧
    (rule_RL_requestI s).2.iMem.memory = s.iMem.memory ∧
    (rule_RL_requestI s).2.iMem.readResult = s.iMem.readResult ++ [s.iMem.memory.getD (iIdx x.addr) default] := by
  simp [rule_RL_requestI, h, hx, iIdx]

theorem responseI_sem (s : state) (q : t_mem) (qs : List t_mem) (v : BitVec 32) (vs : List (BitVec 32))
    (hq : s.ireq.queue = q :: qs) (hv : s.iMem.readResult = v :: vs) :
    (rule_RL_responseI s).2.ireq.queue = qs ∧ (rule_RL_responseI s).2.iMem.memory = s.iMem.memory ∧
    (rule_RL_responseI s).2.iMem.readResult = vs ∧
    (rule_RL_responseI s).2.fromImem.queue =
      s.fromImem.queue ++ [{ byte_en := q.byte_en, addr := q.addr, data := v }] := by
  simp [rule_RL_responseI, hq, hv, ActionValue]

theorem requestD_sem (s : state) (x : t_mem) (xs : List t_mem) (h : s.toDmem.queue = x :: xs) :
    (rule_RL_requestD s).2.toDmem.queue = xs ∧ (rule_RL_requestD s).2.dreq.queue = s.dreq.queue ++ [x] ∧
    (rule_RL_requestD s).2.dMem = (M_mkSimpleBRAM.meth_put s.dMem
      (bool_not (if (x.byte_en == 0) = true then BTrue Unit_ else BFalse Unit_))
      (extract_bits (shift_right_logical x.addr 2) 29 0) x.data).avAction_ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rule_RL_requestD, M_mkFIFO.meth_deq, M_mkFIFO.meth_enq, M_mkFIFO.meth_first, h,
    List.tail_cons, List.headD_cons]

theorem put_readResult (b : M_mkSimpleBRAM.state (BitVec 32)) (w : t_bool) {n} (a : BitVec n) (d : BitVec 32) :
    (M_mkSimpleBRAM.meth_put b w a d).avAction_.readResult = b.readResult ++ [b.memory.getD a.toNat default] := rfl

theorem responseD_sem (s : state) (q : t_mem) (qs : List t_mem) (v : BitVec 32) (vs : List (BitVec 32))
    (hq : s.dreq.queue = q :: qs) (hv : s.dMem.readResult = v :: vs) :
    (rule_RL_responseD s).2.dreq.queue = qs ∧ (rule_RL_responseD s).2.dMem.memory = s.dMem.memory ∧
    (rule_RL_responseD s).2.dMem.readResult = vs ∧
    (rule_RL_responseD s).2.fromDmem.queue =
      s.fromDmem.queue ++ [{ byte_en := q.byte_en, addr := q.addr, data := v }] := by
  simp [rule_RL_responseD, hq, hv, ActionValue]

theorem decode_sem (s : state) (f : t_f2d) (fs : List t_f2d) (m : t_mem) (ms : List t_mem)
    (hf : s.f2d.queue = f :: fs) (hm : s.fromImem.queue = m :: ms) :
    (rule_RL_decode s).2.f2d.queue = fs ∧ (rule_RL_decode s).2.fromImem.queue = ms ∧
    (rule_RL_decode s).2.d2e.queue =
      if f.iEp = s.ep then s.d2e.queue ++ [decOut f m.data s.rf] else s.d2e.queue := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, ⟨fromImem⟩, toDmem, fromDmem, ⟨f2d⟩, ⟨d2e⟩, e2w,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hf hm
  subst hf hm
  refine ⟨rfl, rfl, ?_⟩
  simp only [rule_RL_decode, M_mkFIFO.meth_first, List.headD_cons]
  split
  · rename_i h
    simp only [if_bool_eq_BTrue, beq_iff_eq] at h
    simp only [h, if_true, M_mkFIFO.meth_enq, decOut, readOp]
    repeat' split
    all_goals simp_all
  · rename_i h
    simp only [if_bool_eq_BFalse, beq_iff_eq] at h
    simp [h]

theorem execute_sem (s : state) (w : t_d2e) (ws : List t_d2e) (hd : s.d2e.queue = w :: ws) :
    (rule_RL_execute s).2.d2e.queue = ws ∧
    (w.iEp ≠ s.ep → (rule_RL_execute s).2.e2w = s.e2w ∧ (rule_RL_execute s).2.toDmem = s.toDmem ∧
      (rule_RL_execute s).2.pc = s.pc ∧ (rule_RL_execute s).2.ep = s.ep) ∧
    (w.iEp = s.ep → (rule_RL_execute s).2.e2w.queue = s.e2w.queue ++ [exOut w] ∧
      (rule_RL_execute s).2.toDmem.queue =
        s.toDmem.queue ++ ite_bsv (isMemoryInst w.dInst) [exMem w] [] ∧
      (rule_RL_execute s).2.pc = (if redirB w then exNext w else s.pc) ∧
      ((rule_RL_execute s).2.ep = s.ep ↔ redirB w = false)) := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, ⟨toDmem⟩, fromDmem, f2d, ⟨d2e⟩, ⟨e2w⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at hd
  subst hd
  refine ⟨rfl, fun hst => ?_, fun hep => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons] <;>
      split <;> simp_all
  · subst hep
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exOut, exData, exStData, exOff]
      repeat' split
      all_goals simp_all [tuple2]
    · simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exMem, exByteEn, exStData, exOff]
      repeat' split
      all_goals simp_all
    · rw [← exPc_eq]
      simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, exPc, exNext]
      repeat' split
      all_goals simp_all
    · simp only [rule_RL_execute, M_mkFIFO.meth_first, List.headD_cons, redirB, exNext]
      have hflip : ∀ e : BitVec 1, (e + 1 = e) ↔ False := by
        intro e; rcases bv1_cases e with h | h <;> subst h <;> decide
      repeat' split
      all_goals simp_all [bool_to_bitvec1, bool_not]

theorem writeback_sem (s : state) (x : t_e2w) (xs : List t_e2w) (he : s.e2w.queue = x :: xs) :
    (rule_RL_writeback s).2.e2w.queue = xs ∧
    (rule_RL_writeback s).2.fromDmem.queue =
      ite_bsv (isMemoryInst x.dInst) s.fromDmem.queue.tail s.fromDmem.queue ∧
    (rule_RL_writeback s).2.rf = arr_set s.rf (getInstFields x.dInst.inst).rd.toNat
      (ite_bsv (wr x.dInst) (wbVal x (s.fromDmem.queue.headD default).data)
        (arr_get s.rf (getInstFields x.dInst.inst).rd.toNat)) ∧
    (rule_RL_writeback s).2.retiredInst.queue =
      s.retiredInst.queue ++ [commitOf x (s.fromDmem.queue.headD default).data] := by
  obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, ⟨fromDmem⟩, f2d, d2e, ⟨e2w⟩,
    retiredInst, pc, ep, rf, sb⟩ := s
  dsimp only at he
  subst he
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons]
    repeat' split
    all_goals simp_all [ite_bsv]
  · simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons, wbVal, loadVal, wr]
    repeat' split
    all_goals simp_all [ite_bsv]
  · simp only [rule_RL_writeback, M_mkFIFO.meth_first, List.headD_cons, commitOf, wbVal, loadVal]
    repeat' split
    all_goals simp_all [ite_bsv]

end RuleSem

-- ─── Helper facts ──────────────────────────────────────────────────────

theorem bool_or_BTrue_r (x : t_bool) : bool_or x (BTrue Unit_) = BTrue Unit_ := by
  rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- An operand read only looks at `rf` when the operand is valid. -/
theorem readOp_congr (d : t_decodedinst) (r : BitVec 5) (v : t_bool) (rf₁ rf₂ : Array (BitVec 32))
    (h : v = BTrue Unit_ → arr_get rf₁ r.toNat = arr_get rf₂ r.toNat) :
    readOp d r v rf₁ = readOp d r v rf₂ := by
  unfold readOp
  rcases v with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · rw [h rfl]
  · simp only [bool_not_BFalse, bool_or_BTrue_r, bool_or_BTrue_l, ite_BTrue]

theorem decOut_congr (f : t_f2d) (instr : BitVec 32) (rf₁ rf₂ : Array (BitVec 32))
    (h1 : (decodeInst instr).valid_rs1 = BTrue Unit_ →
      arr_get rf₁ (getInstFields instr).rs1.toNat = arr_get rf₂ (getInstFields instr).rs1.toNat)
    (h2 : (decodeInst instr).valid_rs2 = BTrue Unit_ →
      arr_get rf₁ (getInstFields instr).rs2.toNat = arr_get rf₂ (getInstFields instr).rs2.toNat) :
    decOut f instr rf₁ = decOut f instr rf₂ := by
  unfold decOut
  rw [readOp_congr _ _ _ _ _ h1, readOp_congr _ _ _ _ _ h2]

/-- An ISA step leaves every register it does not write unchanged. -/
theorem rf_step (t : SState) (r : Nat) (h : writes r (decodeInst (instrOf t)) = false) :
    arr_get (stepOne t).rf r = arr_get t.rf r := by
  rw [isa_rf t (dval t) (fun _ => rfl)]
  by_cases hrd : (getInstFields (instrOf t)).rd.toNat = r
  · subst hrd
    rcases hw : wr (decodeInst (instrOf t)) with u | u
    · rw [writes_of_wr_true _ hw] at h; simp at h
    · rw [ite_BFalse]; exact arr_get_set_self _ _
  · exact arr_get_set_ne _ _ _ _ hrd

theorem rf_chain (σ : SState) (r n : Nat)
    (h : ∀ j < n, writes r (decodeInst (instrOf (st σ j))) = false) :
    arr_get (st σ n).rf r = arr_get σ.rf r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [st_succ, rf_step _ _ (h n (by omega)), ih (fun j hj => h j (by omega))]

theorem fInstr_fOf (m : Array (BitVec 32)) (e : BitVec 1) (t : SState) (hm : m = t.imem) :
    (m.getD (iIdx (fOf e t).pc) default) = instrOf t := by
  subst hm; rfl

-- The memory instructions among the first `a` instructions.
def memIdx (σ : SState) (a : Nat) : List Nat := (List.range a).filter (fun j => isMem (st σ j))

theorem mem_memIdx {σ : SState} {a j : Nat} : j ∈ memIdx σ a ↔ j < a ∧ isMem (st σ j) = true := by
  simp [memIdx]

theorem memIdx_pairwise (σ : SState) (a : Nat) : (memIdx σ a).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem memIdx_succ (σ : SState) (a : Nat) :
    memIdx σ (a + 1) = memIdx σ a ++ (if isMem (st σ a) then [a] else []) := by
  unfold memIdx
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : isMem (st σ a) <;> simp [h]

theorem memIdx_shift (σ : SState) (a : Nat) :
    memIdx σ (a + 1) = (if isMem σ then [0] else []) ++ (memIdx (stepOne σ) a).map (· + 1) := by
  unfold memIdx
  rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have : (fun j => isMem (st σ j)) ∘ (· + 1) = fun j => isMem (st (stepOne σ) j) := by
    funext j; simp [st_succ']
  rw [this]
  by_cases h : isMem σ <;> simp [h, st_zero]

theorem dmem_const (σ : SState) (c j : Nat) (hcj : c ≤ j)
    (h : ∀ m, c ≤ m → m < j → isMem (st σ m) = false) : (st σ j).dmem = (st σ c).dmem := by
  induction j with
  | zero => obtain rfl : c = 0 := by omega
            rfl
  | succ j ih =>
    rcases Nat.lt_or_ge c (j + 1) with hc | hc
    · rw [st_succ, isa_dmem_nomem _ ((not_isMem_iff _).mp (h j (by omega) (by omega))),
        ih (by omega) (fun m h1 h2 => h m h1 (by omega))]
    · obtain rfl : c = j + 1 := by omega
      rfl

-- An ISA step ignores `output`, apart from appending to it.
theorem stepOne_output (s : SState) :
    ∃ c, (stepOne s).output = s.output ++ [c] ∧
      ∀ o, stepOne { s with output := o } = { stepOne s with output := o ++ [c] } :=
  ⟨_, rfl, fun _ => rfl⟩

theorem st_output (σ : SState) (j : Nat) :
    ∃ ex, (st σ j).output = σ.output ++ ex ∧
      ∀ o, st { σ with output := o } j = { st σ j with output := o ++ ex } := by
  induction j with
  | zero => exact ⟨[], by simp [st_zero], fun o => by simp [st_zero]⟩
  | succ j ih =>
    obtain ⟨ex, h1, h2⟩ := ih
    obtain ⟨c, h3, h4⟩ := stepOne_output (st σ j)
    refine ⟨ex ++ [c], ?_, fun o => ?_⟩
    · rw [st_succ, h3, h1, List.append_assoc]
    · rw [st_succ, st_succ, h2, h4, List.append_assoc]

theorem mispred_output (t : SState) (o : List t_commitinst) :
    mispred { t with output := o } ↔ mispred t := by
  obtain ⟨c, -, h⟩ := stepOne_output t
  unfold mispred; rw [h]

/-- The ISA spec without the `doFetch` stutter. -/
def SpecNS : Bluespec.Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.Spec.meth_doFetch M_mktop_pipelined.Spec.meth_RDY_doFecth
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules := Empty.casesOn _

-- ─── The simulation relation ───────────────────────────────────────────

def fReq (f : t_f2d) : t_mem := { byte_en := 0, addr := f.pc, data := 0 }
def fInstr (m : Array (BitVec 32)) (f : t_f2d) : BitVec 32 := m.getD (iIdx f.pc) default
def fResp (m : Array (BitVec 32)) (f : t_f2d) : t_mem := { byte_en := 0, addr := f.pc, data := fInstr m f }

/-- Fetch side: the `f2d` records, oldest first, are those whose instruction has come back
(`fromImem`), is being read (`ireq`, with the BRAM's pending read results), or is still to be
requested (`toImem`). -/
def FetchP (i : state) : Prop :=
  ∃ A B C : List t_f2d, i.f2d.queue = A ++ B ++ C ∧ i.fromImem.queue = A.map (fResp i.iMem.memory) ∧
    i.ireq.queue = B.map fReq ∧ i.iMem.readResult = B.map (fInstr i.iMem.memory) ∧
    i.toImem.queue = C.map fReq

/-- Memory side: the memory instructions among the executed ones (`e2w`), oldest first, have their
response in `fromDmem` (`P1`), are being served (`P2`), or are still to be sent (`P3`). The data
memory has seen exactly the stores of `P1 ++ P2`: it is the ISA's data memory at a cut point `c`
between them and `P3`. -/
def MemP (i : state) (σ : SState) (a : Nat) : Prop :=
  ∃ (P1 P2 P3 : List Nat) (c : Nat), memIdx σ a = P1 ++ P2 ++ P3 ∧
    i.fromDmem.queue = P1.map (fun j => dresp (st σ j)) ∧
    i.dreq.queue = P2.map (fun j => exMem (dOf 0 (st σ j))) ∧
    i.dMem.readResult = P2.map (fun j => dval (st σ j)) ∧
    i.toDmem.queue = P3.map (fun j => exMem (dOf 0 (st σ j))) ∧
    c ≤ a ∧ (∀ j ∈ P1 ++ P2, j < c) ∧ (∀ j ∈ P3, c ≤ j) ∧ i.dMem.memory = (st σ c).dmem

/-- Front end: `d2e` and `f2d` hold, oldest first, stale records (older epoch, `S`), the next
right-path instructions `g 0, g 1, ...` (`nd` decoded, then `nf` fetched), and wrong-path records
(current epoch, `W`) which only exist after a pending mispredicted instruction. When no mispredict
is pending, `pc` is the next right-path instruction. -/
def Front (ep : BitVec 1) (pc : BitVec 32) (dq : List t_d2e) (fq : List t_f2d) (g : Nat → SState)
    (nd nf : Nat) : Prop :=
  ∃ (Sd Wd : List t_d2e) (Sf Wf : List t_f2d),
    dq = Sd ++ (List.range nd).map (fun t => dOf ep (g t)) ++ Wd ∧
    fq = Sf ++ (List.range nf).map (fun t => fOf ep (g (nd + t))) ++ Wf ∧
    (∀ x ∈ Sd, x.iEp ≠ ep) ∧ (∀ x ∈ Sf, x.iEp ≠ ep) ∧
    (∀ x ∈ Wd, x.iEp = ep) ∧ (∀ x ∈ Wf, x.iEp = ep) ∧
    (Sf ≠ [] → nd = 0 ∧ Wd = []) ∧ (Wd ≠ [] → nf = 0) ∧
    (∀ t, t + 1 < nd + nf → ¬ mispred (g t)) ∧
    (Wd ≠ [] ∨ Wf ≠ [] → nd + nf ≠ 0 ∧ mispred (g (nd + nf - 1))) ∧
    ((nd + nf = 0 ∨ ¬ mispred (g (nd + nf - 1))) → pc = (g (nd + nf)).pc)

/-- The pipeline state `i` against the ISA run from `σ`: instructions `0 .. a-1` are executed
(`e2w`), `a .. a+nd+nf-1` are in the front end, and `σ` is the architectural state. -/
structure Pipe (i : state) (σ : SState) (a nd nf : Nat) : Prop where
  rf : i.rf = σ.rf
  imem : i.iMem.memory = σ.imem
  ret : i.retiredInst.queue = σ.output
  e2w : i.e2w.queue = (List.range a).map (fun j => exOut (dOf 0 (st σ j)))
  mem : MemP i σ a
  fetch : FetchP i
  front : Front i.ep i.pc i.d2e.queue i.f2d.queue (fun t => st σ (a + t)) nd nf

-- ─── Scoreboard invariant ──────────────────────────────────────────────

/-- The scoreboard covers every in-flight writer (it may overcount, never undercount). -/
def SBCover (s : state) : Prop :=
  s.sb.size = 32 ∧ ∀ r < 32, inflight s r ≤ arr_get s.sb r

theorem sbcover_decode (s : state) (h : SBCover s) :
    SBCover (rule_RL_decode s).2 := by
  obtain ⟨hsz, hc⟩ := h
  have hd : (rule_RL_decode s).2.d2e.queue.map (·.dInst) = s.d2e.queue.map (·.dInst) ++
      (if (M_mkFIFO.meth_first s.f2d).iEp = s.ep then [decodeInst (M_mkFIFO.meth_first s.fromImem).data]
        else []) := by
    dsimp only [rule_RL_decode]
    split <;> rename_i hF <;> simp only [if_bool_eq_BTrue', if_bool_eq_BFalse', beq_iff_eq] at hF <;>
      simp [hF, M_mkFIFO.meth_enq]
  refine ⟨by simp [hsz], fun r hr => ?_⟩
  have := hc r hr
  clear hc
  unfold inflight at *
  rw [hd, decode_sb_get _ _ (by omega)]
  show _ + (s.e2w.queue.map (·.dInst)).countP (writes r) ≤ _
  by_cases hF : (M_mkFIFO.meth_first s.f2d).iEp = s.ep <;>
    by_cases hw : writes r (decodeInst (M_mkFIFO.meth_first s.fromImem).data) = true <;> (simp_all; try omega)

theorem sbcover_execute (s : state) (h : SBCover s) (hg : (rule_RL_execute s).1 = BTrue Unit_) :
    SBCover (rule_RL_execute s).2 := by
  have hne := execute_d2e_ne s hg
  obtain ⟨hsz, hc⟩ := h
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
  refine ⟨by simp [hsz], fun r hr => ?_⟩
  have := hc r hr
  clear hc
  unfold inflight at *
  rw [hd, he, execute_sb_get _ _ (by omega), hw]
  rw [hq] at this
  by_cases hF : w.iEp = s.ep <;> by_cases hwr : writes r w.dInst = true <;> simp_all <;> omega

theorem sbcover_writeback (s : state) (h : SBCover s) (hg : (rule_RL_writeback s).1 = BTrue Unit_) :
    SBCover (rule_RL_writeback s).2 := by
  have hne := writeback_e2w_ne s hg
  obtain ⟨hsz, hc⟩ := h
  obtain ⟨x, xs, hq⟩ := List.exists_cons_of_ne_nil hne
  have hx : M_mkFIFO.meth_first s.e2w = x := by simp [M_mkFIFO.meth_first, hq]
  have he : (rule_RL_writeback s).2.e2w.queue = xs := by
    show (M_mkFIFO.meth_deq s.e2w).avAction_.queue = xs; simp [M_mkFIFO.meth_deq, hq]
  refine ⟨by simp [hsz], fun r hr => ?_⟩
  have := hc r hr
  clear hc
  unfold inflight at *
  rw [he, writeback_sb_get _ _ (by omega), hx]
  show (s.d2e.queue.map (·.dInst)).countP (writes r) + _ ≤ _
  rw [hq] at this
  by_cases hwr : writes r x.dInst = true <;> (simp_all; try omega)

theorem sbcover_init (s : ImplModule.State) (h : ImplModule.init s) : SBCover s := by
  obtain ⟨-, -, -, -, -, -, -, hd, he, -, hsb, -, -, -⟩ := h
  exact ⟨by rw [hsb]; simp, fun r hr => by simp [inflight, hd, he]⟩


/-- The spec is `k` ISA steps past the last right-path instruction in flight (one per wrong-path
fetch or stuttering fetch so far). -/
def R (i : state) (s : SState) : Prop :=
  SBCover i ∧ ∃ σ a nd nf k, Pipe i σ a nd nf ∧ s = st σ (a + nd + nf + k)

theorem R_init (i : ImplModule.State) (h : ImplModule.init i) (halted : BitVec 1) :
    R i ⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ := by
  have hsb := sbcover_init i h
  obtain ⟨hi, hd, ht, hm, htd, hfd, hf, hde, he, hr, -, -, hrr, hdrr⟩ := h
  refine ⟨hsb, _, 0, 0, 0, 0, ⟨rfl, rfl, hr, by simp [he], ?_, ?_, ?_⟩, rfl⟩
  · exact ⟨[], [], [], 0, rfl, by simp [hfd], by simp [hd], by simp [hdrr], by simp [htd], le_rfl,
      by simp, by simp, rfl⟩
  · exact ⟨[], [], [], by simp [hf], by simp [hm], by simp [hi], by simp [hrr], by simp [ht]⟩
  · exact ⟨[], [], [], [], by simp [hde], by simp [hf], by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, fun _ => rfl⟩

-- ─── Preservation: fetch and memory interface rules ────────────────────

theorem R_requestI {i : state} {s : SState} (h : R i s) (hg : (rule_RL_requestI i).1 = BTrue Unit_) :
    R (rule_RL_requestI i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w, hmem, ⟨A, B, C, hf, hA, hB, hR, hC⟩, hfr⟩, rfl⟩ := h
  obtain ⟨c, C', rfl⟩ : ∃ c C', C = c :: C' :=
    List.exists_cons_of_ne_nil (by rintro rfl; exact requestI_ne i hg (by simp [hC]))
  obtain ⟨h1, h2, h3, h4⟩ := requestI_sem i (fReq c) (C'.map fReq) (by simp [hC]) rfl
  refine ⟨hsb, σ, a, nd, nf, k, ⟨hrf, h3.trans him, hret, he2w, hmem,
    ⟨A, B ++ [c], C', ?_, ?_, ?_, ?_, ?_⟩, hfr⟩, rfl⟩
  · show i.f2d.queue = _; simp [hf]
  · rw [h3]; exact hA
  · simp [h2, hB]
  · rw [h4, h3, hR]; simp [fInstr, fReq]
  · exact h1

theorem R_responseI {i : state} {s : SState} (h : R i s) (hg : (rule_RL_responseI i).1 = BTrue Unit_) :
    R (rule_RL_responseI i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w, hmem, ⟨A, B, C, hf, hA, hB, hR, hC⟩, hfr⟩, rfl⟩ := h
  obtain ⟨hne1, -⟩ := responseI_ne i hg
  obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' :=
    List.exists_cons_of_ne_nil (by rintro rfl; exact hne1 (by simp [hB]))
  obtain ⟨h1, h2, h3, h4⟩ := responseI_sem i (fReq b) (B'.map fReq) (fInstr i.iMem.memory b)
    (B'.map (fInstr i.iMem.memory)) (by simp [hB]) (by simp [hR])
  refine ⟨hsb, σ, a, nd, nf, k, ⟨hrf, h2.trans him, hret, he2w, hmem,
    ⟨A ++ [b], B', C, ?_, ?_, ?_, ?_, ?_⟩, hfr⟩, rfl⟩
  · show i.f2d.queue = _; simp [hf]
  · rw [h4, h2, hA]; simp [fResp, fReq]
  · exact h1
  · rw [h3, h2]
  · exact hC

theorem R_requestD {i : state} {s : SState} (h : R i s) (hg : (rule_RL_requestD i).1 = BTrue Unit_) :
    R (rule_RL_requestD i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, hP3, hca, hlt, hge, hmemc⟩, hfe, hfr⟩, rfl⟩ := h
  obtain ⟨j, P3', rfl⟩ : ∃ j P3', P3 = j :: P3' :=
    List.exists_cons_of_ne_nil (by rintro rfl; exact requestD_ne i hg (by simp [hP3]))
  obtain ⟨h1, h2, h3⟩ := requestD_sem i (exMem (dOf 0 (st σ j))) (P3'.map fun j => exMem (dOf 0 (st σ j)))
    (by simp [hP3])
  have hjmem : j ∈ memIdx σ a := by rw [hidx]; simp
  obtain ⟨hja, hjm⟩ := mem_memIdx.mp hjmem
  have hpw := memIdx_pairwise σ a
  rw [hidx] at hpw
  have hsorted : ∀ x ∈ P3', j < x := by
    have := (List.pairwise_append.mp hpw).2.1
    exact (List.pairwise_cons.mp this).1
  have hcj : c ≤ j := hge j (by simp)
  -- no memory instruction between the cut point and `j`
  have hmj : i.dMem.memory = (st σ j).dmem := by
    rw [hmemc, dmem_const σ c j hcj]
    intro m hcm hmj
    by_contra hm
    have hm' : m ∈ P1 ++ P2 ++ j :: P3' := by
      rw [← hidx]; exact mem_memIdx.mpr ⟨by omega, by simpa using hm⟩
    simp only [List.mem_append, List.mem_cons] at hm'
    rcases hm' with (hm' | hm') | hm' | hm'
    · have := hlt m (by simp [hm']); omega
    · have := hlt m (by simp [hm']); omega
    · omega
    · have := hsorted m hm'; omega
  refine ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2 ++ [j], P3', j + 1, by rw [hidx]; simp, hP1, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩, hfe, hfr⟩, rfl⟩
  · rw [h2, hP2]; simp
  · rw [h3, put_readResult, hR, hmj]; simp [dval, iIdx]
  · exact h1
  · intro x hx
    by_cases hxj : x = j
    · omega
    · have := hlt x (by simp only [List.mem_append, List.mem_singleton] at hx ⊢; tauto); omega
  · intro x hx; have := hsorted x hx; omega
  · rw [h3, st_succ]
    exact isa_dmem_mem _ _ hmj ((isMem_iff _).mp hjm)

theorem R_responseD {i : state} {s : SState} (h : R i s) (hg : (rule_RL_responseD i).1 = BTrue Unit_) :
    R (rule_RL_responseD i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, hP3, hca, hlt, hge, hmemc⟩, hfe, hfr⟩, rfl⟩ := h
  obtain ⟨hne1, -⟩ := responseD_ne i hg
  obtain ⟨j, P2', rfl⟩ : ∃ j P2', P2 = j :: P2' :=
    List.exists_cons_of_ne_nil (by rintro rfl; exact hne1 (by simp [hP2]))
  obtain ⟨h1, h2, h3, h4⟩ := responseD_sem i (exMem (dOf 0 (st σ j))) (P2'.map fun j => exMem (dOf 0 (st σ j)))
    (dval (st σ j)) (P2'.map fun j => dval (st σ j))
    (by simp [hP2]) (by simp [hR])
  refine ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1 ++ [j], P2', P3, c, by rw [hidx]; simp, ?_, h1, h3, hP3, hca, ?_, hge, h2.trans hmemc⟩, hfe, hfr⟩, rfl⟩
  · rw [h4, hP1]; simp [dresp]
  · intro x hx
    apply hlt
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto

-- ─── Preservation: writeback (the ghost base advances by one ISA step) ─

theorem map_shift {β : Type} (σ : SState) (f : SState → β) (Q : List Nat) :
    (Q.map (· + 1)).map (fun j => f (st σ j)) = Q.map (fun j => f (st (stepOne σ) j)) := by
  simp [Function.comp_def, st_succ']

theorem R_writeback {i : state} {s : SState} (h : R i s) (hg : (rule_RL_writeback i).1 = BTrue Unit_) :
    R (rule_RL_writeback i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, hP3, hca, hlt, hge, hmemc⟩, hfe, hfr⟩, rfl⟩ := h
  have hne := writeback_e2w_ne i hg
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := by
    cases a with
    | zero => simp [he2w] at hne
    | succ a' => exact ⟨a', rfl⟩
  have hx : i.e2w.queue =
      exOut (dOf 0 σ) :: (List.range a).map (fun j => exOut (dOf 0 (st (stepOne σ) j))) := by
    rw [he2w, List.range_succ_eq_map]; simp [st_zero, st_succ', Function.comp_def]
  obtain ⟨h1, h2, h3, h4⟩ := writeback_sem i _ _ hx
  have hxd : (exOut (dOf 0 σ)).dInst = decodeInst (instrOf σ) := rfl
  rw [hxd] at h2
  have hshift := memIdx_shift σ a
  rw [hidx] at hshift
  -- split off instruction 0's memory record, if any
  obtain ⟨P1r, hP1e, hP1r, hrest, hy⟩ : ∃ P1r, P1 = (if isMem σ then [0] else []) ++ P1r ∧
      i.fromDmem.queue = (if isMem σ then [dresp σ] else []) ++ P1r.map (fun j => dresp (st σ j)) ∧
      P1r ++ P2 ++ P3 = (memIdx (stepOne σ) a).map (· + 1) ∧
      (isMemoryInst (decodeInst (instrOf σ)) = BTrue Unit_ → (i.fromDmem.queue.headD default).data = dval σ) := by
    by_cases hm : isMem σ = true
    · have hne' : i.fromDmem.queue ≠ [] := writeback_mem_fromDmem i hg (by
        simp only [M_mkFIFO.meth_first, hx, List.headD_cons, hxd]; exact (isMem_iff σ).mp hm)
      obtain ⟨p, P1', rfl⟩ : ∃ p P1', P1 = p :: P1' :=
        List.exists_cons_of_ne_nil (by rintro rfl; exact hne' (by simp [hP1]))
      simp only [hm, if_true, List.cons_append, List.cons.injEq] at hshift
      obtain ⟨rfl, hs⟩ := hshift
      exact ⟨P1', by simp [hm], by simp [hP1, hm, st_zero], hs, fun _ => by simp [hP1, dresp, st_zero]⟩
    · simp only [hm, Bool.false_eq_true, if_false, List.nil_append] at hshift
      exact ⟨P1, by simp [hm], by simp [hP1, hm], hshift,
        fun h' => absurd ((isMem_iff σ).mpr h') hm⟩
  obtain ⟨Q1, Q23, hq, hQ1, hQ23⟩ := List.map_eq_append_iff.mp (hrest.symm.trans (List.append_assoc _ _ _))
  obtain ⟨Q2, Q3, rfl, hQ2, hQ3⟩ := List.map_eq_append_iff.mp hQ23
  subst hQ1 hQ2 hQ3
  refine ⟨sbcover_writeback i hsb hg, stepOne σ, a, nd, nf, k, ⟨?_, him, ?_, h1, ?_, hfe, ?_⟩, ?_⟩
  · rw [h3, hrf]; exact (isa_rf σ _ hy).symm
  · rw [h4, hret]; exact (isa_output σ _ hy).symm
  · refine ⟨Q1, Q2, Q3, c - 1, by rw [hq, List.append_assoc], ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · rw [h2, hP1r]
      rcases hmi : isMemoryInst (decodeInst (instrOf σ)) with u | u
      · have hm : isMem σ = true := (isMem_iff σ).mpr (by cases u; exact hmi)
        simp only [hm, if_true, ite_bsv, List.singleton_append, List.tail_cons, List.map_map]
        exact List.map_congr_left (fun j _ => by simp [st_succ'])
      · have hm : isMem σ = false := (not_isMem_iff σ).mpr (by cases u; exact hmi)
        simp only [hm, Bool.false_eq_true, if_false, ite_bsv, List.nil_append, List.map_map]
        exact List.map_congr_left (fun j _ => by simp [st_succ'])
    · show i.dreq.queue = _; rw [hP2, List.map_map]
      exact List.map_congr_left (fun j _ => by simp [st_succ'])
    · show i.dMem.readResult = _; rw [hR, List.map_map]
      exact List.map_congr_left (fun j _ => by simp [st_succ'])
    · show i.toDmem.queue = _; rw [hP3, List.map_map]
      exact List.map_congr_left (fun j _ => by simp [st_succ'])
    · intro j hj
      have hj1 : j + 1 ∈ P1 ++ Q2.map (· + 1) := by
        rw [hP1e]
        rcases List.mem_append.mp hj with hj | hj
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr (List.mem_map.mpr ⟨j, hj, rfl⟩))))
        · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨j, hj, rfl⟩))
      have := hlt (j + 1) hj1
      omega
    · intro j hj
      have := hge (j + 1) (List.mem_map.mpr ⟨j, hj, rfl⟩)
      omega
    · show i.dMem.memory = _
      rw [hmemc]
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · -- nothing requested yet, so instruction 0 is not a memory instruction
        have hm : isMem σ = false := by
          by_contra hm
          have := hlt 0 (by rw [hP1e]; simp [Bool.not_eq_false] at hm; simp [hm])
          omega
        simp only [st_zero, Nat.zero_sub]
        exact (isa_dmem_nomem σ ((not_isMem_iff σ).mp hm)).symm
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [st_succ']; rfl
  · have hfun : (fun t => st (stepOne σ) (a + t)) = (fun t => st σ (a + 1 + t)) := by
      funext t; rw [show a + 1 + t = (a + t) + 1 by omega, st_succ']
    rw [hfun]; exact hfr
  · rw [show a + 1 + nd + nf + k = (a + nd + nf + k) + 1 by omega, st_succ']

-- ─── Preservation: decode ──────────────────────────────────────────────

/-- A register with no in-flight writer holds, in the implementation, the value the ISA gives it
just before the next instruction to decode. -/
theorem rf_ready {i : state} {σ : SState} {a nd : Nat} {Sd Wd : List t_d2e} (hsb : SBCover i)
    (hrf : i.rf = σ.rf) (he2w : i.e2w.queue = (List.range a).map (fun j => exOut (dOf 0 (st σ j))))
    (hd : i.d2e.queue = Sd ++ (List.range nd).map (fun t => dOf i.ep (st σ (a + t))) ++ Wd)
    (r : Nat) (hr : r < 32) (h0 : arr_get i.sb r = 0) :
    arr_get i.rf r = arr_get (st σ (a + nd)).rf r := by
  have hc := hsb.2 r hr
  rw [h0] at hc
  unfold inflight at hc
  have hd0 : (i.d2e.queue.map (·.dInst)).countP (writes r) = 0 := by omega
  have he0 : (i.e2w.queue.map (·.dInst)).countP (writes r) = 0 := by omega
  rw [List.countP_eq_zero] at hd0 he0
  rw [rf_chain σ r (a + nd), hrf]
  intro j hj
  have hdi : ∀ e, (dOf e (st σ j)).dInst = decodeInst (instrOf (st σ j)) := fun _ => rfl
  by_cases hja : j < a
  · have := he0 (exOut (dOf 0 (st σ j))).dInst (by rw [he2w]; simp only [List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hja, rfl⟩)
    simpa using this
  · have := hd0 (dOf i.ep (st σ (a + (j - a)))).dInst (by
      rw [hd]; simp only [List.map_append, List.mem_append, List.map_map, List.mem_map, List.mem_range]
      exact .inl (.inr ⟨j - a, by omega, rfl⟩))
    rw [show a + (j - a) = j by omega, hdi] at this
    simpa using this

theorem R_decode {i : state} {s : SState} (h : R i s) (hg : (rule_RL_decode i).1 = BTrue Unit_) :
    R (rule_RL_decode i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w, hmem, ⟨A, B, C, hf, hA, hB, hR, hC⟩,
    ⟨Sd, Wd, Sf, Wf, hd, hff, hSd, hSf, hWd, hWf, hSfc, hWdc, hcons, hW, hpc⟩⟩, rfl⟩ := h
  have hmne := decode_fromImem_ne i hg
  obtain ⟨f0, A', rfl⟩ : ∃ f0 A', A = f0 :: A' :=
    List.exists_cons_of_ne_nil (by rintro rfl; exact hmne (by simp [hA]))
  have hf2d : i.f2d.queue = f0 :: (A' ++ B ++ C) := by simp [hf]
  have hfim : i.fromImem.queue = fResp i.iMem.memory f0 :: A'.map (fResp i.iMem.memory) := by simp [hA]
  obtain ⟨h1, h2, h3⟩ := decode_sem i f0 _ _ _ hf2d hfim
  have hfe' : FetchP (rule_RL_decode i).2 := ⟨A', B, C, by rw [h1], by rw [h2]; rfl, hB, hR, hC⟩
  have hsb' := sbcover_decode i hsb
  rcases Sf with _ | ⟨x, Sf'⟩
  · rcases nf with _ | nf
    · -- a wrong-path instruction: it joins the wrong-path decoded records
      simp only [List.range_zero, List.map_nil, List.nil_append, List.append_nil] at hff
      rw [hf2d] at hff
      subst hff
      have hlive : f0.iEp = i.ep := hWf f0 (by simp)
      rw [if_pos hlive] at h3
      have hfr' : Front i.ep i.pc (rule_RL_decode i).2.d2e.queue (rule_RL_decode i).2.f2d.queue
          (fun t => st σ (a + t)) nd 0 :=
        ⟨Sd, Wd ++ [decOut f0 (fResp i.iMem.memory f0).data i.rf], [], A' ++ B ++ C, ?_, ?_, hSd, by simp,
          ?_, fun y hy => hWf y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto), by simp,
          fun _ => rfl, hcons, fun _ => hW (.inr (by simp)), hpc⟩
      · exact ⟨hsb', σ, a, nd, 0, k, ⟨hrf, him, hret, he2w, hmem, hfe', hfr'⟩, rfl⟩
      · rw [h3, hd]; simp
      · rw [h1]; simp
      · intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hWd y hy
        · exact hlive
    · -- the next right-path instruction
      have hWd0 : Wd = [] := by
        by_contra hne; exact absurd (hWdc hne) (by omega)
      subst hWd0
      rw [List.range_succ_eq_map, hf2d] at hff
      simp only [List.nil_append, List.map_cons, List.cons_append, List.cons.injEq, Nat.add_zero,
        List.map_map] at hff
      obtain ⟨hf0, hrest⟩ := hff
      have hlive : f0.iEp = i.ep := by rw [hf0]; rfl
      rw [if_pos hlive] at h3
      -- the decoded record is the ISA's
      have hnew : decOut f0 (fResp i.iMem.memory f0).data i.rf = dOf i.ep (st σ (a + nd)) := by
        have hreads := decode_reads i hg (by
          simp only [M_mkFIFO.meth_first, hf2d, List.headD_cons, hlive, beq_self_eq_true, if_true])
        simp only [M_mkFIFO.meth_first, hfim, List.headD_cons] at hreads
        rw [hf0] at hreads ⊢
        have hins : (fResp i.iMem.memory (fOf i.ep (st σ (a + nd)))).data = instrOf (st σ (a + nd)) :=
          fInstr_fOf _ _ _ (him.trans (st_imem σ _).symm)
        rw [hins] at hreads ⊢
        unfold dOf
        apply decOut_congr
        · intro hv
          exact rf_ready hsb hrf he2w hd _ (getInstFields _).rs1.isLt (hreads.1 hv)
        · intro hv
          exact rf_ready hsb hrf he2w hd _ (getInstFields _).rs2.isLt (hreads.2 hv)
      have hfr' : Front i.ep i.pc (rule_RL_decode i).2.d2e.queue (rule_RL_decode i).2.f2d.queue
          (fun t => st σ (a + t)) (nd + 1) nf :=
        ⟨Sd, [], [], Wf, ?_, ?_, hSd, by simp, by simp, hWf, by simp, by simp, ?_, ?_, ?_⟩
      · refine ⟨hsb', σ, a, nd + 1, nf, k, ⟨hrf, him, hret, he2w, hmem, hfe', hfr'⟩, ?_⟩
        rw [show a + (nd + 1) + nf + k = a + nd + (nf + 1) + k by omega]
      · rw [h3, hd, hnew, List.range_succ]; simp
      · rw [h1, hrest]
        simp only [List.nil_append]
        congr 1
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        rw [show nd + (t + 1) = nd + 1 + t by omega]
      · intro t ht; exact hcons t (by omega)
      · intro hw
        rcases hw with hw | hw
        · simp at hw
        · obtain ⟨-, hm⟩ := hW (.inr hw)
          exact ⟨by omega, by rw [show nd + 1 + nf - 1 = nd + (nf + 1) - 1 by omega]; exact hm⟩
      · intro hp
        rw [show nd + 1 + nf = nd + (nf + 1) by omega]
        apply hpc
        rcases hp with hp | hp
        · exact .inl (by omega)
        · exact .inr (by rwa [show nd + (nf + 1) - 1 = nd + 1 + nf - 1 by omega])
  · -- a stale instruction: dropped
    simp only [List.cons_append] at hff
    rw [hf2d, List.cons.injEq] at hff
    obtain ⟨rfl, hrest⟩ := hff
    have hstale : ¬ f0.iEp = i.ep := hSf f0 (by simp)
    rw [if_neg hstale] at h3
    have hfr' : Front i.ep i.pc (rule_RL_decode i).2.d2e.queue (rule_RL_decode i).2.f2d.queue
        (fun t => st σ (a + t)) nd nf :=
      ⟨Sd, Wd, Sf', Wf, h3.trans hd, by rw [h1, hrest], hSd, fun y hy => hSf y (by simp [hy]), hWd, hWf,
        fun _ => hSfc (by simp), hWdc, hcons, hW, hpc⟩
    exact ⟨hsb', σ, a, nd, nf, k, ⟨hrf, him, hret, he2w, hmem, hfe', hfr'⟩, rfl⟩

-- ─── Preservation: execute ─────────────────────────────────────────────

theorem exOut_dOf (e : BitVec 1) (t : SState) : exOut (dOf e t) = exOut (dOf 0 t) := rfl
theorem exMem_dOf (e : BitVec 1) (t : SState) : exMem (dOf e t) = exMem (dOf 0 t) := rfl
theorem redirB_dOf (e : BitVec 1) (t : SState) : redirB (dOf e t) = redirB (dOf 0 t) := rfl
theorem exNext_dOf (e : BitVec 1) (t : SState) : exNext (dOf e t) = exNext (dOf 0 t) := rfl

theorem R_execute {i : state} {s : SState} (h : R i s) (hg : (rule_RL_execute i).1 = BTrue Unit_) :
    R (rule_RL_execute i).2 s := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, hP3, hca, hlt, hge, hmemc⟩, hfe,
    ⟨Sd, Wd, Sf, Wf, hd, hff, hSd, hSf, hWd, hWf, hSfc, hWdc, hcons, hW, hpc⟩⟩, rfl⟩ := h
  have hne := execute_d2e_ne i hg
  have hsb' := sbcover_execute i hsb hg
  rcases Sd with _ | ⟨x, Sd'⟩
  · rcases nd with _ | nd
    · -- the head would be a wrong-path record with no pending mispredict: impossible
      simp only [List.range_zero, List.map_nil, List.nil_append] at hd
      have hWne : Wd ≠ [] := by rw [← hd]; exact hne
      have := hWdc hWne
      have := (hW (.inl hWne)).1
      omega
    · -- the next right-path instruction executes
      rw [List.range_succ_eq_map] at hd
      simp only [List.nil_append, List.map_cons, List.cons_append, Nat.add_zero, List.map_map] at hd
      obtain ⟨h1, -, h3⟩ := execute_sem i _ _ hd
      obtain ⟨he', htd', hpc', hep'⟩ := h3 rfl
      rw [exOut_dOf] at he'
      rw [exMem_dOf] at htd'
      have hdI : (dOf i.ep (st σ a)).dInst = decodeInst (instrOf (st σ a)) := rfl
      rw [hdI] at htd'
      rw [redirB_dOf] at hpc' hep'
      rw [exNext_dOf] at hpc'
      -- executed instructions and the memory pipeline gain instruction `a`
      have he2w' : (rule_RL_execute i).2.e2w.queue =
          (List.range (a + 1)).map (fun j => exOut (dOf 0 (st σ j))) := by
        rw [he', he2w, List.range_succ]; simp
      have hmem' : MemP (rule_RL_execute i).2 σ (a + 1) := by
        refine ⟨P1, P2, P3 ++ (if isMem (st σ a) then [a] else []), c, ?_, hP1, hP2, hR, ?_, by omega,
          hlt, ?_, hmemc⟩
        · rw [memIdx_succ, hidx]; simp
        · rw [htd', hP3]
          rcases hmi : isMemoryInst (decodeInst (instrOf (st σ a))) with u | u
          · have hm : isMem (st σ a) = true := (isMem_iff _).mpr (by cases u; exact hmi)
            simp [hm, ite_bsv]
          · have hm : isMem (st σ a) = false := (not_isMem_iff _).mpr (by cases u; exact hmi)
            simp [hm, ite_bsv]
        · intro j hj
          simp only [List.mem_append] at hj
          rcases hj with hj | hj
          · exact hge j hj
          · split at hj <;> simp at hj; omega
      by_cases hmis : mispred (st σ a)
      · -- mispredicted: redirect, and every younger record becomes stale
        have hr : redirB (dOf 0 (st σ a)) = true := (mispred_iff _).mp hmis
        have h0 : nd + nf = 0 := by
          by_contra hc; exact hcons 0 (by omega) (by simpa using hmis)
        obtain ⟨rfl, rfl⟩ : nd = 0 ∧ nf = 0 := by omega
        simp only [List.range_zero, List.map_nil, List.nil_append] at hd h1
        have hSf0 : Sf = [] := by
          by_contra hc; exact absurd (hSfc hc).1 (by omega)
        subst hSf0
        simp only [List.range_zero, List.map_nil, List.nil_append, List.append_nil] at hff
        have hep2 : (rule_RL_execute i).2.ep ≠ i.ep := by
          intro he; have := hep'.mp he; rw [hr] at this; exact absurd this (by decide)
        have hpc2 : (rule_RL_execute i).2.pc = (st σ (a + 1)).pc := by
          rw [hpc', if_pos hr, st_succ, isa_pc, exPc_eq, if_pos hr]
        have hfr' : Front (rule_RL_execute i).2.ep (rule_RL_execute i).2.pc (rule_RL_execute i).2.d2e.queue
            (rule_RL_execute i).2.f2d.queue (fun t => st σ (a + 1 + t)) 0 0 :=
          ⟨Wd, [], Wf, [], by rw [h1]; simp, by show i.f2d.queue = _; rw [hff]; simp,
            fun y hy => by rw [hWd y hy]; exact Ne.symm hep2,
            fun y hy => by rw [hWf y hy]; exact Ne.symm hep2,
            by simp, by simp, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun t ht => by omega,
            fun hw => by simp at hw, fun _ => by rw [hpc2]⟩
        exact ⟨hsb', σ, a + 1, 0, 0, k, ⟨hrf, him, hret, he2w', hmem', hfe, hfr'⟩, by
          rw [show a + (0 + 1) + 0 + k = a + 1 + 0 + 0 + k by omega]⟩
      · -- correctly predicted: nothing else changes
        have hr : redirB (dOf 0 (st σ a)) = false := by
          simpa using (fun h => hmis ((mispred_iff _).mpr h))
        have hep2 : (rule_RL_execute i).2.ep = i.ep := hep'.mpr hr
        have hpc2 : (rule_RL_execute i).2.pc = i.pc := by rw [hpc', if_neg (by rw [hr]; decide)]
        have hfr' : Front (rule_RL_execute i).2.ep (rule_RL_execute i).2.pc (rule_RL_execute i).2.d2e.queue
            (rule_RL_execute i).2.f2d.queue (fun t => st σ (a + 1 + t)) nd nf := by
          rw [hep2, hpc2]
          refine ⟨[], Wd, Sf, Wf, ?_, ?_, by simp, hSf, hWd, hWf,
            fun hs => absurd (hSfc hs).1 (by omega), hWdc, ?_, ?_, ?_⟩
          · rw [h1]; simp only [List.nil_append]
            congr 1
            apply List.map_congr_left
            intro t _
            simp only [Function.comp_apply, Nat.succ_eq_add_one]
            rw [show a + (t + 1) = a + 1 + t by omega]
          · show i.f2d.queue = _
            rw [hff]
            congr 2
            apply List.map_congr_left
            intro t _
            simp only
            rw [show a + (nd + 1 + t) = a + 1 + (nd + t) by omega]
          · intro t ht
            have := hcons (t + 1) (by omega)
            simpa [show a + (t + 1) = a + 1 + t by omega] using this
          · intro hw
            obtain ⟨-, hm⟩ := hW hw
            have hnz : nd + nf ≠ 0 := by
              intro h0; apply hmis; simpa [show nd + 1 + nf - 1 = 0 by omega] using hm
            exact ⟨hnz, by dsimp only; rw [show a + 1 + (nd + nf - 1) = a + (nd + nf) by omega]; simpa using hm⟩
          · intro hp
            have hp' : nd + 1 + nf = 0 ∨ ¬ mispred (st σ (a + (nd + 1 + nf - 1))) := by
              right
              by_cases h0 : nd + nf = 0
              · simpa [show nd + 1 + nf - 1 = 0 by omega] using hmis
              · rcases hp with hp | hp
                · exact absurd hp h0
                · dsimp only at hp; rw [show a + 1 + (nd + nf - 1) = a + (nd + nf) by omega] at hp; simpa using hp
            have := hpc hp'
            simpa [show a + (nd + 1 + nf) = a + 1 + (nd + nf) by omega] using this
        exact ⟨hsb', σ, a + 1, nd, nf, k, ⟨hrf, him, hret, he2w', hmem', hfe, hfr'⟩, by
          rw [show a + (nd + 1) + nf + k = a + 1 + nd + nf + k by omega]⟩
  · -- a stale instruction: dropped
    simp only [List.cons_append] at hd
    obtain ⟨h1, h2, -⟩ := execute_sem i _ _ hd
    obtain ⟨he, htd, hpc2, hep2⟩ := h2 (hSd x (by simp))
    have hfr' : Front (rule_RL_execute i).2.ep (rule_RL_execute i).2.pc (rule_RL_execute i).2.d2e.queue
        (rule_RL_execute i).2.f2d.queue (fun t => st σ (a + t)) nd nf := by
      rw [hep2, hpc2]
      exact ⟨Sd', Wd, Sf, Wf, by rw [h1], hff, fun y hy => hSd y (by simp [hy]), hSf, hWd, hWf, hSfc, hWdc,
        hcons, hW, hpc⟩
    exact ⟨hsb', σ, a, nd, nf, k, ⟨hrf, him, hret, by rw [he]; exact he2w,
      ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, by rw [htd]; exact hP3, hca, hlt, hge, hmemc⟩, hfe, hfr'⟩, rfl⟩

-- ─── Preservation: the methods ─────────────────────────────────────────

/-- A real fetch: on the right path it adds the next ISA instruction to the front end; after a
pending mispredict it adds a wrong-path record. Either way the spec takes one ISA step. -/
theorem R_doFetch {i : state} {s : SState} (h : R i s) : R (meth_doFetch i).avAction_ (stepOne s) := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w, hmem, ⟨A, B, C, hf, hA, hB, hR, hC⟩,
    ⟨Sd, Wd, Sf, Wf, hd, hff, hSd, hSf, hWd, hWf, hSfc, hWdc, hcons, hW, hpc⟩⟩, rfl⟩ := h
  let fnew : t_f2d := { pc := i.pc, ppc := i.pc + 4, iEp := i.ep }
  have hf' : (meth_doFetch i).avAction_.f2d.queue = i.f2d.queue ++ [fnew] := rfl
  have hfe' : FetchP (meth_doFetch i).avAction_ :=
    ⟨A, B, C ++ [fnew], by rw [hf', hf]; simp, hA, hB, hR, by
      show i.toImem.queue ++ [fReq fnew] = _; rw [hC]; simp⟩
  by_cases onP : nd + nf = 0 ∨ ¬ mispred (st σ (a + (nd + nf - 1)))
  · -- right path
    have hpcv := hpc onP
    have hWd0 : Wd = [] := by
      by_contra hc; obtain ⟨h1, h2⟩ := hW (.inl hc); rcases onP with h | h <;> contradiction
    have hWf0 : Wf = [] := by
      by_contra hc; obtain ⟨h1, h2⟩ := hW (.inr hc); rcases onP with h | h <;> contradiction
    subst hWd0 hWf0
    have hnew : fnew = fOf i.ep (st σ (a + (nd + nf))) := by
      simp only [fnew, fOf, hpcv]
    have hfr' : Front i.ep (i.pc + 4) i.d2e.queue (i.f2d.queue ++ [fnew]) (fun t => st σ (a + t)) nd (nf + 1) :=
      ⟨Sd, [], Sf, [], hd, by rw [hff, hnew, List.range_succ]; simp, hSd, hSf, by simp, by simp,
        fun hs => ⟨(hSfc hs).1, rfl⟩, by simp, ?_, fun hw => by simp at hw, ?_⟩
    · exact ⟨hsb, σ, a, nd, nf + 1, k, ⟨hrf, him, hret, he2w, hmem, hfe', hfr'⟩, by
        rw [show a + nd + (nf + 1) + k = (a + nd + nf + k) + 1 by omega, st_succ]⟩
    · intro t ht
      by_cases ht' : t + 1 < nd + nf
      · exact hcons t ht'
      · rcases onP with h0 | h0
        · omega
        · rwa [show t = nd + nf - 1 by omega]
    · intro hp
      have hnm : ¬ mispred (st σ (a + (nd + nf))) := by
        rcases hp with hp | hp
        · omega
        · simpa [show nd + (nf + 1) - 1 = nd + nf by omega] using hp
      simp only [mispred, ne_eq, not_not] at hnm
      simp only [show a + (nd + (nf + 1)) = a + (nd + nf) + 1 by omega, st_succ, hnm]
      rw [hpcv]
  · -- wrong path: the spec runs one more step ahead
    have hfr' : Front i.ep (i.pc + 4) i.d2e.queue (i.f2d.queue ++ [fnew]) (fun t => st σ (a + t)) nd nf :=
      ⟨Sd, Wd, Sf, Wf ++ [fnew], hd, by rw [hff]; simp, hSd, hSf, hWd,
        fun y hy => by
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hWf y hy
          · rfl,
        hSfc, hWdc, hcons, fun _ => by
          simp only [not_or, not_not] at onP; exact onP,
        fun hp => absurd hp onP⟩
    exact ⟨hsb, σ, a, nd, nf, k + 1, ⟨hrf, him, hret, he2w, hmem, hfe', hfr'⟩, by
      rw [show a + nd + nf + (k + 1) = (a + nd + nf + k) + 1 by omega, st_succ]⟩

/-- A stuttering fetch: the spec runs one more step ahead. -/
theorem R_stutter {i : state} {s : SState} (h : R i s) : R i (stepOne s) := by
  obtain ⟨hsb, σ, a, nd, nf, k, hp, rfl⟩ := h
  exact ⟨hsb, σ, a, nd, nf, k + 1, hp, by
    rw [show a + nd + nf + (k + 1) = (a + nd + nf + k) + 1 by omega, st_succ]⟩

theorem Front_congr {ep : BitVec 1} {pc : BitVec 32} {dq : List t_d2e} {fq : List t_f2d}
    {g g' : Nat → SState} {nd nf : Nat} (h : Front ep pc dq fq g nd nf)
    (hD : ∀ t, dOf ep (g' t) = dOf ep (g t)) (hF : ∀ t, fOf ep (g' t) = fOf ep (g t))
    (hM : ∀ t, mispred (g' t) ↔ mispred (g t)) (hP : ∀ t, (g' t).pc = (g t).pc) :
    Front ep pc dq fq g' nd nf := by
  obtain ⟨Sd, Wd, Sf, Wf, hd, hff, hSd, hSf, hWd, hWf, hSfc, hWdc, hcons, hW, hpc⟩ := h
  refine ⟨Sd, Wd, Sf, Wf, by simp only [hD]; exact hd, by simp only [hF]; exact hff, hSd, hSf, hWd, hWf,
    hSfc, hWdc, by simp only [hM]; exact hcons, by simp only [hM]; exact hW, by simp only [hM, hP]; exact hpc⟩

/-- A commit is read: the ghost base loses the same record from its `output`. -/
theorem R_getCommitInst {i i' : state} {s : SState} {fp : Footprint} (h : R i s)
    (hm : ImplModule.getMethod i ⟨.getCommitInst, fp⟩ i') :
    ∃ s', SpecNS.getMethod s ⟨.getCommitInst, fp⟩ s' ∧ R i' s' := by
  obtain ⟨hsb, σ, a, nd, nf, k, ⟨hrf, him, hret, he2w,
    ⟨P1, P2, P3, c, hidx, hP1, hP2, hR, hP3, hca, hlt, hge, hmemc⟩, hfe, hfr⟩, rfl⟩ := h
  obtain ⟨v, hv, hfp, hrdy⟩ := hm
  obtain rfl : i' = (meth_getCommitInst i).avAction_ := (congrArg (·.avAction_) hv).symm
  obtain rfl : v = (meth_getCommitInst i).avValue_ := (congrArg (·.avValue_) hv).symm
  rcases hq : i.retiredInst.queue with _ | ⟨x, xs⟩
  · simp [meth_RDY_getCommitInst, hq] at hrdy
  have hout : σ.output = x :: xs := hret ▸ hq
  -- the ghost base without the record read; its ISA run differs only in `output`
  let σ' : SState := { σ with output := xs }
  have hst : ∀ j, ∃ o, st σ' j = { st σ j with output := o } := fun j => by
    obtain ⟨ex, -, h2⟩ := st_output σ j; exact ⟨_, h2 xs⟩
  have eD : ∀ e j, dOf e (st σ' j) = dOf e (st σ j) := fun e j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; rfl
  have eF : ∀ e j, fOf e (st σ' j) = fOf e (st σ j) := fun e j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; rfl
  have eM : ∀ j, isMem (st σ' j) = isMem (st σ j) := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; rfl
  have eV : ∀ j, dval (st σ' j) = dval (st σ j) := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; rfl
  have eR : ∀ j, dresp (st σ' j) = dresp (st σ j) := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; rfl
  have eDm : ∀ j, (st σ' j).dmem = (st σ j).dmem := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]
  have eP : ∀ j, (st σ' j).pc = (st σ j).pc := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]
  have eMis : ∀ j, mispred (st σ' j) ↔ mispred (st σ j) := fun j => by
    obtain ⟨o, ho⟩ := hst j; rw [ho]; exact mispred_output _ _
  have eIdx : memIdx σ' a = memIdx σ a := by unfold memIdx; simp only [eM]
  obtain ⟨ex, hex1, hex2⟩ := st_output σ (a + nd + nf + k)
  refine ⟨st σ' (a + nd + nf + k), ⟨x, ?_, ?_, ?_⟩, hsb, σ', a, nd, nf, k,
    ⟨hrf, him, ?_, ?_, ⟨P1, P2, P3, c, ?_, ?_, ?_, ?_, ?_, hca, hlt, hge, ?_⟩, hfe, ?_⟩, rfl⟩
  · show M_mktop_pipelined.Spec.meth_getCommitInst _ = _
    rw [hex2 xs]
    simp [M_mktop_pipelined.Spec.meth_getCommitInst, hex1, hout]
  · rw [hfp]; simp [meth_getCommitInst, M_mkFIFO.meth_first, hq]
  · simp [M_mktop_pipelined.Spec.meth_RDY_getCommitInst, hex1, hout]
  · simp [meth_getCommitInst, M_mkFIFO.meth_deq, hq, σ']
  · show i.e2w.queue = _; rw [he2w]; simp only [eD]
  · rw [eIdx]; exact hidx
  · show i.fromDmem.queue = _; rw [hP1]; simp only [eR]
  · show i.dreq.queue = _; rw [hP2]; simp only [eD]
  · show i.dMem.readResult = _; rw [hR]; simp only [eV]
  · show i.toDmem.queue = _; rw [hP3]; simp only [eD]
  · show i.dMem.memory = _; rw [hmemc, eDm]
  · exact Front_congr hfr (fun t => eD _ _) (fun t => eF _ _) (fun t => eMis _) (fun t => eP _)

-- ─── The simulation ────────────────────────────────────────────────────

theorem R_rule {i i' : state} {s : SState} (h : R i s) (hr : ImplModule.getARule i i') : R i' s := by
  obtain ⟨r, hr⟩ := hr
  cases r <;> dsimp only [ImplModule, Module.getRule, ofRule] at hr <;>
    obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp hr
  · exact R_requestI h hg
  · exact R_responseI h hg
  · exact R_requestD h hg
  · exact R_responseD h hg
  · exact R_decode h hg
  · exact R_execute h hg
  · exact R_writeback h hg

theorem R_rules {i i' : state} {s : SState} (h : R i s) (hr : trans_refl ImplModule.getARule i i') :
    R i' s := by
  induction hr with
  | refl => exact h
  | step hab _ ih => exact ih (R_rule h hab)

theorem R_method {i i' : state} {s : SState} {e : Event Method} (h : R i s)
    (hm : ImplModule.getMethod i e i') : ∃ s', SpecNS.getMethod s e s' ∧ R i' s' := by
  obtain ⟨name, fp⟩ := e
  cases name
  · -- every fetch, real or stuttering, is one ISA step
    refine ⟨stepOne s, ⟨Unit_, rfl, ?_, rfl⟩, ?_⟩ <;>
      dsimp only [ImplModule, Module.getMethod, orStutter0, ofAVMethod0] at hm <;>
      rcases hm with ⟨v, hv, hfp, -⟩ | ⟨hfp, rfl⟩
    · rw [hfp]
    · exact hfp
    · obtain rfl : i' = (meth_doFetch i).avAction_ := (congrArg (·.avAction_) hv).symm
      exact R_doFetch h
    · exact R_stutter h
  · exact R_getCommitInst h hm

/-- `R` is a forward simulation: every run of the pipeline is matched, from an `R`-related state, by
a method-only run of the stutter-free ISA spec over the same trace. -/
theorem simulation {i i' : state} {s : SState} {l : List (Event Method)} :
    R i s → star_extend ImplModule.getARule ImplModule.getMethod i l i' →
    ∃ s', star SpecNS.getMethod s l s' ∧ R i' s' := by
  intro h hi
  induction hi with
  | refl => exact ⟨s, .refl _, h⟩
  | step_int _ _ _ _ htr ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih
    exact ⟨s₁, hs₁, R_rules h₁ htr⟩
  | step_ext _ _ _ _ _ hm ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih
    obtain ⟨s₂, hs₂, h₂⟩ := R_method h₁ hm
    exact ⟨s₂, .step _ _ _ _ _ hs₁ hs₂, h₂⟩

-- ─── Trace inclusion ───────────────────────────────────────────────────

/-- The pipeline (with its stuttering fetch) refines the stutter-free ISA spec. -/
theorem trace_inclusion (l : List (Event Method)) (i : ImplModule.State) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    spec_behaviour SpecNS.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SState) := by
  rintro ⟨i', hi⟩
  obtain ⟨s', hs', -⟩ := simulation (R_init i h halted) hi
  exact ⟨s', hs'⟩

/-- The pipeline without the `doFetch` stutter. -/
def ImplNS : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.state
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.meth_doFetch M_mktop_pipelined.meth_RDY_doFetch
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules := ImplModule.rules

theorem star_SpecNS {s s' : SState} {l : List (Event Method)} :
    star SpecNS.getMethod s l s' → star SpecModule.getMethod s l s' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step _ _ _ e _ hm ih =>
    refine .step _ _ _ _ _ ih ?_
    obtain ⟨_ | _, fp⟩ := e
    · exact Or.inl hm
    · exact hm

theorem star_extend_ImplNS {i i' : state} {l : List (Event Method)} :
    star_extend ImplNS.getARule ImplNS.getMethod i l i' →
    star_extend ImplModule.getARule ImplModule.getMethod i l i' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step_int _ _ _ _ htr ih => exact .step_int _ _ _ _ ih htr
  | step_ext _ _ _ e _ hm ih =>
    refine .step_ext _ _ _ _ _ ih ?_
    obtain ⟨_ | _, fp⟩ := e
    · exact Or.inl hm
    · exact hm

/-- Neither side stutters. -/
theorem trace_inclusion_ns (l : List (Event Method)) (i : state) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplNS.getARule ImplNS.getMethod l i →
    spec_behaviour SpecNS.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SState) :=
  fun ⟨i', hi⟩ => trace_inclusion l i h halted ⟨i', star_extend_ImplNS hi⟩

/-- The statement of `Refines.trace_inclusion` (both sides stuttering), re-proved directly. -/
theorem trace_inclusion_orig (l : List (Event Method)) (i : ImplModule.State) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    spec_behaviour SpecModule.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SpecModule.State) := by
  intro hi
  obtain ⟨s', hs'⟩ := trace_inclusion l i h halted hi
  exact ⟨s', star_SpecNS hs'⟩

#print axioms simulation
#print axioms trace_inclusion
#print axioms trace_inclusion_ns
#print axioms trace_inclusion_orig

end M_mktop_pipelined.Refines.Sim
