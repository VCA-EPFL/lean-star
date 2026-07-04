-- core_step_lemmas.lean -- clean, closed-form equations for `rule_RL_execute_core`
-- and `rule_RL_decode_core` under specific fire conditions.
--
-- MOTIVATION: these `_core` functions are built from chains of
-- `match _ : <t_bool expr> with | BTrue _ => .. | BFalse _ => ..`, i.e.
-- *dependent* matches (Lean's `match h : e with` binds a proof `h : e = pat`
-- even when the name is `_`). Once such a term is buried inside a `let`
-- inside a state record used downstream by further rules (e.g. execute's
-- output eEp gets fed into decode's own epoch-mismatch match), `rw`/`simp`
-- can no longer rewrite the shared discriminant in place: the tactic must
-- reconstruct a motive that abstracts every occurrence simultaneously, and
-- that motive is ill-typed as soon as one occurrence sits inside another
-- dependent match's proof-carrying scrutinee (confirmed empirically: `rw`
-- fails with "motive is not type correct" on exactly this shape).
--
-- FIX: prove the resolved output as a *standalone equation* -- a plain
-- function-application rewrite, with no surrounding match -- so that once
-- applied at a call site (before further unfolding), the `let`-bound tuple
-- destructuring downstream just sees concrete literal fields (iota-reduces
-- trivially, no dependent match survives).
import Star.Bluespec.SimpleProcessor.mktop_pipelined
open BluespecPrelude Params_types M_mktop_pipelined

theorem beq_eq_false_iff_ne'' {α} [BEq α] [LawfulBEq α] (x y : α) : (x == y) = false ↔ x ≠ y := by
  simp [beq_iff_eq]

-- `rule_RL_execute_core`'s output when: the d2e entry's epoch matches (no
-- squash), the instruction is not a memory op (so `dmem` is untouched), and
-- the branch/jump target disagrees with the speculated `ppc` (a taken,
-- mispredicted branch/jump).
theorem rule_RL_execute_core_taken_branch
    (d2eElement : t_d2e) (eEp : BitVec 1) (sb : Array (BitVec 2))
    (pc : BitVec 32) (dmem : Array (BitVec 32)) (e2wElement : t_e2w)
    (d2eHasElement e2wHasElement : Bool)
    (hieEp : d2eElement.ieEp = eEp)
    (hmi : RVUtil.isMemoryInst d2eElement.dInst ≠ BTrue Unit_)
    (hpcm : ¬ (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
        (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC = d2eElement.ppc) :
    M_mktop_pipelined.rule_RL_execute_core d2eElement eEp sb pc dmem e2wElement
        d2eHasElement e2wHasElement =
    (bool_and (fifo_RDY_deq d2eHasElement)
       (bool_and (fifo_RDY_deq d2eHasElement) (fifo_RDY_enq e2wHasElement)),
     sb, dmem, eEp + (-1 : BitVec 1),
     (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
        (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC,
     true,
     { data := ite_bsv (RVUtil.isControlInst d2eElement.dInst) (d2eElement.pc + 4)
         (RVUtil.execALU32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
           (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc),
       dInst := d2eElement.dInst, pc := d2eElement.pc }) := by
  have h1 : bool_not (if d2eElement.ieEp == eEp then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
    simp only [hieEp]; simp; rfl
  have h2 : RVUtil.isMemoryInst d2eElement.dInst = BFalse Unit_ := by
    cases h : RVUtil.isMemoryInst d2eElement.dInst
    · exact absurd h hmi
    · rfl
  have h3 : bool_not (if (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
        (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC == d2eElement.ppc
        then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ := by
    have hne : ((RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
        (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC == d2eElement.ppc) = false :=
      beq_eq_false_iff_ne'' _ _ |>.mpr hpcm
    rw [hne]; rfl
  unfold M_mktop_pipelined.rule_RL_execute_core
  dsimp only
  rw [h1, h2, h3]
  simp [ite_bsv, bool_and]

-- `rule_RL_execute_core`'s output when the d2e entry's epoch is stale
-- (squash): the instruction never really executes, so only `sb` (releasing
-- its scoreboard reservation) changes -- `dmem`/`eEp`/`pc`/`e2w` are all
-- untouched, regardless of whether the (never-executed) instruction was a
-- memory op or a taken branch.
theorem rule_RL_execute_core_squash_branch
    (d2eElement : t_d2e) (eEp : BitVec 1) (sb : Array (BitVec 2))
    (pc : BitVec 32) (dmem : Array (BitVec 32)) (e2wElement : t_e2w)
    (d2eHasElement e2wHasElement : Bool)
    (hieEpNe : d2eElement.ieEp ≠ eEp) :
    M_mktop_pipelined.rule_RL_execute_core d2eElement eEp sb pc dmem e2wElement
        d2eHasElement e2wHasElement =
    (bool_and (fifo_RDY_deq d2eHasElement) (bool_and (fifo_RDY_deq d2eHasElement) (BTrue Unit_)),
     arr_set sb ((RVUtil.getInstFields d2eElement.dInst.inst).rd.toNat)
       (arr_get sb ((RVUtil.getInstFields d2eElement.dInst.inst).rd.toNat) +
         ite_bsv (bool_and d2eElement.dInst.valid_rd
             (bool_not (if (RVUtil.getInstFields d2eElement.dInst.inst).rd == (0 : BitVec 5)
               then BTrue Unit_ else BFalse Unit_)))
           (-1 : BitVec 2) (0 : BitVec 2)),
     dmem, eEp, pc, e2wHasElement, e2wElement) := by
  have h1 : bool_not (if d2eElement.ieEp == eEp then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ := by
    have hne : (d2eElement.ieEp == eEp) = false := beq_eq_false_iff_ne'' _ _ |>.mpr hieEpNe
    rw [hne]; rfl
  unfold M_mktop_pipelined.rule_RL_execute_core
  dsimp only
  rw [h1]

-- `rule_RL_execute_core`'s output when the d2e entry's epoch matches (no
-- squash), leaving everything downstream of `isMemInst`/`pcMismatch`
-- symbolic (unresolved) -- covers both remaining fetch/execute cases
-- (memory instruction; correctly-predicted branch/ALU instruction)
-- uniformly, since both only need the *outer* ieEpMismatch match resolved.
-- Named (not re-elaborated per call site) so that two separate uses of this
-- lemma at different states -- e.g. comparing `execute` fired on two states
-- that agree on `d2eElement`/`dmem` -- talk about *the same* term, not two
-- textually-identical-but-distinct `match` elaborations (Lean's equation
-- compiler generates a fresh private matcher per source occurrence, so
-- retyping "the same" match expression at a second call site produces a
-- term `rw`/`rfl` won't recognize as equal to the first).
def execDmemNormal (d2eElement : t_d2e) (dmem : Array (BitVec 32)) : Array (BitVec 32) :=
  match _ : bool_and (RVUtil.isMemoryInst d2eElement.dInst)
      (if extract_bit d2eElement.dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_) with
  | BTrue _ => M_mkSimpleMem.write dmem (extract_bits (d2eElement.rv1 + RVUtil.getImmediate d2eElement.dInst) 31 2)
      (shift_left d2eElement.rv2 (concat_bits (extract_bits (d2eElement.rv1 + RVUtil.getImmediate d2eElement.dInst) 1 0) 3 (0 : BitVec 3)))
  | BFalse _ => dmem

def execDataNormal (d2eElement : t_d2e) (dmem : Array (BitVec 32)) : BitVec 32 :=
  ite_bsv (RVUtil.isMemoryInst d2eElement.dInst)
    (M_mktop_pipelined.processMem
      { isUnsigned := bitvec1_to_bool (extract_bit (RVUtil.getInstFields d2eElement.dInst.inst).funct3 2),
        size := extract_bits (RVUtil.getInstFields d2eElement.dInst.inst).funct3 1 0,
        offset := extract_bits (d2eElement.rv1 + RVUtil.getImmediate d2eElement.dInst) 1 0 }
      (M_mkSimpleMem.read (execDmemNormal d2eElement dmem)
        (extract_bits (d2eElement.rv1 + RVUtil.getImmediate d2eElement.dInst) 31 2)))
    (ite_bsv (RVUtil.isControlInst d2eElement.dInst) (d2eElement.pc + 4)
      (RVUtil.execALU32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
        (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc))

theorem rule_RL_execute_core_normal_branch
    (d2eElement : t_d2e) (eEp : BitVec 1) (sb : Array (BitVec 2))
    (pc : BitVec 32) (dmem : Array (BitVec 32)) (e2wElement : t_e2w)
    (d2eHasElement e2wHasElement : Bool)
    (hieEp : d2eElement.ieEp = eEp) :
    M_mktop_pipelined.rule_RL_execute_core d2eElement eEp sb pc dmem e2wElement
        d2eHasElement e2wHasElement =
    (bool_and (fifo_RDY_deq d2eHasElement) (bool_and (fifo_RDY_deq d2eHasElement) (fifo_RDY_enq e2wHasElement)),
     sb, execDmemNormal d2eElement dmem,
     eEp + ite_bsv (bool_not (if (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
           (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC == d2eElement.ppc then BTrue Unit_ else BFalse Unit_))
       (-1 : BitVec 1) (0 : BitVec 1),
     ite_bsv (bool_not (if (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
           (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC == d2eElement.ppc then BTrue Unit_ else BFalse Unit_))
       (RVUtil.execControl32 d2eElement.dInst.inst d2eElement.rv1 d2eElement.rv2
         (RVUtil.getImmediate d2eElement.dInst) d2eElement.pc).nextPC pc,
     true,
     { data := execDataNormal d2eElement dmem, dInst := d2eElement.dInst, pc := d2eElement.pc }) := by
  have h1 : bool_not (if d2eElement.ieEp == eEp then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
    simp only [hieEp]; simp; rfl
  unfold M_mktop_pipelined.rule_RL_execute_core execDmemNormal execDataNormal
  dsimp only
  rw [h1]
  rfl

-- `rule_RL_decode_core`'s output on the *epoch-mismatch squash* branch: the
-- queued f2d entry's idEp matches `dEp`, but its ieEp disagrees with the
-- current `eEp` (a stale entry issued before a since-resolved branch
-- redirect) -- so the instruction is dropped without touching
-- `sb`/`d2e`/`pc`/`dEp`/`halt`, regardless of the scoreboard/operand-
-- readiness state and regardless of whether the (never-issued) instruction
-- would otherwise have been legal or not (`newHalt` only ever differs from
-- `halt` on the *non*-squash path -- see rule_RL_decode_core). Note this no
-- longer depends on `imem`'s contents at all (only `f2dElement`'s epoch
-- tags), since the fetched instruction is discarded either way.
theorem rule_RL_decode_core_squash_branch
    (imem : Array (BitVec 32)) (f2dElement : t_f2d) (dEp eEp : BitVec 1)
    (sb : Array (BitVec 2)) (rf : Array (BitVec 32)) (pc : BitVec 32) (d2eElement : t_d2e)
    (halt : Bool) (f2dHasElement d2eHasElement : Bool)
    (hidEp : f2dElement.idEp = dEp)
    (hieEpNe : f2dElement.ieEp ≠ eEp) :
    M_mktop_pipelined.rule_RL_decode_core imem f2dElement dEp eEp sb rf pc d2eElement
        halt f2dHasElement d2eHasElement =
    (bool_and (fifo_RDY_deq f2dHasElement)
      (bool_and (BTrue Unit_)
        (bool_and (fifo_RDY_deq f2dHasElement) (BTrue Unit_))),
     pc, dEp, d2eHasElement, d2eElement, sb, halt) := by
  have h1 : bool_not (if f2dElement.idEp == dEp then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
    simp only [hidEp]; simp; rfl
  have h2 : bool_not (if f2dElement.ieEp == eEp then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ := by
    have hne : (f2dElement.ieEp == eEp) = false := by
      simp only [beq_eq_false_iff_ne'']; exact hieEpNe
    rw [hne]; rfl
  unfold M_mktop_pipelined.rule_RL_decode_core
  dsimp only
  rw [h1, h2]
  simp [bool_or]
