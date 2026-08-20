-- RVUtil_rv_irrelevance.lean -- imported by mktop_pipelined_spec.lean.
--
-- Helper lemmas needed by `reach_flush_again_meth_getCommit`'s pipeline-vs-ISA
-- equivalence argument: `decodeD2eNormal`/`executeAt` zero rv1/rv2 whenever an
-- operand is architecturally unused (not just for x0), unlike `Spec.stepOne`,
-- which only zeros for x0 -- these lemmas show `execALU32`/`execControl32`
-- don't actually depend on that stray rv1/rv2 value in that case, so the
-- discrepancy is harmless. (Originally written targeting
-- commutes_rule_RL_decode_rule_RL_writeback, which ended up closing a
-- different way -- reused here instead.)
--
-- BACKGROUND: decode always stores rv1/rv2 (raw rf reads) into its d2e output
-- unconditionally, even for instructions that don't validly use rs1/rs2
-- (usesRS1/usesRS2 = false). When writeback and decode fire in different
-- orders, decode can end up reading a different (but architecturally
-- irrelevant) rf value at that register, making the two resulting d2e states
-- literally unequal even though they're semantically equivalent. These
-- lemmas show that execute's *output* doesn't actually depend on that stray
-- rv1/rv2 value for any properly-encoded RV32I instruction -- except
-- SYSTEM-class and other reserved/undefined opcodes with bit2(inst)=0, which
-- this simplified core's pipeline never gates out (isLegalInstruction is
-- computed by the decoder but checked nowhere in the pipeline itself -- see
-- mktop_pipelined.lean / RVUtil.lean).
--
-- STATUS: all four lemmas below (execALU32_rv1_irrelevant, execALU32_rv2_irrelevant,
-- execControl32_rv1_irrelevant, execControl32_rv2_irrelevant) are fully proven.

import Star.Bluespec.Basic
import Star.Bluespec.SimpleProcessor.core_step_lemmas
open BluespecPrelude Params_types M_mktop_pipelined

set_option maxHeartbeats 4000000

theorem bv1_ne_one_eq_zero (x : BitVec 1) (h : x ≠ 1) : x = 0 := by bv_decide

theorem bool_or_true_iff (a b : t_bool) : bool_or a b = BTrue Unit_ ↔ a = BTrue Unit_ ∨ b = BTrue Unit_ := by
  cases a <;> cases b <;> simp [bool_or]

theorem tbool_ite_true_iff (b : Bool) : (if b then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ ↔ b = true := by
  cases b <;> simp

theorem extract_bits_eq_extractLsb' {n : Nat} (x : BitVec n) (high low : Nat) :
    extract_bits x high low = BitVec.extractLsb' low (high - low + 1) x := rfl

theorem extract_bit_eq_extractLsb' {n : Nat} (x : BitVec n) (idx : Nat) :
    extract_bit x idx = BitVec.extractLsb' idx 1 x := rfl

-- `isMemoryInst` (a loose bit-pattern check: bit6=0, bits[4:3]=00) admits two
-- op5 patterns beyond LOAD/STORE proper -- LOAD-FP (00001) and STORE-FP
-- (01001) -- which this core doesn't implement and `isLegalInstruction` never
-- classifies as legal (it only recognizes LOAD/OPIMM/AUIPC/STORE/OP/LUI/
-- BRANCH/JALR/JAL/SYSTEM, none of which share an op5 with LOAD-FP/STORE-FP).
-- So under legality, `isMemoryInst` really is LOAD-or-STORE, both of which
-- `usesRS1` lists directly -- needed since decode's `decodeD2eNormal` and
-- spec's `Spec.stepOne` must agree on rv1 for the memory-address computation,
-- which only holds unconditionally when `valid_rs1` is true (see file header).
theorem legal_mem_implies_usesRS1 (inst : BitVec 32)
    (hlegal : RVUtil.isLegalInstruction inst = BTrue Unit_)
    (hmem : RVUtil.isMemoryInst (RVUtil.decodeInst inst) = BTrue Unit_) :
    RVUtil.usesRS1 inst = BTrue Unit_ := by
  unfold RVUtil.isLegalInstruction RVUtil.isMultiplyInst RVUtil.getInstFields RVUtil.isMemoryInst
    RVUtil.decodeInst RVUtil.usesRS1 RVUtil.op_LOAD RVUtil.op_OPIMM RVUtil.op_AUIPC RVUtil.op_STORE
    RVUtil.op_OP RVUtil.op_LUI RVUtil.op_BRANCH RVUtil.op_JALR RVUtil.op_JAL RVUtil.op_SYSTEM at *
  dsimp only at *
  rw [bool_or_true_iff] at hlegal
  simp only [tbool_ite_true_iff] at hlegal hmem ⊢
  revert hlegal hmem
  simp only [extract_bits_eq_extractLsb', extract_bit_eq_extractLsb', beq_iff_eq]
  bv_decide

-- execALU32 special-cases LUI/AUIPC (bit2(inst)=1) before ever touching
-- rs1_val, so bit2=1 alone is enough to guarantee rv1-independence.
theorem execALU32_rv1_irrelevant (inst rv1 rv1' rv2 imm pc : BitVec 32)
    (hb2 : extract_bit inst 2 = (1 : BitVec 1)) :
    RVUtil.execALU32 inst rv1 rv2 imm pc = RVUtil.execALU32 inst rv1' rv2 imm pc := by
  unfold RVUtil.execALU32
  dsimp only
  rw [hb2]
  by_cases hb5 : extract_bit inst 5 = (1 : BitVec 1)
  · simp [hb5]
  · simp [hb5, bv1_ne_one_eq_zero _ hb5]

theorem execALU32_rv2_irrelevant (inst rv1 rv2 rv2' imm pc : BitVec 32)
    (hb : extract_bit inst 2 = (1 : BitVec 1) ∨ extract_bit inst 5 = (0 : BitVec 1)) :
    RVUtil.execALU32 inst rv1 rv2 imm pc = RVUtil.execALU32 inst rv1 rv2' imm pc := by
  unfold RVUtil.execALU32
  dsimp only
  rcases hb with hb2 | hb5
  · rw [hb2]
    by_cases hb5 : extract_bit inst 5 = (1 : BitVec 1)
    · simp [hb5]
    · simp [hb5, bv1_ne_one_eq_zero _ hb5]
  · by_cases hb2 : extract_bit inst 2 = (1 : BitVec 1) ∧ extract_bit inst 5 = (1 : BitVec 1)
    · exact absurd (hb2.2.symm.trans hb5) (by decide)
    · by_cases hb2' : extract_bit inst 2 = (1 : BitVec 1) ∧ extract_bit inst 5 = (0 : BitVec 1)
      · simp [hb2'.1, hb2'.2]
      · simp only [hb2, hb2', if_false, hb5, if_true, BitVec.zero_and, BEq.beq, decide_true]

-- execControl32 uses rv1 only for JALR (bits[6:4]=110, bit3=0), which is
-- excluded here via usesRS1 (JALR's exact bit pattern uniquely pins
-- usesRS1=true, unlike the bit2=0 "branch-like" reserved-opcode case, which
-- bit2=1 already rules out).
theorem execControl32_rv1_irrelevant (inst rv1 rv1' rv2 imm pc : BitVec 32)
    (hb2 : extract_bit inst 2 = (1 : BitVec 1)) (hv1 : RVUtil.usesRS1 inst ≠ BTrue Unit_) :
    RVUtil.execControl32 inst rv1 rv2 imm pc = RVUtil.execControl32 inst rv1' rv2 imm pc := by
  unfold RVUtil.execControl32
  dsimp only
  by_cases hcontrol : extract_bits inst 6 4 = (6 : BitVec 3)
  · have hb3 : extract_bit inst 3 = (1 : BitVec 1) := by
      by_contra hb3'
      have hb3 : extract_bit inst 3 = (0 : BitVec 1) := bv1_ne_one_eq_zero _ hb3'
      apply hv1
      unfold RVUtil.usesRS1
      dsimp only
      split
      · rfl
      · exfalso
        rename_i hb
        simp only [Bool.not_eq_true, extract_bits_eq_extractLsb', extract_bit_eq_extractLsb'] at hb hb2 hb3 hcontrol
        revert hb hb2 hb3 hcontrol
        bv_decide
    simp only [hcontrol, if_true]
    simp [hb2, hb3]
  · split
    · rfl
    · rename_i h
      exact absurd (by simpa using h : extract_bits inst 6 4 = (6 : BitVec 3)) hcontrol

-- execControl32 uses rv2 only in the branch-resolution ("else") computation,
-- which requires bit2=0 to reach at all (JAL/JALR both have bit2=1 and never
-- touch rv2) -- so bit2=1 alone suffices, no usesRS2/reserved-opcode
-- exclusion needed here (unlike the rv1 case).
theorem execControl32_rv2_irrelevant (inst rv1 rv2 rv2' imm pc : BitVec 32)
    (hb2 : extract_bit inst 2 = (1 : BitVec 1)) :
    RVUtil.execControl32 inst rv1 rv2 imm pc = RVUtil.execControl32 inst rv1 rv2' imm pc := by
  unfold RVUtil.execControl32
  dsimp only
  by_cases hb3 : extract_bit inst 3 = (1 : BitVec 1)
  · simp [hb2, hb3]
  · simp [hb2, hb3, bv1_ne_one_eq_zero _ hb3]
