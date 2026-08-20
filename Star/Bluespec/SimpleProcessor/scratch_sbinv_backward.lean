-- Scratch experiment: does `SbInv` hold *backwards*, i.e. `SbInv i' → step i i' → SbInv i`?
-- (in addition to the already-landed forward direction in mktop_pipelined_spec.lean)
--
-- Answer: yes, for all four rules. `SbInv` is an *affine* invariant -- every
-- rule's effect on `sb` is either a no-op on the relevant fields, or an exact
-- +delta/-delta update where delta is uniquely determined by the current
-- dInst (not by the pre-state's sb value). That makes the update invertible:
-- knowing the *post*-state value plus the (rule-determined) delta always
-- recovers the *pre*-state value via cancellation. So `SbInv` is really an
-- iff across every single-rule step, not just a preserved-forward invariant.
--
-- Not currently used by anything -- kept here purely as a validated
-- exploration, not landed into mktop_pipelined_spec.lean.
import Star.Bluespec.SimpleProcessor.mktop_pipelined_spec
open BluespecPrelude BluespecVerification ReachingStar Bluespec Params_types M_mktop_pipelined

set_option maxHeartbeats 4000000

theorem SbInv_backward_rule_RL_fetch {i i' : ImplModule.State} (hInv : SbInv i')
    (hr : ImplModule.getRule .rule_RL_fetch i i') : SbInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

theorem SbInv_backward_rule_RL_decode {i i' : ImplModule.State} (hInv : SbInv i')
    (hr : ImplModule.getRule .rule_RL_decode i i') : SbInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
    M_mktop_pipelined.rule_RL_decode_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hsize, hpt⟩ := hInv
  refine ⟨?_, fun r => ?_⟩ <;>
  · generalize hsq :
      bool_or (bool_not (if (i.f2d_element.idEp == i.dEp) = true then BTrue Unit_ else BFalse Unit_))
        (bool_not (if (i.f2d_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_)) = sq at *
    cases sq
    case BTrue a => cases a; dsimp only at hsize hpt ⊢; first | exact hsize | exact hpt r
    case BFalse a =>
      cases a
      dsimp only at hsize hpt ⊢
      have hd2e : i.d2e_hasElement = false := by
        dsimp only [fifo_RDY_enq] at hguard
        simp only [bool_and_true_iff] at hguard
        rcases h : i.d2e_hasElement with _ | _
        · rfl
        · exfalso; simp [h] at hguard
      first
      | (rw [arr_set_size] at hsize; exact hsize)
      | (set instr := M_mkSimpleMem.read i.imem (truncate (shift_right_logical i.f2d_element.pc 2) 30) with hinstr
         set decodedInst := RVUtil.decodeInst instr with hdecodedInst
         set rdIdx := (RVUtil.getInstFields instr).rd with hrdIdx
         have hsize' : i.sb.size = 32 := by rw [arr_set_size] at hsize; exact hsize
         have hbound : rdIdx.toNat < i.sb.size := by rw [hsize']; exact rdIdx.isLt.trans_le (by decide)
         have hdr0 : dInstRd decodedInst = rdIdx := by
           rw [dInstRd, hdecodedInst]; unfold RVUtil.decodeInst; exact hrdIdx.symm
         have hIH := hpt r
         by_cases heq : rdIdx = r
         · subst heq
           rw [arr_get_arr_set_self _ _ _ hbound] at hIH
           rw [hd2e]
           have hzero : sbContrib false i.d2e_element.dInst rdIdx = 0 := rfl
           rw [hzero, zero_add]
           generalize hB : sbContrib i.e2w_hasElement i.e2w_element.dInst rdIdx = B at hIH ⊢
           unfold sbContrib dInstWrites at hIH
           rw [hdr0] at hIH
           generalize hc : (if (rdIdx == (0:BitVec 5)) = true then BTrue Unit_ else BFalse Unit_) = c at hIH
           generalize hleg : decodedInst.legal = leg at hIH
           generalize hvrd : decodedInst.valid_rd = vrd at hIH
           cases leg <;> cases vrd <;> cases c <;>
             simp [bool_and, bool_not, ite_bsv, beq_iff_eq] at hIH <;> bv_decide
         · have hne : rdIdx.toNat ≠ r.toNat := by
             intro h; apply heq; exact BitVec.eq_of_toNat_eq h
           rw [arr_get_arr_set_ne _ _ _ _ hne] at hIH
           rw [hd2e]
           have hzero : sbContrib false i.d2e_element.dInst r = 0 := rfl
           rw [hzero, zero_add]
           have hdrne : dInstRd decodedInst ≠ r := hdr0 ▸ heq
           unfold sbContrib at hIH ⊢
           simp [hdrne, ite_bsv, zero_add] at hIH
           simpa using hIH)

theorem SbInv_backward_rule_RL_execute {i i' : ImplModule.State} (hInv : SbInv i')
    (hr : ImplModule.getRule .rule_RL_execute i i') : SbInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute,
    M_mktop_pipelined.rule_RL_execute_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hsize, hpt⟩ := hInv
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
      dsimp only at hsize hpt ⊢
      first
      | exact hsize
      | (have he2w_old : i.e2w_hasElement = false := by
           dsimp only [fifo_RDY_enq] at hguard
           simp only [bool_and_true_iff] at hguard
           rcases h : i.e2w_hasElement with _ | _
           · rfl
           · exfalso; simp [h] at hguard
         have hIH := hpt r
         have hzero_post : sbContrib false i.d2e_element.dInst r = 0 := rfl
         rw [hzero_post, zero_add] at hIH
         rw [hd2e, he2w_old]
         have hzero_pre : sbContrib false i.e2w_element.dInst r = 0 := rfl
         rw [hzero_pre, add_zero]
         exact hIH)
    case BTrue a =>
      cases a
      dsimp only at hsize hpt ⊢
      first
      | (rw [arr_set_size] at hsize; exact hsize)
      | (have hsize' : i.sb.size = 32 := by rw [arr_set_size] at hsize; exact hsize
         have hbound : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.toNat < i.sb.size := by
           rw [hsize']
           exact (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.isLt.trans_le (by decide)
         have hIH := hpt r
         by_cases heq : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = r
         · subst heq
           rw [arr_get_arr_set_self _ _ _ hbound] at hIH
           have hzero : sbContrib false i.d2e_element.dInst
               (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = 0 := rfl
           rw [hzero, zero_add] at hIH
           rw [hd2e]
           generalize hB : sbContrib i.e2w_hasElement i.e2w_element.dInst
             (RVUtil.getInstFields i.d2e_element.dInst.inst).rd = B at hIH ⊢
           unfold sbContrib dInstWrites dInstRd at ⊢
           generalize hc : (if (RVUtil.getInstFields i.d2e_element.dInst.inst).rd == (0:BitVec 5)
             then BTrue Unit_ else BFalse Unit_) = c at hIH ⊢
           generalize hleg : i.d2e_element.dInst.legal = leg at hIH ⊢
           generalize hvrd : i.d2e_element.dInst.valid_rd = vrd at hIH ⊢
           cases leg <;> cases vrd <;> cases c <;>
             simp [bool_and, bool_not, ite_bsv, beq_iff_eq] at hIH ⊢ <;> bv_decide
         · have hne : (RVUtil.getInstFields i.d2e_element.dInst.inst).rd.toNat ≠ r.toNat := by
             intro h; apply heq; exact BitVec.eq_of_toNat_eq h
           rw [arr_get_arr_set_ne _ _ _ _ hne] at hIH
           have hzero_post : sbContrib false i.d2e_element.dInst r = 0 := rfl
           rw [hzero_post, zero_add] at hIH
           rw [hd2e]
           have hdrne : dInstRd i.d2e_element.dInst ≠ r := heq
           have hzero_true : sbContrib true i.d2e_element.dInst r = 0 := by
             unfold sbContrib; simp [hdrne, ite_bsv]
           rw [hzero_true, zero_add]
           exact hIH)

theorem SbInv_backward_rule_RL_writeback {i i' : ImplModule.State} (hInv : SbInv i')
    (hr : ImplModule.getRule .rule_RL_writeback i i') : SbInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hsize, hpt⟩ := hInv
  have he2w : i.e2w_hasElement = true := by
    dsimp only [fifo_RDY_deq] at hguard
    simp only [bool_and_true_iff] at hguard
    rcases h : i.e2w_hasElement with _ | _
    · exfalso; simp [h] at hguard
    · rfl
  refine ⟨?_, fun r => ?_⟩
  · rw [arr_set_size] at hsize; exact hsize
  · have hsize' : i.sb.size = 32 := by rw [arr_set_size] at hsize; exact hsize
    have hbound : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.toNat < i.sb.size := by
      rw [hsize']
      exact (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.isLt.trans_le (by decide)
    have hIH := hpt r
    by_cases heq : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = r
    · subst heq
      rw [arr_get_arr_set_self _ _ _ hbound] at hIH
      have hzero : sbContrib false i.e2w_element.dInst
          (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = 0 := rfl
      rw [hzero, add_zero] at hIH
      rw [he2w]
      generalize hA : sbContrib i.d2e_hasElement i.d2e_element.dInst
        (RVUtil.getInstFields i.e2w_element.dInst.inst).rd = A at hIH ⊢
      unfold sbContrib dInstWrites dInstRd at ⊢
      generalize hc : (if (RVUtil.getInstFields i.e2w_element.dInst.inst).rd == (0:BitVec 5)
        then BTrue Unit_ else BFalse Unit_) = c at hIH ⊢
      generalize hleg : i.e2w_element.dInst.legal = leg at hIH ⊢
      generalize hvrd : i.e2w_element.dInst.valid_rd = vrd at hIH ⊢
      cases leg <;> cases vrd <;> cases c <;>
        simp [bool_and, bool_not, ite_bsv, beq_iff_eq] at hIH ⊢ <;> bv_decide
    · have hne : (RVUtil.getInstFields i.e2w_element.dInst.inst).rd.toNat ≠ r.toNat := by
        intro h; apply heq; exact BitVec.eq_of_toNat_eq h
      rw [arr_get_arr_set_ne _ _ _ _ hne] at hIH
      have hzero_post : sbContrib false i.e2w_element.dInst r = 0 := rfl
      rw [hzero_post, add_zero] at hIH
      rw [he2w]
      have hdrne : dInstRd i.e2w_element.dInst ≠ r := heq
      have hzero_true : sbContrib true i.e2w_element.dInst r = 0 := by
        unfold sbContrib; simp [hdrne, ite_bsv]
      rw [hzero_true, add_zero]
      exact hIH

theorem SbInv_backward {i i' : ImplModule.State} (hInv : SbInv i')
    (hr : ImplModule.getARule i i') : SbInv i := by
  rcases ImplModule.get_rule_cases hr with h | h | h | h
  · exact SbInv_backward_rule_RL_fetch hInv h
  · exact SbInv_backward_rule_RL_decode hInv h
  · exact SbInv_backward_rule_RL_execute hInv h
  · exact SbInv_backward_rule_RL_writeback hInv h
