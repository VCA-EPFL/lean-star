import Star.Bluespec.SimpleProcessor.mktop_pipelined_spec
import Star.Bluespec.SimpleProcessor.core_step_lemmas
open BluespecPrelude BluespecVerification ReachingStar Bluespec Params_types M_mktop_pipelined

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

-- FULL fetch/execute commuting theorem: 3 cases total (not 8!), since
-- `hmi` turns out to be unnecessary -- `rule_RL_execute_core_normal_branch`
-- leaves isMemInst symbolic, and the pc/eEp outcome is driven purely by
-- pcMismatch regardless of mem-ness (a memory instruction can never
-- actually trigger the "taken branch" case in practice, but Lean can't
-- assume that without a reachability argument, so leaving isMemInst
-- unresolved and splitting only on pcMismatch handles the adversarial
-- "mem + redirect" case for free, with no extra proof burden).
example {a b c : ImplModule.State} :
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
