import StarExperimental.MSI_trial_dec
import StarExperimental.MSI_trial_old_pp
import StarExperimental.MSI_trial_old_cc
import StarExperimental.MSI_trial_old_pc1
import StarExperimental.MSI_trial_old_pc2

/-!
# `MSI_trial`: i diamanti di `MSI.lean` sollevati ai passi di `MSI_trial`

Per ogni coppia di regole di `MSI_def` il teorema `old_*` (copia di `MSI.lean`) dà il ricongiungimento
con passi di `MSI_def`; qui lo si trasporta ai passi di `MSI_trial` (`step_int_old` in entrata,
`step_int_of_old_*` in uscita) e lo si mette nella forma `DecJoin` di `DecreasingDiagrams`.
I quadrati sono generati meccanicamente; i cammini lunghi e le ripetizioni di una richiesta (che
devono rispettare la guardia nuova) sono dimostrati a mano.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

/-- Sollevamento di `old_downgrade_from_M_rq1_downgrade_from_M_rq2`. -/
theorem peak_downgrade_from_M_rq1_downgrade_from_S_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent .downgrade_from_S_rq1S i₂) s'') :
    DecJoin 1 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_downgrade_from_M_rq2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1`. -/
theorem peak_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₂) s'') :
    DecJoin 1 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq2`. -/
theorem peak_downgrade_from_M_rq1_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 1 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_downgrade_from_M_rq2`. -/
theorem peak_downgrade_from_S_rq1S_downgrade_from_S_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent .downgrade_from_S_rq1S i₂) s'') :
    DecJoin 1 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_downgrade_from_M_rq2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq1`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₂) s'') :
    DecJoin 1 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all1`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all2`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_M_invalid_all {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k₁) i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k₂) i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all1`. -/
theorem peak_upgrade_to_M_invalid_all_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all2`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k₁) i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k₂) i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all1`. -/
theorem peak_invalid_allS_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all2`. -/
theorem peak_invalid_allS_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_upgrade_to_M_invalid_all2`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k₁) i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k₂) i₂) s'') :
    DecJoin 6 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_upgrade_to_M_invalid_all2 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available_rq_data_not_available`. -/
theorem peak_rq_data_not_available_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .rq_data_not_available i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available_rq_data_not_available1`. -/
theorem peak_rq_data_not_available_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available_upgrade_from_I_rs`. -/
theorem peak_rq_data_not_available_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i) s'') :
    DecJoin 2 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available_upgrade_from_I_rsS`. -/
theorem peak_rq_data_not_available_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i) s'') :
    DecJoin 2 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available_downgrade_from_M_rs1`. -/
theorem peak_rq_data_not_available_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available1_rq_data_not_available1`. -/
theorem peak_ld_rq_data_not_availableS_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available1_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available1_upgrade_from_I_rs`. -/
theorem peak_ld_rq_data_not_availableS_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i) s'') :
    DecJoin 2 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available1_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available1_upgrade_from_I_rsS`. -/
theorem peak_ld_rq_data_not_availableS_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i) s'') :
    DecJoin 2 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available1_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_rq_data_not_available1_downgrade_from_M_rs`. -/
theorem peak_ld_rq_data_not_availableS_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_rq_data_not_available1_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rs_upgrade_from_I_rs`. -/
theorem peak_upgrade_from_I_rs_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rs v₁) i) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v₂) i) s'') :
    DecJoin 3 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rs_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rs_upgrade_from_I_rsS`. -/
theorem peak_upgrade_from_I_rs_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rs v₁) i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v₂) i) s'') :
    DecJoin 3 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rs_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rs_downgrade_from_M_rs`. -/
theorem peak_upgrade_from_I_rs_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rs v) i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 3 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rs_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rs_downgrade_from_M_rs1`. -/
theorem peak_upgrade_from_I_rs_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rs v) i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 3 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rs_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rsS_upgrade_from_I_rsS`. -/
theorem peak_upgrade_from_I_rsS_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rsS v₁) i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v₂) i) s'') :
    DecJoin 3 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rsS_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rsS_downgrade_from_M_rs`. -/
theorem peak_upgrade_from_I_rsS_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rsS v) i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 3 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rsS_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_from_I_rsS_downgrade_from_M_rs1`. -/
theorem peak_upgrade_from_I_rsS_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache (.upgrade_from_I_rsS v) i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 3 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_from_I_rsS_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rs_downgrade_from_M_rs1`. -/
theorem peak_downgrade_from_M_rs_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .downgrade_from_M_rs i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rs_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_cache hc ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_rq_data_not_available`. -/
theorem peak_downgrade_from_M_rq1_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_rq_data_not_available1`. -/
theorem peak_downgrade_from_M_rq1_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_from_I_rs`. -/
theorem peak_downgrade_from_M_rq1_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v₁) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v₂) i₂) s'') :
    DecJoin 1 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_from_I_rsS`. -/
theorem peak_downgrade_from_M_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v₁) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v₂) i₂) s'') :
    DecJoin 1 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_downgrade_from_M_rs`. -/
theorem peak_downgrade_from_M_rq1_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_downgrade_from_M_rs1`. -/
theorem peak_downgrade_from_M_rq1_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq1_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_rq_data_not_available`. -/
theorem peak_downgrade_from_S_rq1S_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_rq_data_not_available1`. -/
theorem peak_downgrade_from_S_rq1S_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_from_I_rs`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 1 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_from_I_rsS`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 1 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_downgrade_from_M_rs`. -/
theorem peak_downgrade_from_S_rq1S_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_downgrade_from_M_rs1`. -/
theorem peak_downgrade_from_S_rq1S_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 1 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_rq_data_not_available`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_rq_data_not_available1`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 4 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 4 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_rq_data_not_available`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_rq_data_not_available1`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 4 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rsS`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 4 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs1`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 4 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_rq_data_not_available`. -/
theorem peak_upgrade_to_M_invalid_all_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_rq_data_not_available1`. -/
theorem peak_upgrade_to_M_invalid_all_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_from_I_rs`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_from_I_rsS`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_downgrade_from_M_rs`. -/
theorem peak_upgrade_to_M_invalid_all_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_downgrade_from_M_rs1`. -/
theorem peak_upgrade_to_M_invalid_all_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_rq_data_not_available`. -/
theorem peak_invalid_allS_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_rq_data_not_available1`. -/
theorem peak_invalid_allS_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_from_I_rs`. -/
theorem peak_invalid_allS_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_from_I_rsS`. -/
theorem peak_invalid_allS_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_downgrade_from_M_rs`. -/
theorem peak_invalid_allS_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_downgrade_from_M_rs1`. -/
theorem peak_invalid_allS_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all1_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_rq_data_not_available`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_rq_data_not_available {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_rq_data_not_available (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_rq_data_not_available1`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_ld_rq_data_not_availableS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_rq_data_not_available1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_upgrade_from_I_rs`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_upgrade_from_I_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_upgrade_from_I_rsS`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 6 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_upgrade_from_I_rsS (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_downgrade_from_M_rs`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_downgrade_from_M_rs (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_downgrade_from_M_rs1`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 6 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_invalid_all2_downgrade_from_M_rs1 (step_int_old h1 (by simp [IEvent.isDrop, CEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hb ⟨nofun, nofun⟩) (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

end MSITrial
