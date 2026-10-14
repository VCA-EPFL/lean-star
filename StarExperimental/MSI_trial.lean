import StarExperimental.MSI_trial_peaks_lift
import StarExperimental.MSI_trial_peaks_req
import StarExperimental.MSI_trial_peaks_long
import StarExperimental.MSI_trial_peaks_new
import StarExperimental.MSI_trial_peaks_dropA
import StarExperimental.MSI_trial_peaks_dropB
import StarExperimental.MSI_trial_peaks_ne

/-!
# `MSI_trial`: confluenza dei passi interni sugli stati raggiungibili, **senza terminazione**

`has_diamond_property_on Reach (trans_refl (rule n))` per `MSI_trial`, dal teorema dei diagrammi
decrescenti (`DecreasingDiagrams.has_diamond_property_on_of_decreasing`) e dai 153 picchi locali
(`MSI_trial_peaks_*.lean`), senza alcun invariante: l'unica informazione sugli stati raggiungibili è
l'irraggiungibilità delle viste cattive, trovata dalla tattica backward (`MSI_trial_views.lean`).

`local_peak` smista ogni coppia di passi interni sul suo teorema; `decreasing` impacchetta le tre
ipotesi di `DecreasingDiagrams.Decreasing`; `msi_trial_confluent` è il risultato.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl has_diamond_property_on)
open DecreasingDiagrams (big lt)

namespace MSITrial

variable {n : Nat}

/-- La forma `DecJoin ∨ = ∨ ¬Reach` è simmetrica. -/
theorem peak_symm {α β : Nat} {s s' s'' : MSIState n}
    (h : DecJoin β α s'' s' ∨ s'' = s' ∨ ¬ Reach s) : DecJoin α β s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h)

/-- Gli eventi del parent che non etichettano nessuna regola non danno passi. -/
theorem no_step_junk {s s' : MSIState n} {e : ParentUpdQueueInternalEvent n} {i : Fin n}
    (he : e = .invalid_allM ∨ e = .dawngrade_safe_parent_rq1 ∨ e = .dawngrade_safe_parent_rq1S)
    (h : step_int s (.parent e i) s') : False := by
  cases h with
  | parent_upd_queue _ _ _ hp =>
      rcases he with rfl | rfl | rfl <;> cases hp

/-- Due passi di cache su indici diversi: il quadrato, in forma `DecJoin`. -/
theorem peak_cache_ne_dec {s s' s'' : MSIState n} {c₁ c₂ : CEvent} {i₁ i₂ : Fin n} (hii : ¬ i₁ = i₂)
    (h1 : step_int s (.cache c₁ i₁) s') (h2 : step_int s (.cache c₂ i₂) s'') :
    DecJoin (lab (.cache c₁ i₁)) (lab (.cache c₂ i₂)) s' s'' := by
  obtain ⟨d, hc, hb⟩ := peak_cache_ne hii h1 h2
  exact DecJoin.square hb hc rfl rfl

/-- **Ogni picco locale di `MSI_trial` è decrescente**, o i due passi coincidono, o lo stato non è
raggiungibile. Smistamento sulle coppie di eventi. -/
theorem local_peak {s s' s'' : MSIState n} {e₁ e₂ : IEvent n}
    (h1 : step_int s e₁ s') (h2 : step_int s e₂ s'') :
    DecJoin (lab e₁) (lab e₂) s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases e₁ with
  | cache c₁ i₁ =>
    cases e₂ with
    | cache c₂ i₂ =>
      cases c₁ with
      | rq_data_not_available =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_rq_data_not_available h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_ld_rq_data_not_availableS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_upgrade_from_I_rq h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_rq_data_not_available_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_rq_data_not_available h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_rq_data_not_available h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | ld_rq_data_not_availableS =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_ld_rq_data_not_availableS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_ld_rq_data_not_availableS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_upgrade_from_I_rq h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_ld_rq_data_not_availableS_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_ld_rq_data_not_availableS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_ld_rq_data_not_availableS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | upgrade_from_I_rq =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_upgrade_from_I_rq h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_upgrade_from_I_rq h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_upgrade_from_I_rq h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rq_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_upgrade_from_I_rq h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_upgrade_from_I_rq h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | upgrade_from_I_rqS =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_upgrade_from_I_rqS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_upgrade_from_I_rqS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rq_upgrade_from_I_rqS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rqS_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rqS_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rqS_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rqS_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rqS_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_upgrade_from_I_rqS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_upgrade_from_I_rqS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | upgrade_from_I_rs v₁ =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rq_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rqS_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rs_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rs_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rs_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rs_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_upgrade_from_I_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | upgrade_from_I_rsS v₁ =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rq_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rqS_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rs_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rsS_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rsS_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_upgrade_from_I_rsS_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_upgrade_from_I_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | downgrade_from_M_rs =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rq_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rqS_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rs_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rsS_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_downgrade_from_M_rs_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_downgrade_from_M_rs_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_downgrade_from_M_rs h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | downgrade_from_S_rsS =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_rq_data_not_available_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_ld_rq_data_not_availableS_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rq_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rqS_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rs_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_upgrade_from_I_rsS_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_downgrade_from_M_rs_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_downgrade_from_S_rsS_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIσ_downgrade_from_S_rsS h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | drop_rqIμ =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_rq_data_not_available h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_ld_rq_data_not_availableS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_upgrade_from_I_rq h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_drop_rqIμ h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIμ_drop_rqIσ h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
      | drop_rqIσ =>
        cases c₂ with
        | rq_data_not_available =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_rq_data_not_available h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | ld_rq_data_not_availableS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_ld_rq_data_not_availableS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rq =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_upgrade_from_I_rq h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rqS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_upgrade_from_I_rqS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rs v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_upgrade_from_I_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | upgrade_from_I_rsS v₂ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_upgrade_from_I_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_M_rs =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_downgrade_from_M_rs h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | downgrade_from_S_rsS =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_downgrade_from_S_rsS h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIμ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_symm (peak_drop_rqIμ_drop_rqIσ h2 h1)
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
        | drop_rqIσ =>
          by_cases hii : i₁ = i₂
          · subst hii
            exact peak_drop_rqIσ_drop_rqIσ h1 h2
          · exact Or.inl (peak_cache_ne_dec hii h1 h2)
    | parent p₂ i₂ =>
      cases c₁ with
      | rq_data_not_available =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_rq_data_not_available h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_rq_data_not_available h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_rq_data_not_available h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_rq_data_not_available h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_rq_data_not_available h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_rq_data_not_available h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_rq_data_not_available h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | ld_rq_data_not_availableS =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_ld_rq_data_not_availableS h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_ld_rq_data_not_availableS h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_ld_rq_data_not_availableS h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_ld_rq_data_not_availableS h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_ld_rq_data_not_availableS h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_ld_rq_data_not_availableS h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_ld_rq_data_not_availableS h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_from_I_rq =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_from_I_rq h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_from_I_rq h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rq h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_upgrade_from_I_rq h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_upgrade_from_I_rq h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rq h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_from_I_rqS =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_from_I_rqS h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_from_I_rqS h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rqS h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rqS h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_upgrade_from_I_rqS h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_upgrade_from_I_rqS h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rqS h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_from_I_rs v₁ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_from_I_rs h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_from_I_rs h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rs h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_upgrade_from_I_rs h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_upgrade_from_I_rs h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rs h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_from_I_rsS v₁ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_from_I_rsS h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_from_I_rsS h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rsS h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_upgrade_from_I_rsS h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_upgrade_from_I_rsS h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rsS h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | downgrade_from_M_rs =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_downgrade_from_M_rs h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_downgrade_from_M_rs h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_M_rs h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_downgrade_from_M_rs h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_downgrade_from_M_rs h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_M_rs h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | downgrade_from_S_rsS =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_downgrade_from_S_rsS h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_downgrade_from_S_rsS h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_downgrade_from_S_rsS h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_S_rsS h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_downgrade_from_S_rsS h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_downgrade_from_S_rsS h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_symm (peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_S_rsS h2 h1)
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | drop_rqIμ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_drop_rqIμ_downgrade_from_M_rq1 h1 h2
        | downgrade_from_S_rq1S =>
          exact peak_drop_rqIμ_downgrade_from_S_rq1S h1 h2
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_drop_rqIμ_upgrade_to_M_data_avilable_rq1 h1 h2
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_drop_rqIμ_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_drop_rqIμ_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_drop_rqIμ_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_drop_rqIμ_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | drop_rqIσ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_drop_rqIσ_downgrade_from_M_rq1 h1 h2
        | downgrade_from_S_rq1S =>
          exact peak_drop_rqIσ_downgrade_from_S_rq1S h1 h2
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_drop_rqIσ_upgrade_to_M_data_avilable_rq1 h1 h2
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_drop_rqIσ_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_drop_rqIσ_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_drop_rqIσ_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_drop_rqIσ_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
  | parent p₁ i₁ =>
    cases e₂ with
    | cache c₂ i₂ =>
      cases p₁ with
      | downgrade_from_M_rq1 v₁ =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_downgrade_from_M_rq1_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_downgrade_from_M_rq1_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_downgrade_from_M_rq1_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_downgrade_from_M_rq1_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_downgrade_from_M_rq1_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_downgrade_from_M_rq1_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_downgrade_from_M_rq1_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_downgrade_from_M_rq1_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_downgrade_from_M_rq1 h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_downgrade_from_M_rq1 h2 h1)
      | downgrade_from_S_rq1S =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_downgrade_from_S_rq1S_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_downgrade_from_S_rq1S_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_downgrade_from_S_rq1S_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_downgrade_from_S_rq1S_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_downgrade_from_S_rq1S_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_downgrade_from_S_rq1S_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_downgrade_from_S_rq1S_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_downgrade_from_S_rq1S_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_downgrade_from_S_rq1S h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_downgrade_from_S_rq1S h2 h1)
      | upgrade_to_M_data_avilable_rq1 =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_upgrade_to_M_data_avilable_rq1_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_upgrade_to_M_data_avilable_rq1_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_upgrade_to_M_data_avilable_rq1_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_upgrade_to_M_data_avilable_rq1 h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_upgrade_to_M_data_avilable_rq1 h2 h1)
      | upgrade_to_S_data_avilable_rq1S =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_upgrade_to_S_data_avilable_rq1S_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_upgrade_to_S_data_avilable_rq1S_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_upgrade_to_S_data_avilable_rq1S_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_upgrade_to_S_data_avilable_rq1S h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_upgrade_to_S_data_avilable_rq1S h2 h1)
      | upgrade_to_M_invalid_all k₁ =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_upgrade_to_M_invalid_all_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_upgrade_to_M_invalid_all_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_upgrade_to_M_invalid_all_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_upgrade_to_M_invalid_all_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_upgrade_to_M_invalid_all_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_upgrade_to_M_invalid_all_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_upgrade_to_M_invalid_all_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_upgrade_to_M_invalid_all_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_upgrade_to_M_invalid_all h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_upgrade_to_M_invalid_all h2 h1)
      | invalid_allS =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_invalid_allS_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_invalid_allS_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_invalid_allS_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_invalid_allS_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_invalid_allS_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_invalid_allS_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_invalid_allS_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_invalid_allS_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_invalid_allS h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_invalid_allS h2 h1)
      | upgrade_to_S_invalid_2_rq1S k₁ =>
        cases c₂ with
        | rq_data_not_available =>
          exact peak_upgrade_to_S_invalid_2_rq1S_rq_data_not_available h1 h2
        | ld_rq_data_not_availableS =>
          exact peak_upgrade_to_S_invalid_2_rq1S_ld_rq_data_not_availableS h1 h2
        | upgrade_from_I_rq =>
          exact peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rq h1 h2
        | upgrade_from_I_rqS =>
          exact peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rqS h1 h2
        | upgrade_from_I_rs v₂ =>
          exact peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rs h1 h2
        | upgrade_from_I_rsS v₂ =>
          exact peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rsS h1 h2
        | downgrade_from_M_rs =>
          exact peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_M_rs h1 h2
        | downgrade_from_S_rsS =>
          exact peak_upgrade_to_S_invalid_2_rq1S_downgrade_from_S_rsS h1 h2
        | drop_rqIμ =>
          exact peak_symm (peak_drop_rqIμ_upgrade_to_S_invalid_2_rq1S h2 h1)
        | drop_rqIσ =>
          exact peak_symm (peak_drop_rqIσ_upgrade_to_S_invalid_2_rq1S h2 h1)
      | invalid_allM =>
        exact (no_step_junk (by simp) h1).elim
      | dawngrade_safe_parent_rq1 =>
        exact (no_step_junk (by simp) h1).elim
      | dawngrade_safe_parent_rq1S =>
        exact (no_step_junk (by simp) h1).elim
    | parent p₂ i₂ =>
      cases p₁ with
      | downgrade_from_M_rq1 v₁ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_downgrade_from_M_rq1_downgrade_from_M_rq1 h1 h2
        | downgrade_from_S_rq1S =>
          exact peak_downgrade_from_M_rq1_downgrade_from_S_rq1S h1 h2
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 h1 h2
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_downgrade_from_M_rq1_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_downgrade_from_M_rq1_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_downgrade_from_M_rq1_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_downgrade_from_M_rq1_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | downgrade_from_S_rq1S =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_downgrade_from_S_rq1S h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_downgrade_from_S_rq1S_downgrade_from_S_rq1S h1 h2
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_downgrade_from_S_rq1S_upgrade_to_M_data_avilable_rq1 h1 h2
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_downgrade_from_S_rq1S_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_downgrade_from_S_rq1S_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_downgrade_from_S_rq1S_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_downgrade_from_S_rq1S_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_to_M_data_avilable_rq1 =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_to_M_data_avilable_rq1 h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 h1 h2
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_upgrade_to_M_data_avilable_rq1_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_to_S_data_avilable_rq1S =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_to_S_data_avilable_rq1S h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_to_S_data_avilable_rq1S h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_data_avilable_rq1S h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_S_data_avilable_rq1S h1 h2
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_upgrade_to_S_data_avilable_rq1S_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_to_M_invalid_all k₁ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_to_M_invalid_all h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_to_M_invalid_all h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_M_invalid_all h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all h1 h2
        | invalid_allS =>
          exact peak_upgrade_to_M_invalid_all_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_upgrade_to_M_invalid_all_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | invalid_allS =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_invalid_allS h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_invalid_allS h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_invalid_allS h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_invalid_allS h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_invalid_allS h2 h1)
        | invalid_allS =>
          exact peak_invalid_allS_invalid_allS h1 h2
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_invalid_allS_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | upgrade_to_S_invalid_2_rq1S k₁ =>
        cases p₂ with
        | downgrade_from_M_rq1 v₂ =>
          exact peak_symm (peak_downgrade_from_M_rq1_upgrade_to_S_invalid_2_rq1S h2 h1)
        | downgrade_from_S_rq1S =>
          exact peak_symm (peak_downgrade_from_S_rq1S_upgrade_to_S_invalid_2_rq1S h2 h1)
        | upgrade_to_M_data_avilable_rq1 =>
          exact peak_symm (peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_invalid_2_rq1S h2 h1)
        | upgrade_to_S_data_avilable_rq1S =>
          exact peak_symm (peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_S_invalid_2_rq1S h2 h1)
        | upgrade_to_M_invalid_all k₂ =>
          exact peak_symm (peak_upgrade_to_M_invalid_all_upgrade_to_S_invalid_2_rq1S h2 h1)
        | invalid_allS =>
          exact peak_symm (peak_invalid_allS_upgrade_to_S_invalid_2_rq1S h2 h1)
        | upgrade_to_S_invalid_2_rq1S k₂ =>
          exact peak_upgrade_to_S_invalid_2_rq1S_upgrade_to_S_invalid_2_rq1S h1 h2
        | invalid_allM =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1 =>
          exact (no_step_junk (by simp) h2).elim
        | dawngrade_safe_parent_rq1S =>
          exact (no_step_junk (by simp) h2).elim
      | invalid_allM =>
        exact (no_step_junk (by simp) h1).elim
      | dawngrade_safe_parent_rq1 =>
        exact (no_step_junk (by simp) h1).elim
      | dawngrade_safe_parent_rq1S =>
        exact (no_step_junk (by simp) h1).elim

/-- `rule n` è la `rule` di `DecreasingDiagrams` sui passi etichettati. -/
theorem rule_eq : rule n = DecreasingDiagrams.rule (lstep (n := n)) := by
  funext a b; exact propext rule_iff_lstep

/-- Le tre ipotesi di `DecreasingDiagrams.Decreasing` per `MSI_trial`. -/
theorem decreasing : DecreasingDiagrams.Decreasing (Reach (n := n)) lstep where
  hR := fun a b ha hab => reach_step ha (rule_iff_lstep.mpr hab)
  hTop := by
    intro a b c k ha ⟨e₁, l₁, h1⟩ ⟨e₂, l₂, h2⟩
    have hp := local_peak h1 h2
    rw [l₁, l₂] at hp
    rcases hp with hj | heq | hun
    · rcases hj with ⟨_, d, hb, hc⟩ | ⟨hlt, _⟩ | ⟨hlt, _⟩
      · exact ⟨d, hb, hc⟩
      · exact absurd hlt (lt_irrefl _)
      · exact absurd hlt (lt_irrefl _)
    · subst heq; exact ⟨b, big_refl _ _, big_refl _ _⟩
    · exact absurd ha hun
  hMix := by
    intro a b c l k ha hlk ⟨e₁, l₁, h1⟩ ⟨e₂, l₂, h2⟩
    have hp := local_peak h1 h2
    rw [l₁, l₂] at hp
    rcases hp with hj | heq | hun
    · rcases hj with ⟨heq, _⟩ | ⟨_, b', d, hb, hbd, hcd⟩ | ⟨hgt, _⟩
      · exact absurd heq (Nat.ne_of_lt hlk)
      · exact ⟨b', d, hb, hbd, hcd⟩
      · exact absurd (Nat.lt_trans hlk hgt) (lt_irrefl _)
    · subst heq; exact ⟨b, b, Or.inl rfl, trans_refl.refl, trans_refl.refl⟩
    · exact absurd ha hun

/-- **Confluenza dei passi interni di `MSI_trial` sugli stati raggiungibili**, senza terminazione e
senza invarianti: l'ipotesi `has_diamond_property_on` di `ReachingStar.trace_inclusion`. -/
theorem msi_trial_confluent : has_diamond_property_on (Reach (n := n)) (trans_refl (rule n)) := by
  rw [rule_eq]
  exact DecreasingDiagrams.has_diamond_property_on_of_decreasing decreasing

end MSITrial
