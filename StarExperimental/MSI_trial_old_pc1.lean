import StarExperimental.MSI_trial_bridge

/-!
# `MSI_trial`: i diamanti locali di `MSI.lean` riusati (parent–cache, prima metà)

Copie testuali dei teoremi `comm_*` di `MSI.lean`: stesse ipotesi (passi di `MSI_def`), stesso
ricongiungimento, stessa dimostrazione. Cambia solo l'uscita: `¬ Reach s` (raggiungibilità di ARS di
`MSI_trial`, passi interni ed esterni) al posto di `¬ MSI.reachable s` (soli passi interni), tramite i
lemmi ponte di `MSI_trial_bridge.lean`. Ogni teorema è `old_<nome>`; il sollevamento ai passi di
`MSI_trial` e alla forma `DecJoin` è in `MSI_trial_peaks_*.lean`.
-/

open THEORY Relation MSIView

namespace MSITrial

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio spontaneo
della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂` la cache è in `M`
mentre il suo rilascio è già in volo: vista cattiva (`not_reach_of_M`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
      subst hne
      cases hc with
      | rq_data_not_available hM =>
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il downgrade non tocca la cache `i₂`
      have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
        simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
          .rq_data_not_available c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [downgradeMSt]
        · intro q
          simp only [downgradeMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss]
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio spontaneo
della cache `i₂` da `S` (accoda un `rsIσ` e passa a `I`). Con `i₁ = i₂` la cache è in `S`
mentre un suo rilascio da `M` è ancora in volo: vista cattiva (`not_reach_of_S`). Con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `S` con un proprio `rsIμ` in volo
      subst hne
      cases hc with
      | rq_data_not_available1 hS =>
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il downgrade non tocca la cache `i₂`
      have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
        simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
          .ld_rq_data_not_availableS c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [downgradeMSt]
        · intro q
          simp only [downgradeMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss]
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e richiesta di `M`
della cache `i₂` (in `I`, accoda `rqM`). Con `i₁ = i₂` il parent consuma la posizione `j` e la
cache accoda in fondo: i due passi commutano sulla stessa coda. Con `i₁ ≠ i₂` toccano indici
diversi: diamante. -/
theorem old_downgrade_from_M_rq1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rsIμ v` in posizione `j` sopravvive all'`rqM` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc => simp only [downgradeMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1, ← hs2,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeMSt, update_Fin_gss, ← hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la richiesta si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
            .upgrade_from_I_rq
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rqM] } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rq _ hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e richiesta di `S`
della cache `i₂` (in `I`, accoda `rqS`). Con `i₁ = i₂` il parent consuma la posizione `j` e la
cache accoda in fondo: i due passi commutano sulla stessa coda. Con `i₁ ≠ i₂` toccano indici
diversi: diamante. -/
theorem old_downgrade_from_M_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rsIμ v` in posizione `j` sopravvive all'`rqS` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc => simp only [downgradeMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1, ← hs2,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeMSt, update_Fin_gss, ← hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la richiesta si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
            .upgrade_from_I_rqS
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rqS] } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rq1 _ hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v₁` in `queue_cip i₁`) e presa del grant
di `M` dalla cache `i₂` (in `I`, consuma un `rsM v₂` da `queue_pc`). Con `i₁ = i₂` ci sono due
token `M` in volo per lo stesso indice (`rsM` in `queue_pci`, `rsIμ` in `queue_cip`):
vista cattiva (`not_reach_of_two_mu`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v₁ i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM v₂` in `queue_pci i₁` e `rsIμ v₁` in `queue_cip i₁`, due token `M`
        subst hne
        obtain ⟨_, hs2⟩ := hsync i₁
        refine Or.inr (Or.inr (not_reach_of_two_mu (i := i₁) ?_))
        -- un rilascio con token `M` in `queue_cip i₁`
        have h1 : 0 < (s.parent.queue_cip i₁).countP isReleaseM :=
          List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩
        -- una concessione con token `M` in `queue_pci i₁` (copia della cache, via `hsync`)
        have h2 : 0 < (s.parent.queue_pci i₁).countP isGrantM := by
          rw [hs2]; exact List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj', rfl⟩
        unfold muMsgs; omega
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeMSt s v₁ i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la concessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeMSt s v₁ i₁ j).caches i₂)
            (.upgrade_from_I_rs v₂)
            { s.caches i₂ with
                state := Bstate.M,
                value := v₂,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v₂ j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v₁` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v₁` in `queue_cip i₁`) e presa del grant
di `S` dalla cache `i₂` (in `I`, consuma un `rsS v₂` da `queue_pc`). Con `i₁ = i₂` un token `M`
(`rsIμ` in `queue_cip`) e un token `S` (`rsS` in `queue_pci`) sono in volo per lo stesso
indice: vista cattiva (`not_reach_of_mu_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v₁ i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsIμ v₁` in `queue_cip i₁` e `rsS v₂` in `queue_pci i₁`, token `M` e `S`
        subst hne
        obtain ⟨_, hs2⟩ := hsync i₁
        -- l'`rsS v₂` letto dal lato parent (copia della cache, via `hsync`)
        rw [← hs2] at hj'
        exact Or.inr (Or.inr (not_reach_of_mu_sig (muMsgs_ne_zero_of_rsIμ hj) (sigMsgs_ne_zero_of_rsS hj')))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeMSt s v₁ i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la concessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeMSt s v₁ i₁ j).caches i₂)
            (.upgrade_from_I_rsS v₂)
            { s.caches i₂ with
                state := Bstate.S,
                value := v₂,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v₂ j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v₁` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio su richiesta
della cache `i₂` (in `M`, consuma un `rqIμ` da `queue_pc` e accoda un `rsIμ`). Con `i₁ = i₂`
la cache è in `M` mentre il suo rilascio è già in volo: vista cattiva (`not_reach_of_M`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
      subst hne
      cases hc with
      | downgrade_from_M_rs j' hj' hM =>
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il downgrade non tocca la cache `i₂`
      have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
        simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
          .downgrade_from_M_rs c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [downgradeMSt]
        · intro q
          simp only [downgradeMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss]
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio su richiesta
della cache `i₂` (in `S`, consuma un `rqIσ` da `queue_pc` e accoda un `rsIσ`). Con `i₁ = i₂` la
cache è in `S` mentre un suo rilascio con token `M` è già in volo: vista cattiva (`not_reach_of_S`).
Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `S` con un proprio `rsIμ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
            .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeMSt, update_Fin_gss]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e rilascio
spontaneo della cache `i₂` da `M` (accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂` la cache
è in `M` mentre il suo rilascio `S` è già in volo: vista cattiva (`not_reach_of_M`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con un `rsIσ` in volo per sé
        subst hne
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .rq_data_not_available
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value],
                state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available _ hM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e rilascio
spontaneo della cache `i₂` da `S` (accoda un `rsIσ` e passa a `I`). Con `i₁ = i₂` la cache
è in `S` mentre il suo rilascio `S` è già in volo: vista cattiva (`not_reach_of_S`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `S` con un `rsIσ` in volo per sé
        subst hne
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio da `S` si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .ld_rq_data_not_availableS
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ],
                state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available1 _ hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e richiesta di `M`
della cache `i₂` (in `I`, accoda `rqM`). Con `i₁ = i₂` il parent consuma la posizione `j` e la
cache accoda in fondo: i due passi commutano sulla stessa coda. Con `i₁ ≠ i₂` toccano indici
diversi: diamante. -/
theorem old_downgrade_from_M_rq2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rsIσ` in posizione `j` sopravvive all'`rqM` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc => simp only [downgradeSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1, ← hs2,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la richiesta si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .upgrade_from_I_rq
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rqM] } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rq _ hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSSt]
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e richiesta di `S`
della cache `i₂` (in `I`, accoda `rqS`). Con `i₁ = i₂` il parent consuma la posizione `j` e la
cache accoda in fondo: i due passi commutano sulla stessa coda. Con `i₁ ≠ i₂` toccano indici
diversi: diamante. -/
theorem old_downgrade_from_M_rq2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rsIσ` in posizione `j` sopravvive all'`rqS` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc => simp only [downgradeSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1, ← hs2,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la richiesta si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .upgrade_from_I_rqS
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rqS] } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rq1 _ hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSSt]
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e presa del grant di `M`
dalla cache `i₂` (in `I`, consuma un `rsM v` da `queue_pc`). Con `i₁ = i₂` un token `M`
(`rsM` in `queue_pci`) e un token `S` (`rsIσ` in `queue_cip`) sono in volo per lo stesso
indice: vista cattiva (`not_reach_of_mu_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM v` in `queue_pci i₁` e `rsIσ` in `queue_cip i₁`, token `M` e `S`
        subst hne
        obtain ⟨_, hs2⟩ := hsync i₁
        -- l'`rsM v` letto dal lato parent (copia della cache, via `hsync`)
        rw [← hs2] at hj'
        exact Or.inr (Or.inr (not_reach_of_mu_sig (muMsgs_ne_zero_of_rsM hj') (sigMsgs_ne_zero_of_rsIσ hj)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la concessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            (.upgrade_from_I_rs v)
            { s.caches i₂ with
                state := Bstate.M,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSSt]
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e presa del grant di `S`
dalla cache `i₂` (in `I`, consuma un `rsS v` da `queue_pc`). Con `i₁ = i₂` ci sono due token `S`
in volo per lo stesso indice (`rsS` in `queue_pci`, `rsIσ` in `queue_cip`): vista cattiva
(`not_reach_of_two_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsS v` in `queue_pci i₁` e `rsIσ` in `queue_cip i₁`, due token `S`
        subst hne
        obtain ⟨_, hs2⟩ := hsync i₁
        refine Or.inr (Or.inr (not_reach_of_two_sig (i := i₁) ?_))
        -- un rilascio con token `S` in `queue_cip i₁`
        have h1 : 0 < (s.parent.queue_cip i₁).countP isReleaseS :=
          List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩
        -- una concessione con token `S` in `queue_pci i₁` (copia della cache, via `hsync`)
        have h2 : 0 < (s.parent.queue_pci i₁).countP isGrantS := by
          rw [hs2]; exact List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj', rfl⟩
        unfold sigMsgs; omega
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la concessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            (.upgrade_from_I_rsS v)
            { s.caches i₂ with
                state := Bstate.S,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSSt]
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e cessione della
linea da `M` della cache `i₂` su invalidate (`rqIμ` in posizione `j'` di `queue_pc`). Con
`i₁ = i₂` la cache è in `M` mentre il suo rilascio `S` è già in volo: vista cattiva
(`not_reach_of_M`). Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem old_downgrade_from_M_rq2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con un `rsIσ` in volo per sé
        subst hne
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la cessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs _ j' hj' hM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade del parent su `i₁` (consuma un `rsIσ` in `queue_cip i₁`) e rilascio su richiesta
della cache `i₂` (in `S`, consuma un `rqIσ` da `queue_pc` e accoda un `rsIσ`). Con `i₁ = i₂` la
cache è in `S` mentre un suo rilascio con token `S` è già in volo: vista cattiva (`not_reach_of_S`).
Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem old_downgrade_from_M_rq2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `S` con un proprio `rsIσ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((downgradeSSt s i₁ j).caches i₂)
            .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIσ` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSSt]
          · intro q
            simp only [downgradeSSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSSt, update_Fin_gss]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, righe tutte a `I`) e
rilascio spontaneo della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂` la
cache è in `M` mentre la riga la dà a `I`: vista cattiva (`not_reach_of_M`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `M` con la riga a `I`
      subst hne
      cases hc with
      | rq_data_not_available hM =>
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inr (Or.inr (by simp [hall i₁])))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il grant non tocca la cache `i₂`
      have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
        simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .rq_data_not_available c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- le righe non sono toccate dal passo di cache
      case g2 => exact hall
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [grantMSt]
        · intro q
          simp only [grantMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, righe tutte a `I`) e
rilascio spontaneo della cache `i₂` (in `S`, accoda un `rsIσ` e passa a `I`). Con `i₁ = i₂` la
cache è in `S` mentre la riga la dà a `I`: vista cattiva (`not_reach_of_S`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `S` con la riga a `I`
      subst hne
      cases hc with
      | rq_data_not_available1 hS =>
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inr (Or.inr (by simp [hall i₁])))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il grant non tocca la cache `i₂`
      have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
        simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .ld_rq_data_not_availableS c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- le righe non sono toccate dal passo di cache
      case g2 => exact hall
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [grantMSt]
        · intro q
          simp only [grantMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`)
e richiesta `upgrade_from_I_rq` della cache `i₂` (in `I`, accoda un `rqM`). Con `i₁ = i₂` la
cache accoda in fondo alla coda da cui il parent cancella la posizione `j`; con `i₁ ≠ i₂`
i due passi toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: l'`rqM` accodato in fondo non disturba la posizione `j`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida della coda (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- cancellare `j` commuta con l'append in fondo
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rqM]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rqM] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₁` è ancora in `I` dopo il grant
        case gc => simp only [grantMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1, herase]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs2]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₂` non è toccata dal grant su `i₁`
        case gc => simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`)
e richiesta `upgrade_from_I_rq1` della cache `i₂` (in `I`, accoda un `rqS`). Con `i₁ = i₂` la
cache accoda in fondo alla coda da cui il parent cancella la posizione `j`; con `i₁ ≠ i₂`
i due passi toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: l'`rqS` accodato in fondo non disturba la posizione `j`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida della coda (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- cancellare `j` commuta con l'append in fondo
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rqS]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rqS] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqM` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₁` è ancora in `I` dopo il grant
        case gc => simp only [grantMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1, herase]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs2]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₂` non è toccata dal grant su `i₁`
        case gc => simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (directory tutta a `I`) e `upgrade_from_I_rs` della cache
`i₂` (in `I`, consuma un `rsM v` da `queue_pc`). Con `i₁ = i₂` c'è un token `M` in volo verso
`i₁` mentre la riga `i₁` è a `I`: vista cattiva (`not_reach_of_mu_row`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM v` in volo verso `i₁` con la riga `i₁ = I` (vista cattiva 2)
        subst hne
        have hg : (s.parent.queue_pci i₁)[j']? = some (PCEvent.rsM v) := by
          rw [(hsync i₁).2]; exact hj'
        exact Or.inr (Or.inr (not_reach_of_mu_row (muMsgs_ne_zero_of_rsM hg) (by simp [hall i₁])))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la ricezione dell'`rsM` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) (.upgrade_from_I_rs v)
            { s.caches i₂ with
                state := Bstate.M,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (directory tutta a `I`) e `upgrade_from_I_rsS` della cache
`i₂` (in `I`, consuma un `rsS v` da `queue_pc`). Con `i₁ = i₂` c'è un token `S` in volo verso
`i₁` mentre la riga `i₁` è a `I`: vista cattiva (`not_reach_of_sig_row`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsS v` in volo verso `i₁` con la riga `i₁ = I` (vista cattiva 2)
        subst hne
        have hg : (s.parent.queue_pci i₁)[j']? = some (PCEvent.rsS v) := by
          rw [(hsync i₁).2]; exact hj'
        exact Or.inr (Or.inr (not_reach_of_sig_row (sigMsgs_ne_zero_of_rsS hg) (by simp [hall i₁])))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
        -- la ricezione dell'`rsS` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) (.upgrade_from_I_rsS v)
            { s.caches i₂ with
                state := Bstate.S,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, righe tutte a `I`) e
`downgrade_from_M_rs` della cache `i₂` (in `M`, consuma un `rqIμ` da `queue_pc`, accoda un `rsIμ`
e passa a `I`). Con `i₁ = i₂` la cache è in `M` mentre la riga la dà a `I`: vista cattiva
(`not_reach_of_M`). Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `M` con la riga a `I`
      subst hne
      cases hc with
      | downgrade_from_M_rs j' hj' hM =>
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inr (Or.inr (by simp [hall i₁])))))
    · -- indici distinti: il diamante
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      -- il grant non tocca la cache `i₂`
      have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
        simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
      -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
      have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .downgrade_from_M_rs c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
      case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      -- le righe non sono toccate dal passo di cache
      case g2 => exact hall
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · simp only [grantMSt]
        · intro q
          simp only [grantMSt]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
        · intro q
          by_cases hq₁ : q = i₁
          · subst hq₁
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `M` del parent su `i₁` (directory tutta a `I`) e `downgrade_from_M_rs1` della
cache `i₂` (in `S`, consuma un `rqIσ` da `queue_pc` e rilascia la linea con `rsIσ`). Con
`i₁ = i₂` la cache è in `S` mentre la riga `i₁` è a `I`: vista cattiva (`not_reach_of_S`). Con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `S` con la riga `i₁ = I` (vista cattiva 3)
        subst hne
        exact Or.inr (Or.inr (not_reach_of_S hS (Or.inr (Or.inr (by simp [hall i₁])))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `S` del parent su `i₁` (consuma un `rqS` in `queue_cip i₁`, nessuna riga a `M`) e
rilascio spontaneo della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂`
la cache è in `M` mentre la riga non è a `M`: vista cattiva (`not_reach_of_M`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi: diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con la riga non a `M`
        subst hne
        exact Or.inr (Or.inr (not_reach_of_M hM (Or.inr (Or.inr (hnoM i₁)))))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) .rq_data_not_available
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value],
                state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available _ hM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la riga `i₁` della directory non è toccata dal passo di cache
        case hI1 => exact hI
        -- le righe della directory non sono toccate dal passo di cache
        case g2 => exact hnoM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `S` del parent su `i₁` (consuma l'`rqS` in posizione `j` di `queue_cip i₁`, accoda
`rsS` a `queue_pci i₁`) e rilascio spontaneo della cache `i₂` in `S` (accoda `rsIσ`, passa a `I`).
Commutano sempre: con `i₁ = i₂` la cache accoda in fondo alla coda da cui il parent cancella
(`(l ++ [rsIσ]).eraseIdx j = l.eraseIdx j ++ [rsIσ]`); con `i₁ ≠ i₂` toccano indici diversi. -/
theorem old_upgrade_to_M_data_avilable_rq2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent cancella da `queue_cip i₁`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- l'`rqS` sta nella copia della cache, prima dell'`rsIσ` accodato
        have hj' : (s.caches i₁).queue_cp[j]? = some CPEvent.rqS := by rw [← hs1]; exact hj
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?c1)) ?eq⟩
        -- lato sinistro: l'`rqS` è ancora in posizione `j` dopo l'append dell'`rsIσ`
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- le righe della directory non sono toccate dal passo di cache
        case hI1 => exact hI
        case g2 => exact hnoM
        -- la cache `i₁` è ancora in `S` dopo il grant
        case c1 => simp only [grantSSt, update_Fin_gss]; exact hS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs1, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs1, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs2]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) .ld_rq_data_not_availableS
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ],
                state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available1 _ hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- le righe della directory non sono toccate dal passo di cache
        case hI1 => exact hI
        case g2 => exact hnoM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `S` del parent su `i₁` (consuma un `rqS` in `queue_cip i₁`, nessuna riga a `M`) e
richiesta `rqM` della cache `i₂` (in `I`, accoda in fondo a `queue_cp`). Con `i₁ = i₂` l'`rqM`
accodato in fondo non sposta la posizione `j` dell'`rqS` e la cache resta in `I`: il diamante.
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hrowI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: l'`rqM` accodato in fondo non disturba la posizione `j`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida della coda (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- cancellare `j` commuta con l'append in fondo
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rqM]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rqM] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqS` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la riga `i₁` è ancora `I`: il passo di cache non tocca la directory
        case hI1 => exact hrowI
        -- la directory non è toccata dal passo di cache
        case g2 => exact hnoM
        -- la cache `i₁` è ancora in `I` dopo il grant
        case gc => simp only [grantSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs1, herase]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs2]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la riga `i₁` è ancora `I`: il passo di cache non tocca la directory
        case hI1 => exact hrowI
        -- la directory non è toccata dal passo di cache
        case g2 => exact hnoM
        -- la cache `i₂` non è toccata dal grant su `i₁`
        case gc => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `S` del parent su `i₁` (consuma un `rqS` in `queue_cip i₁`, nessuna riga a `M`) e
richiesta `rqS` della cache `i₂` (in `I`, accoda in fondo a `queue_cp`). Con `i₁ = i₂` l'`rqS`
accodato in fondo non sposta la posizione `j` di quello consumato e la cache resta in `I`:
il diamante. Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- la nuova guardia del grant: la riga di `i₁` era a `I`
  have hrowI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: l'`rqS` accodato in fondo non disturba la posizione `j`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida della coda (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- cancellare `j` commuta con l'append in fondo
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rqS]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rqS] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqS` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la riga di `i₁` non è toccata dal passo di cache
        case hI1 => exact hrowI
        -- la directory non è toccata dal passo di cache
        case g2 => exact hnoM
        -- la cache `i₁` è ancora in `I` dopo il grant
        case gc => simp only [grantSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs1, herase]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSSt, update_Fin_gss, hs2]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la riga di `i₁` non è toccata dal passo di cache
        case hI1 => exact hrowI
        -- la directory non è toccata dal passo di cache
        case g2 => exact hnoM
        -- la cache `i₂` non è toccata dal grant su `i₁`
        case gc => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


end MSITrial
