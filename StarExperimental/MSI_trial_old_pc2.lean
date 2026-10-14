import StarExperimental.MSI_trial_bridge

/-!
# `MSI_trial`: i diamanti locali di `MSI.lean` riusati (parent–cache, seconda metà)

Copie testuali dei teoremi `comm_*` di `MSI.lean`: stesse ipotesi (passi di `MSI_def`), stesso
ricongiungimento, stessa dimostrazione. Cambia solo l'uscita: `¬ Reach s` (raggiungibilità di ARS di
`MSI_trial`, passi interni ed esterni) al posto di `¬ MSI.reachable s` (soli passi interni), tramite i
lemmi ponte di `MSI_trial_bridge.lean`. Ogni teorema è `old_<nome>`; il sollevamento ai passi di
`MSI_trial` e alla forma `DecJoin` è in `MSI_trial_peaks_*.lean`.
-/

open THEORY Relation MSIView

namespace MSITrial

/-- Grant di `S` del parent su `i₁` (consuma un `rqS`, nessuna riga a `M`) e presa del grant
di `M` da parte della cache `i₂` (consuma un `rsM v` da `queue_pc`). Con `i₁ = i₂` c'è un
`rsM` in volo verso `i₁` mentre la riga `i₁` non è a `M`: vista cattiva 2 (`not_reach_of_mu_row`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hIrow := grantS_rowI h₁
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
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM v` in volo verso `i₁` con la riga `i₁` non a `M` (vista cattiva 2)
        subst hne
        have hg : (s.parent.queue_pci i₁)[j']? = some (PCEvent.rsM v) := by
          rw [(hsync i₁).2]; exact hj'
        exact Or.inr (Or.inr (not_reach_of_mu_row (muMsgs_ne_zero_of_rsM hg) (hnoM i₁)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la presa dell'`rsM` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) (.upgrade_from_I_rs v)
            { s.caches i₂ with
                state := Bstate.M,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case hI1 => exact hIrow
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


/-- Grant di `S` del parent su `i₁` (consuma un `rqS`, accoda un `rsS` a `queue_pci i₁`) e presa
di un grant di `S` da parte della cache `i₂` (in `I`, consuma un `rsS v` in posizione `j'` di
`queue_pc`). Con `i₁ = i₂` il parent accoda in fondo e la cache cancella una posizione interna:
i due effetti commutano e la cache resta in `I` per il secondo passo: il diamante. Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hrow := grantS_rowI h₁
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
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci i₁`, la cache cancella da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la posizione `j'` è dentro la coda: sopravvive all'append dell'`rsS`
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?gI ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` (= `queue_cp`, per `hs1`) non è toccato
        case g1 => simp only [update_Fin_gss]; rw [← hs1]; exact hj
        -- la directory non è toccata dal passo di cache
        case gI => exact hrow
        case g2 => exact hnoM
        -- lato destro: l'`rsS v` è ancora in posizione `j'` dopo l'append del nuovo `rsS`
        case c1 =>
          simp only [grantSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il grant
        case c2 => simp only [grantSSt, update_Fin_gss]; exact hI
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
            · subst hq; simp only [grantSSt, update_Fin_gss, hs1]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la presa dell'`rsS` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) (.upgrade_from_I_rsS v)
            { s.caches i₂ with
                state := Bstate.S,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?gI ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case gI => exact hrow
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
`downgrade_from_M_rs` della cache `i₂` (in `M`, consuma un `rqIμ` da `queue_pc`, accoda `rsIμ`).
Con `i₁ = i₂` la cache è in `M` mentre la riga non è a `M`: vista cattiva (`not_reach_of_M`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi: diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
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
    | downgrade_from_M_rs j' hj' hM =>
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
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs _ j' hj' hM
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


/-- Grant di `S` del parent su `i₁` (consuma un `rqS` in `queue_cip i₁`, accoda un `rsS` a
`queue_pci i₁`) e `downgrade_from_M_rs1` della cache `i₂` (in `S`, consuma un `rqIσ` in `j'` da
`queue_pc`, accoda `rsIσ` a `queue_cp`). Con `i₁ = i₂` ciascun passo accoda in fondo alla coda
da cui l'altro cancella una posizione interna: i due effetti commutano. Con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano: il diamante. -/
theorem old_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
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
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: append in fondo e cancellazione interna commutano su entrambe le code
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida di `queue_cp`: sopravvive all'append dell'`rsIσ`
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- `j'` è una posizione valida di `queue_pc`: sopravvive all'append dell'`rsS`
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqS` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la directory non è toccata dal passo di cache
        case hI1 => exact hI
        case g2 => exact hnoM
        -- lato destro: l'`rqIσ` è ancora in posizione `j'` dopo l'append dell'`rsS`
        case c1 =>
          simp only [grantSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il grant
        case c2 => simp only [grantSSt, update_Fin_gss]; exact hS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt, List.eraseIdx_append_of_lt_length hb]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs1, List.eraseIdx_append_of_lt_length hb]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio da `S` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((grantSSt s i₁ j).caches i₂) .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
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


/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`, con un `rqM` o un
`rqS` pendente da `k`) e rilascio spontaneo della cache `i₂` (in `M`: passa a `I` e accoda un
`rsIμ` a `queue_cp`). Con `i₁ = i₂` le due regole scrivono su code diverse e il passo del parent
riallinea le copie (`hsync`); se il richiedente `k` è `i₂`, la richiesta in posizione `j`
sopravvive all'append. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidateM_inv h₁
  -- la richiesta sta in una posizione valida di `queue_cip k`
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hj with hj | hj <;> exact (List.getElem?_eq_some_iff.mp hj).1
  -- l'invalidate si riapplica con la stessa regola (`rqM` oppure `rqS` pendente da `k`)
  have hIM : ∀ (p : ParentState n),
      ((p.queue_cip k)[j]? = some CPEvent.rqM ∨ (p.queue_cip k)[j]? = some CPEvent.rqS) →
      p.shared_state i₁ = Bstate.M →
      parent_msi_step p (.upd_queue (.upgrade_to_M_invalid_all k) i₁)
        { p with queue_pci := update_Fin i₁ (p.queue_pci i₁ ++ [PCEvent.rqIμ]) p.queue_pci } := by
    intro p hp hpM
    rcases hp with hp | hp
    · exact parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hp hpM
    · exact parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hp hpM
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp` e `state`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- la richiesta in `queue_cip k` sopravvive all'append dell'`rsIμ`
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            simp only [update_Fin_gss, ← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case c1 => simp only [invMSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- la richiesta in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            simp only [update_Fin_gss, ← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hcM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`, con un `rqM` o un
`rqS` pendente da `k`) e rilascio spontaneo della cache `i₂` (in `S`: passa a `I` e accoda un
`rsIσ` a `queue_cp`). Con `i₁ = i₂` le due regole scrivono su code diverse e il passo del parent
riallinea le copie (`hsync`); se il richiedente `k` è `i₂`, la richiesta in posizione `j`
sopravvive all'append. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidateM_inv h₁
  -- la richiesta sta in una posizione valida di `queue_cip k`
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hj with hj | hj <;> exact (List.getElem?_eq_some_iff.mp hj).1
  -- l'invalidate si riapplica con la stessa regola (`rqM` oppure `rqS` pendente da `k`)
  have hIM : ∀ (p : ParentState n),
      ((p.queue_cip k)[j]? = some CPEvent.rqM ∨ (p.queue_cip k)[j]? = some CPEvent.rqS) →
      p.shared_state i₁ = Bstate.M →
      parent_msi_step p (.upd_queue (.upgrade_to_M_invalid_all k) i₁)
        { p with queue_pci := update_Fin i₁ (p.queue_pci i₁ ++ [PCEvent.rqIμ]) p.queue_pci } := by
    intro p hp hpM
    rcases hp with hp | hp
    · exact parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hp hpM
    · exact parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hp hpM
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hcS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp` e `state`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?c1)) ?eq⟩
        -- la richiesta in `queue_cip k` sopravvive all'append dell'`rsIσ`
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: la posizione `j` è prima dell'`rsIσ` accodato
            subst hk
            simp only [update_Fin_gss, ← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- la cache `i₁` è ancora in `S` dopo il passo del parent
        case c1 => simp only [invMSt, update_Fin_gss]; exact hcS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?c1)) ?eq⟩
        -- la richiesta in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIσ` accodato
            subst hk
            simp only [update_Fin_gss, ← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hcS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato (`upgrade_to_M_invalid_all k`: il parent accoda un `rqIμ` a `queue_pci i₁`)
e richiesta `rqM` dalla cache `i₂` (in `I`, accoda a `queue_cp`) commutano sempre. Con `i₁ = i₂`
il parent tocca `queue_pci` e la cache `queue_cp`; con `i₁ ≠ i₂` i passi toccano indici diversi.
La richiesta di `k` (`rqM` o `rqS`) resta al suo posto anche se `k = i₂`: diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`; la richiesta di `k` (`rqM` o `rqS`) sta in `j`
  obtain ⟨⟨j, hrq⟩, hM, rfl⟩ := invalidateM_inv h₁
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hrq with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  -- l'invalidate si riapplica con la stessa regola da ogni stato con la richiesta in `j` e riga `i₁ = M`
  have hinv : ∀ u : MSIState n,
      ((u.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (u.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      u.parent.shared_state i₁ = Bstate.M →
      msi_step_internal u (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) (invMSt u i₁) := by
    intro u hu hM'
    rcases hu with hu | hu
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hu hM')
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hu hM')
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?c1)) ?eq⟩
        -- la richiesta di `k` sopravvive all'`rqM` accodato in fondo
        case g1 =>
          by_cases hk : i₁ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case c1 => simp only [invMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?c1)) ?eq⟩
        -- la richiesta di `k` sopravvive al passo della cache `i₂` (se `k = i₂` sta prima dell'`rqM`)
        case g1 =>
          by_cases hk : i₂ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato (`upgrade_to_M_invalid_all k`: il parent accoda un `rqIμ` a `queue_pci i₁`)
e richiesta `rqS` dalla cache `i₂` (in `I`, accoda a `queue_cp`) commutano sempre. Con `i₁ = i₂`
il parent tocca `queue_pci` e la cache `queue_cp`; con `i₁ ≠ i₂` i passi toccano indici diversi.
La richiesta di `k` (`rqM` o `rqS`) resta al suo posto anche se `k = i₂`: diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`; la richiesta di `k` (`rqM` o `rqS`) sta in `j`
  obtain ⟨⟨j, hrq⟩, hM, rfl⟩ := invalidateM_inv h₁
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hrq with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  -- l'invalidate si riapplica con la stessa regola da ogni stato con la richiesta in `j` e riga `i₁ = M`
  have hinv : ∀ u : MSIState n,
      ((u.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (u.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      u.parent.shared_state i₁ = Bstate.M →
      msi_step_internal u (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) (invMSt u i₁) := by
    intro u hu hM'
    rcases hu with hu | hu
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hu hM')
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hu hM')
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?c1)) ?eq⟩
        -- la richiesta di `k` sopravvive all'`rqS` accodato in fondo
        case g1 =>
          by_cases hk : i₁ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case c1 => simp only [invMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs2]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?c1)) ?eq⟩
        -- la richiesta di `k` sopravvive al passo della cache `i₂` (se `k = i₂` sta prima dell'`rqS`)
        case g1 =>
          by_cases hk : i₂ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato (`upgrade_to_M_invalid_all k`) e `upgrade_from_I_rs` (la cache `i₂`, in `I`,
consuma l'`rsM v` in posizione `j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'`rqIμ`
finisce in fondo alla coda e non sposta `j'`; con `i₁ ≠ i₂` i passi toccano indici diversi.
La richiesta di `k` resta al suo posto (la cache non tocca `queue_cp`): diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`; la richiesta di `k` (`rqM` o `rqS`) sta in `j`
  obtain ⟨⟨j, hrq⟩, hM, rfl⟩ := invalidateM_inv h₁
  -- l'invalidate si riapplica con la stessa regola da ogni stato con la richiesta in `j` e riga `i₁ = M`
  have hinv : ∀ u : MSIState n,
      ((u.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (u.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      u.parent.shared_state i₁ = Bstate.M →
      msi_step_internal u (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) (invMSt u i₁) := by
    intro u hu hM'
    rcases hu with hu | hu
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hu hM')
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hu hM')
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      -- l'`rsM v` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k` è ancora al suo posto: la cache non tocca `queue_cp`
        case g1 =>
          by_cases hk : i₁ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- l'`rsM v` è ancora in posizione `j'`: l'`rqIμ` è stato appeso in fondo
        case c1 =>
          simp only [invMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case c2 => simp only [invMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k`: la cache `i₂` non tocca `queue_cp`
        case g1 =>
          by_cases hk : i₂ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case c2 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato (`upgrade_to_M_invalid_all k`) e `upgrade_from_I_rsS` (la cache `i₂`, in `I`,
consuma l'`rsS v` in posizione `j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'`rqIμ`
finisce in fondo alla coda e non sposta `j'`; con `i₁ ≠ i₂` i passi toccano indici diversi.
La richiesta di `k` resta al suo posto (la cache non tocca `queue_cp`): diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`; la richiesta di `k` (`rqM` o `rqS`) sta in `j`
  obtain ⟨⟨j, hrq⟩, hM, rfl⟩ := invalidateM_inv h₁
  -- l'invalidate si riapplica con la stessa regola da ogni stato con la richiesta in `j` e riga `i₁ = M`
  have hinv : ∀ u : MSIState n,
      ((u.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (u.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      u.parent.shared_state i₁ = Bstate.M →
      msi_step_internal u (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) (invMSt u i₁) := by
    intro u hu hM'
    rcases hu with hu | hu
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hu hM')
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hu hM')
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      -- l'`rsS v` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k` è ancora al suo posto: la cache non tocca `queue_cp`
        case g1 =>
          by_cases hk : i₁ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- l'`rsS v` è ancora in posizione `j'`: l'`rqIμ` è stato appeso in fondo
        case c1 =>
          simp only [invMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case c2 => simp only [invMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k`: la cache `i₂` non tocca `queue_cp`
        case g1 =>
          by_cases hk : i₂ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case c2 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`, con un `rqM` o un
`rqS` pendente da `k`) e cessione della cache `i₂` (in `M`: consuma l'`rqIμ` in posizione `j'`
di `queue_pc`, passa a `I` e accoda un `rsIμ`). Con `i₁ = i₂` il nuovo `rqIμ` finisce in fondo e
non sposta `j'`, mentre il `rsIμ` accodato non sposta la richiesta `j`; con `i₁ ≠ i₂` i due passi
toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidateM_inv h₁
  -- la richiesta sta in una posizione valida di `queue_cip k`
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hj with hj | hj <;> exact (List.getElem?_eq_some_iff.mp hj).1
  -- l'invalidate si riapplica con la stessa regola (`rqM` oppure `rqS` pendente da `k`)
  have hIM : ∀ (p : ParentState n),
      ((p.queue_cip k)[j]? = some CPEvent.rqM ∨ (p.queue_cip k)[j]? = some CPEvent.rqS) →
      p.shared_state i₁ = Bstate.M →
      parent_msi_step p (.upd_queue (.upgrade_to_M_invalid_all k) i₁)
        { p with queue_pci := update_Fin i₁ (p.queue_pci i₁ ++ [PCEvent.rqIμ]) p.queue_pci } := by
    intro p hp hpM
    rcases hp with hp | hp
    · exact parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hp hpM
    · exact parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hp hpM
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hMc =>
      -- l'`rqIμ` consumato sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?gp1 ?gp2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- la richiesta di `k` è ancora al suo posto: l'`rsIμ` è appeso in fondo
        case gp1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            simp only [update_Fin_gss, ← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case gp2 => exact hM
        -- l'`rqIμ` consumato è ancora in posizione `j'`: il nuovo è stato appeso in fondo
        case gc1 =>
          simp only [invMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case gc2 => simp only [invMSt, update_Fin_gss]; exact hMc
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁ (hIM _ ?gp1 ?gp2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- la richiesta di `k`: se `k = i₂` sta prima dell'`rsIμ` appeso
        case gp1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            simp only [update_Fin_gss, ← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gp2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case gc2 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hMc
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato (`upgrade_to_M_invalid_all k`) e `downgrade_from_M_rs1` (la cache `i₂`, in `S`,
consuma l'`rqIσ` in posizione `j'` di `queue_pc` e accoda `rsIσ` a `queue_cp`) commutano sempre.
Con `i₁ = i₂` il nuovo `rqIμ` finisce in fondo e non sposta `j'`, e la richiesta di `k` resta
prima dell'`rsIσ` appeso; con `i₁ ≠ i₂` i passi toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invMSt s i₁`; la richiesta di `k` (`rqM` o `rqS`) sta in `j`
  obtain ⟨⟨j, hrq⟩, hM, rfl⟩ := invalidateM_inv h₁
  have hlt : j < (s.parent.queue_cip k).length := by
    rcases hrq with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  -- l'invalidate si riapplica con la stessa regola da ogni stato con la richiesta in `j` e riga `i₁ = M`
  have hinv : ∀ u : MSIState n,
      ((u.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (u.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      u.parent.shared_state i₁ = Bstate.M →
      msi_step_internal u (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) (invMSt u i₁) := by
    intro u hu hM'
    rcases hu with hu | hu
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all _ k i₁ j hu hM')
    · exact msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₁ j hu hM')
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      -- l'`rqIσ` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc` e accoda a `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k` è ancora al suo posto: l'`rsIσ` è appeso in fondo
        case g1 =>
          by_cases hk : i₁ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` è ancora `M` dopo il passo della cache
        case g2 => exact hM
        -- l'`rqIσ` consumato è ancora in posizione `j'`: il nuovo `rqIμ` è stato appeso in fondo
        case c1 =>
          simp only [invMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il passo del parent
        case c2 => simp only [invMSt, update_Fin_gss]; exact hS
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invMSt, update_Fin_gss, hs1]
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invMSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_, hinv _ ?g1 ?g2,
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?c1 ?c2)) ?eq⟩
        -- la richiesta di `k`: se `k = i₂` sta prima dell'`rsIσ` appeso
        case g1 =>
          by_cases hk : i₂ = k
          · subst hk
            simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hrq
          · simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hrq
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case c2 => simp only [invMSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, per un `rqM`
pendente da `k`) e `rq_data_not_available` (la cache `i₂`, in `M`, rilascia la linea accodando
un `rsIμ` a `queue_cp`) commutano sempre. Con `i₁ = i₂` le due regole scrivono su code diverse
(l'`rqM` di `k` resta al suo posto: l'append è in fondo) e il parent riallinea le copie della
cache (`hsync`); con `i₁ ≠ i₂` toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
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
  obtain ⟨⟨k, j, hj⟩, hS, rfl⟩ := invalidateS_inv h₁
  -- la posizione `j` dell'`rqM` è valida: un append in fondo a `queue_cip k` non la sposta
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `state` e `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: stato intatto, code riallineate
        have hci : (invSSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIσ] } := by
          simp only [invSSt, update_Fin_gss]
        -- il rilascio si applica ancora da `s'`
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₁) .rq_data_not_available
            { s.caches i₁ with
                state := Bstate.I,
                queue_cp := s.parent.queue_cip i₁ ++ [CPEvent.rsIμ (s.caches i₁).value],
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIσ] } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available _ hcM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gj hS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: il rilascio accoda solo in fondo
        case gj =>
          by_cases hk : k = i₁
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il passo del parent su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂) .rq_data_not_available
            { s.caches i₂ with
                state := Bstate.I,
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available _ hcM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gj hS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: il rilascio accoda solo in fondo
        case gj =>
          by_cases hk : k = i₂
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, per un `rqM`
pendente da `k`) e `ld_rq_data_not_availableS` (la cache `i₂`, in `S`, rilascia la linea
accodando un `rsIσ` a `queue_cp`) commutano sempre. Con `i₁ = i₂` le due regole scrivono su
code diverse (l'`rqM` di `k` resta al suo posto) e il parent riallinea le copie della cache
(`hsync`); con `i₁ ≠ i₂` toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
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
  obtain ⟨⟨k, j, hj⟩, hS, rfl⟩ := invalidateS_inv h₁
  -- la posizione `j` dell'`rqM` è valida: un append in fondo a `queue_cip k` non la sposta
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hcS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `state` e `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: stato intatto, code riallineate
        have hci : (invSSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIσ] } := by
          simp only [invSSt, update_Fin_gss]
        -- il rilascio si applica ancora da `s'`
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₁) .ld_rq_data_not_availableS
            { s.caches i₁ with
                state := Bstate.I,
                queue_cp := s.parent.queue_cip i₁ ++ [CPEvent.rsIσ],
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIσ] } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available1 _ hcS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gj hS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: il rilascio accoda solo in fondo
        case gj =>
          by_cases hk : k = i₁
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il passo del parent su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂) .ld_rq_data_not_availableS
            { s.caches i₂ with
                state := Bstate.I,
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available1 _ hcS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gj hS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: il rilascio accoda solo in fondo
        case gj =>
          by_cases hk : k = i₂
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, un `rqM`
pendente da `k`) e `upgrade_from_I_rq` (la cache `i₂`, in `I`, accoda `rqM` a `queue_cp`)
commutano sempre: l'`rqM` di `k` sopravvive all'append della cache. Con `i₁ = i₂` il parent
riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨k, j, hk⟩, hS, rfl⟩ := invalidateS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      -- l'`rqM` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rqM]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqM := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, un `rqM`
pendente da `k`) e `upgrade_from_I_rq1` (la cache `i₂`, in `I`, accoda `rqS` a `queue_cp`)
commutano sempre: l'`rqM` di `k` sopravvive all'append della cache. Con `i₁ = i₂` il parent
riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨k, j, hk⟩, hS, rfl⟩ := invalidateS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      -- l'`rqM` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rqS]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqM := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, un `rqM`
pendente da `k`) e `upgrade_from_I_rs` (la cache `i₂`, in `I`, consuma l'`rsM v` in posizione
`j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta `j'` e il
parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨k, j, hk⟩, hS, rfl⟩ := invalidateS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      -- l'`rqM` del richiedente `k` sopravvive al passo della cache (che non tocca `queue_cp`)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ (s.caches i₂).queue_cp s.parent.queue_cip k)[j'']?
            = some CPEvent.rqM := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          exact ⟨j, by rw [update_Fin_gss]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?gj ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rsM v` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            (.upgrade_from_I_rs v)
            { s.caches i₂ with
                state := Bstate.M,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, un `rqM`
pendente da `k`) e `upgrade_from_I_rsS` (la cache `i₂`, in `I`, consuma l'`rsS v` in posizione
`j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta `j'` e il
parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨k, j, hk⟩, hS, rfl⟩ := invalidateS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      -- l'`rqM` del richiedente `k` sopravvive al passo della cache (che non tocca `queue_cp`)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ (s.caches i₂).queue_cp s.parent.queue_cip k)[j'']?
            = some CPEvent.rqM := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          exact ⟨j, by rw [update_Fin_gss]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?gj ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rsS v` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            (.upgrade_from_I_rsS v)
            { s.caches i₂ with
                state := Bstate.S,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, per un `rqM`
pendente da `k`) e `downgrade_from_M_rs` (la cache `i₂`, in `M`, consuma l'`rqIμ` in posizione
`j'` di `queue_pc` e accoda un `rsIμ` a `queue_cp`) commutano sempre. Con `i₁ = i₂` gli append
in fondo non spostano né `j'` né l'`rqM` di `k`, e il parent riallinea le copie (`hsync`);
con `i₁ ≠ i₂` toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
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
  obtain ⟨⟨k, j, hj⟩, hS, rfl⟩ := invalidateS_inv h₁
  -- la posizione `j` dell'`rqM` è valida: un append in fondo a `queue_cip k` non la sposta
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hcM =>
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt', _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt' _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache tocca `queue_pc`/`queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gk hS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gj ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: la cache accoda solo in fondo a `queue_cp`
        case gk =>
          by_cases hk : k = i₁
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- l'`rqIμ` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs _ j' hj' hcM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j ?gk hS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in posizione `j`: la cache accoda solo in fondo a `queue_cp`
        case gk =>
          by_cases hk : k = i₂
          · rw [hk] at hj hlt ⊢; simp only [update_Fin_gss]; rw [← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`, un `rqM`
pendente da `k`) e `downgrade_from_M_rs1` (la cache `i₂`, in `S`, consuma l'`rqIσ` in posizione
`j'` di `queue_pc`, passa a `I` e accoda `rsIσ` a `queue_cp`) commutano sempre. Con `i₁ = i₂`
l'append in fondo non sposta `j'` e il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂`
indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨k, j, hk⟩, hS, rfl⟩ := invalidateS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hcS =>
      -- l'`rqM` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rsIσ]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqM := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?gj ?gc)) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rqIσ` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hcS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hcS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' ?gk ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate `rqIσ` del parent su `i₁` (un `rqS` pendente da `k ≠ i₁`, riga `i₁ = S`) e
rilascio spontaneo della cache `i₂` (in `M`: passa a `I` e accoda un `rsIμ` a `queue_cp`).
Con `i₁ = i₂` le due regole scrivono su code diverse e il passo del parent riallinea le copie
(`hsync`); con `i₁ ≠ i₂`, se il richiedente `k` è `i₂`, l'`rqS` in posizione `j` sopravvive
all'append. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invSSt s i₁`
  obtain ⟨⟨j, hj⟩, hnk, hS, rfl⟩ := invalidateS2_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp` e `state`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?g1 hnk ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- l'`rqS` sta in `queue_cip k` con `k ≠ i₁`: coda invariata
        case g1 => simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hnk)]; exact hj
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case g2 => exact hS
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case c1 => simp only [invSSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?g1 hnk ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- l'`rqS` in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : k = i₂
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← (hsync k).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hcM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate `rqIσ` del parent su `i₁` (un `rqS` pendente da `k ≠ i₁`, riga `i₁ = S`) e
rilascio spontaneo della cache `i₂` (in `S`: passa a `I` e accoda un `rsIσ` a `queue_cp`).
Con `i₁ = i₂` le due regole scrivono su code diverse e il passo del parent riallinea le copie
(`hsync`); con `i₁ ≠ i₂`, se il richiedente `k` è `i₂`, l'`rqS` in posizione `j` sopravvive
all'append. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invSSt s i₁`
  obtain ⟨⟨j, hj⟩, hnk, hS, rfl⟩ := invalidateS2_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hcS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp` e `state`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?g1 hnk ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?c1)) ?eq⟩
        -- l'`rqS` sta in `queue_cip k` con `k ≠ i₁`: coda invariata
        case g1 => simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hnk)]; exact hj
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case g2 => exact hS
        -- la cache `i₁` è ancora in `S` dopo il passo del parent
        case c1 => simp only [invSSt, update_Fin_gss]; exact hcS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?g1 hnk ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?c1)) ?eq⟩
        -- l'`rqS` in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : k = i₂
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIσ` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← (hsync k).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case g2 => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hcS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `upgrade_to_S_invalid_2_rq1S k` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`,
un `rqS` pendente da `k ≠ i₁`) e `upgrade_from_I_rq` (la cache `i₂`, in `I`, accoda `rqM` a
`queue_cp`) commutano sempre: l'`rqS` di `k` sopravvive all'append della cache. Con `i₁ = i₂`
il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨j, hk⟩, hne₁, hS, rfl⟩ := invalidateS2_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      -- l'`rqS` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rqM]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqS := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `upgrade_to_S_invalid_2_rq1S k` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`,
un `rqS` pendente da `k ≠ i₁`) e `upgrade_from_I_rq1` (la cache `i₂`, in `I`, accoda `rqS` a
`queue_cp`) commutano sempre: l'`rqS` di `k` sopravvive all'append della cache. Con `i₁ = i₂`
il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨j, hk⟩, hne₁, hS, rfl⟩ := invalidateS2_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq1 hI =>
      -- l'`rqS` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rqS]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqS := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.upgrade_from_I_rq1 _ ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `upgrade_to_S_invalid_2_rq1S k` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`,
un `rqS` pendente da `k ≠ i₁`) e `upgrade_from_I_rs` (la cache `i₂`, in `I`, consuma l'`rsM v`
in posizione `j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta
`j'` e il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨j, hk⟩, hne₁, hS, rfl⟩ := invalidateS2_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      -- l'`rqS` del richiedente `k` sopravvive al passo della cache (che non tocca `queue_cp`)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ (s.caches i₂).queue_cp s.parent.queue_cip k)[j'']?
            = some CPEvent.rqS := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          exact ⟨j, by rw [update_Fin_gss]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?gj ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rsM v` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            (.upgrade_from_I_rs v)
            { s.caches i₂ with
                state := Bstate.M,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rs _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `upgrade_to_S_invalid_2_rq1S k` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`,
un `rqS` pendente da `k ≠ i₁`) e `upgrade_from_I_rsS` (la cache `i₂`, in `I`, consuma l'`rsS v`
in posizione `j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta
`j'` e il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨j, hk⟩, hne₁, hS, rfl⟩ := invalidateS2_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      -- l'`rqS` del richiedente `k` sopravvive al passo della cache (che non tocca `queue_cp`)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ (s.caches i₂).queue_cp s.parent.queue_cip k)[j'']?
            = some CPEvent.rqS := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          exact ⟨j, by rw [update_Fin_gss]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?gj ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rsS v` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            (.upgrade_from_I_rsS v)
            { s.caches i₂ with
                state := Bstate.S,
                value := v,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_msi_step_internal.upgrade_from_I_rsS _ v j' hj' hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate `rqIσ` del parent su `i₁` (un `rqS` pendente da `k ≠ i₁`, riga `i₁ = S`) e
`downgrade_from_M_rs` della cache `i₂` (in `M`: consuma l'`rqIμ` in posizione `j'` di `queue_pc`,
passa a `I` e accoda un `rsIμ`). Con `i₁ = i₂` il nuovo `rqIσ` finisce in fondo a `queue_pci` e
non sposta `j'`; con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
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
  -- `s'` è il record esplicito `invSSt s i₁`
  obtain ⟨⟨j, hj⟩, hnk, hS, rfl⟩ := invalidateS2_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hMc =>
      -- l'`rqIμ` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?gp1 hnk ?gp2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqS` sta in `queue_cip k` con `k ≠ i₁`: coda invariata
        case gp1 => simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hnk)]; exact hj
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gp2 => exact hS
        -- l'`rqIμ` consumato è ancora in posizione `j'`: l'`rqIσ` è stato appeso in fondo
        case gc1 =>
          simp only [invSSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case gc2 => simp only [invSSt, update_Fin_gss]; exact hMc
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invSSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invSSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j ?gp1 hnk ?gp2),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqS` del richiedente `k`: se `k = i₂` sta prima dell'`rsIμ` appeso
        case gp1 =>
          by_cases hk : k = i₂
          · rw [hk] at hj ⊢
            have hlt : j < (s.parent.queue_cip i₂).length := (List.getElem?_eq_some_iff.mp hj).1
            simp only [update_Fin_gss]
            rw [← hs1, List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gp2 => exact hS
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc1 => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case gc2 => simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']; exact hMc
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `upgrade_to_S_invalid_2_rq1S k` (il parent accoda un `rqIσ` a `queue_pci i₁`, riga `i₁ = S`,
un `rqS` pendente da `k ≠ i₁`) e `downgrade_from_M_rs1` (la cache `i₂`, in `S`, consuma l'`rqIσ`
in posizione `j'` di `queue_pc`, passa a `I` e accoda `rsIσ` a `queue_cp`) commutano sempre.
Con `i₁ = i₂` l'append in fondo non sposta `j'` e il parent riallinea le copie (`hsync`);
con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem old_upgrade_to_M_invalid_all2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  obtain ⟨⟨j, hk⟩, hne₁, hS, rfl⟩ := invalidateS2_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hcS =>
      -- l'`rqS` del richiedente `k` sopravvive al passo della cache (che accoda soltanto)
      have hk' : ∃ j'' : Nat,
          (update_Fin i₂ ((s.caches i₂).queue_cp ++ [CPEvent.rsIσ]) s.parent.queue_cip k)[j'']?
            = some CPEvent.rqS := by
        by_cases hki : k = i₂
        · subst hki
          rw [(hsync k).1] at hk
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
          exact ⟨j, by rw [update_Fin_gss, List.getElem?_append_left hlt]; exact hk⟩
        · exact ⟨j, by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      obtain ⟨j'', hk''⟩ := hk'
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIσ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIσ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIσ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?gj ?gc)) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` è ancora `S` dopo il passo della cache
        case gS => exact hS
        -- l'`rqIσ` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il passo del parent
        case gc => simp only [invSSt, update_Fin_gss]; exact hcS
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs1]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invSSt, update_Fin_gss, hs2, herase]
            · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invSSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invSSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_msi_step_internal ((invSSt s i₁).caches i₂)
            .downgrade_from_S_rsS
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ] } := by
          rw [hci]; exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' hj' hcS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₁ j'' ?gk hne₁ ?gS),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqS` di `k` è ancora in coda dopo il passo della cache
        case gk => exact hk''
        -- la riga `i₁` non è toccata dal passo della cache `i₂`
        case gS => exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss]
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]



end MSITrial
