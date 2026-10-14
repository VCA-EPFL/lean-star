import StarExperimental.MSI_trial_bridge

/-!
# `MSI_trial`: i diamanti locali di `MSI.lean` riusati (parent–parent)

Copie testuali dei teoremi `comm_*` di `MSI.lean`: stesse ipotesi (passi di `MSI_def`), stesso
ricongiungimento, stessa dimostrazione. Cambia solo l'uscita: `¬ Reach s` (raggiungibilità di ARS di
`MSI_trial`, passi interni ed esterni) al posto di `¬ MSI.reachable s` (soli passi interni), tramite i
lemmi ponte di `MSI_trial_bridge.lean`. Ogni teorema è `old_<nome>`; il sollevamento ai passi di
`MSI_trial` e alla forma `DecJoin` è in `MSI_trial_peaks_*.lean`.
-/

open THEORY Relation MSIView

namespace MSITrial

theorem old_downgrade_from_M_rq1_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s'' →
  (∃ t₁ t₂,
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) t₁ ∧
    msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) t₂ ∧
    { t₁ with parent.value := t₂.parent.value } = t₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List CPEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  -- `s'` e `s''` sono i record espliciti dei due downgrade
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeM_inv h₁
  obtain ⟨j₂, hj₂, rfl⟩ := downgradeM_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    by_cases hj : j₁ = j₂
    · -- stessa posizione: stesso `rsIμ`, quindi `v₁ = v₂` e `s' = s''`
      subst hj
      rw [hj₁] at hj₂
      cases hj₂
      exact Or.inr (Or.inl rfl)
    · rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
      · -- j₁ < j₂: l'`rsIμ v₁` resta in j₁ dopo aver tolto j₂, l'`rsIμ v₂` scala in j₂ - 1
        refine Or.inl ⟨_, _,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j₁ ?g1),
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₂ i₁ (j₂ - 1) ?g2),
          ?eq⟩
        -- da `s''` (tolto j₂): l'`rsIμ v₁` è ancora in j₁
        case g1 =>
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
        -- da `s'` (tolto j₁): l'`rsIμ v₂` è scalato in j₂ - 1
        case g2 =>
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
        -- i due stati finali coincidono a meno di `parent.value`
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, key (s.parent.queue_cip q) j₁ j₂ hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · rfl
          · intro q; simp only [downgradeMSt]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, key (s.parent.queue_cip q) j₁ j₂ hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q; simp only [downgradeMSt]
      · -- j₂ < j₁: simmetrico, l'`rsIμ v₁` scala in j₁ - 1
        refine Or.inl ⟨_, _,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ (j₁ - 1) ?g1),
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₂ i₁ j₂ ?g2),
          ?eq⟩
        -- da `s''` (tolto j₂): l'`rsIμ v₁` è scalato in j₁ - 1
        case g1 =>
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
        -- da `s'` (tolto j₁): l'`rsIμ v₂` è ancora in j₂
        case g2 =>
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
        -- i due stati finali coincidono a meno di `parent.value`
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, key (s.parent.queue_cip q) j₂ j₁ hgt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · rfl
          · intro q; simp only [downgradeMSt]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, key (s.parent.queue_cip q) j₂ j₁ hgt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q; simp only [downgradeMSt]
  · -- indici distinti: entrambi i downgrade restano abilitati, il diamante a meno del valore
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_, _,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j₁ ?g1),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq1 _ v₂ i₂ j₂ ?g2),
      ?eq⟩
    -- da `s''`: la coda `queue_cip i₁` non è toccata dal downgrade su `i₂`
    case g1 => simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- da `s'`: la coda `queue_cip i₂` non è toccata dal downgrade su `i₁`
    case g2 => simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    -- i due stati finali coincidono a meno di `parent.value`, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · rfl
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q; simp only [downgradeMSt]


/-- Downgrade da `M` su `i₁` (consuma un `rsIμ v`) e downgrade da `S` su `i₂` (consuma un `rsIσ`).
Con `i₁ ≠ i₂` i due passi toccano righe e code diverse: diamante. Con `i₁ = i₂` i due messaggi
sono diversi, quindi stanno in posizioni diverse della stessa coda: diamante con le posizioni
scalate (togliere prima `b` e poi `a < b` è come togliere prima `a` e poi `b - 1`). -/
theorem old_downgrade_from_M_rq1_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List CPEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  -- `s'` e `s''` sono i record espliciti dei due downgrade
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeM_inv h₁
  obtain ⟨j₂, hj₂, rfl⟩ := downgradeS_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: `rsIμ v` e `rsIσ` sono messaggi diversi, quindi `j₁ ≠ j₂`
    subst hne
    have hj : j₁ ≠ j₂ := by
      intro h; subst h; rw [hj₁] at hj₂; cases hj₂
    rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
    · -- j₁ < j₂: l'`rsIμ` resta in j₁ dopo aver tolto j₂; l'`rsIσ` scala in j₂ - 1 dopo aver tolto j₁
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j₁ ?g1),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ (j₂ - 1) ?g2)) ?eq⟩
      case g1 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
      case g2 =>
        simp only [downgradeMSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, key _ _ _ hlt]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · simp only [downgradeMSt]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, key _ _ _ hlt]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          simp only [downgradeMSt, downgradeSSt]
    · -- j₂ < j₁: simmetrico, l'`rsIμ` scala in j₁ - 1 dopo aver tolto j₂
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ (j₁ - 1) ?g1),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₂ ?g2)) ?eq⟩
      case g1 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
      case g2 =>
        simp only [downgradeMSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, key _ _ _ hgt]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · simp only [downgradeMSt]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, key _ _ _ hgt]
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          simp only [downgradeMSt, downgradeSSt]
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j₁ ?g1),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq2 _ i₂ j₂ ?g2)) ?eq⟩
    -- l'`rsIμ v` in `queue_cip i₁` non è toccato dal downgrade su `i₂`
    case g1 => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- l'`rsIσ` in `queue_cip i₂` non è toccato dal downgrade su `i₁`
    case g2 => simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
                       update_Fin_gso2 _ _ _ _ hq₂]
      · simp only [downgradeMSt]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
                       update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
                       update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        simp only [downgradeMSt, downgradeSSt]


/-- **Downgrade da `M` / grant di `M`.** Il grant richiede tutte le righe a `I`, ma il
downgrade consuma un `rsIμ` in volo su `i₁`: un token `M` per `i₁` con la riga `i₁` non a `M`
è la vista cattiva 2 (`not_reach_of_mu_row`), sia con `i₁ = i₂` sia con `i₁ ≠ i₂`. -/
theorem old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₂
  -- un `rsIμ` in volo su `i₁` mentre la riga `i₁` è a `I`: vista cattiva 2
  exact Or.inr (Or.inr (not_reach_of_mu_row (muMsgs_ne_zero_of_rsIμ hj₁)
    (by rw [hall i₁]; intro h; cases h)))


/-- **Downgrade da `M` / grant di `S`.** Il grant di `S` richiede nessuna riga a `M`, ma il
downgrade consuma un `rsIμ` in volo su `i₁`: un token `M` per `i₁` con la riga `i₁` non a `M`
è la vista cattiva 2 (`not_reach_of_mu_row`), sia con `i₁ = i₂` sia con `i₁ ≠ i₂`. -/
theorem old_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨_, _, hnoM, _⟩ := grantS_inv h₂
  -- un `rsIμ` in volo su `i₁` mentre la riga `i₁` non è a `M`: vista cattiva 2
  exact Or.inr (Or.inr (not_reach_of_mu_row (muMsgs_ne_zero_of_rsIμ hj₁) (hnoM i₁)))


/-- Downgrade da `M` di `i₁` e invalidate mirato `rqIμ` verso `i₂`. Con `i₁ ≠ i₂` il diamante:
l'invalidate non tocca l'`rsIμ v` e la richiesta di `k` sopravvive alla cancellazione (spostata
se `k = i₁`). Con `i₁ = i₂` la riga va a `I` e l'invalidate non scatta più da `s'`: il downgrade
da `s''` arriva esattamente a `invMSt s' i₂` (invalidate assorbito). -/
theorem old_downgrade_from_M_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s₁ ∧
    s₁ = invMSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  obtain ⟨⟨j', hrq⟩, hM, rfl⟩ := invalidateM_inv h₂
  -- l'`rsIμ v` in `queue_cip i₁` non è toccato dall'invalidate
  have hj' : ((invMSt s i₂).parent.queue_cip i₁)[j]? = some (CPEvent.rsIμ v) := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` arriva a `invMSt s' i₁`
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq : q = i₁
        · subst hq; simp only [downgradeMSt, invMSt, update_Fin_gss]
        · simp only [downgradeMSt, invMSt, update_Fin_gso2 _ _ _ _ hq]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    -- la richiesta di `k` sopravvive alla cancellazione dell'`rsIμ` (spostata se `k = i₁`)
    have hsurv : ∀ x : CPEvent, x ≠ CPEvent.rsIμ v → (s.parent.queue_cip k)[j']? = some x →
        ∃ j'' : Nat, ((downgradeMSt s v i₁ j).parent.queue_cip k)[j'']? = some x := by
      intro x hx hx'
      by_cases hk : k = i₁
      · subst hk
        have hjj : j' ≠ j := by
          intro h; rw [h, hj] at hx'; exact hx (Option.some.inj hx').symm
        rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
        · -- prima della posizione cancellata: stessa posizione
          refine ⟨j', ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_lt hlt]; exact hx'
        · -- dopo la posizione cancellata: scala di uno
          refine ⟨j' - 1, ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hx'
      · exact ⟨j', by simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hk]; exact hx'⟩
    -- la riga `i₂` resta `M` dopo il downgrade di `i₁`
    have hM' : (downgradeMSt s v i₁ j).parent.shared_state i₂ = Bstate.M := by
      simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']; exact hM
    -- l'invalidate da `s'`, con la stessa regola (`rqM` oppure `rqS`)
    have hinv : ∃ t, msi_step_internal (downgradeMSt s v i₁ j)
        (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) t
        ∧ t = invMSt (downgradeMSt s v i₁ j) i₂ := by
      rcases hrq with hrq | hrq
      · obtain ⟨j'', hj''⟩ := hsurv _ (by intro h; cases h) hrq
        exact ⟨_, msi_step_internal.parent_upd_queue _ _ _ i₂
          (parent_msi_step.upgrade_to_M_invalid_all _ k i₂ j'' hj'' hM'), rfl⟩
      · obtain ⟨j'', hj''⟩ := hsurv _ (by intro h; cases h) hrq
        exact ⟨_, msi_step_internal.parent_upd_queue _ _ _ i₂
          (parent_msi_step.upgrade_to_M_invalid_all3 _ k i₂ j'' hj'' hM'), rfl⟩
    obtain ⟨t, ht, rfl⟩ := hinv
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'),
      msi_step_congr ht ?eq⟩
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl


/-- Downgrade da `M` di `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`, un `rqM` pendente
da un `k` qualsiasi). Con `i₁ ≠ i₂` il diamante: la riga `i₂` e l'`rsIμ v` non cambiano e l'`rqM`
di `k` sopravvive alla cancellazione (spostato se `k = i₁`). Con `i₁ = i₂` la riga va a `I`:
il downgrade da `s''` arriva esattamente a `invSSt s' i₂` (invalidate assorbito). -/
theorem old_downgrade_from_M_rq1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s₁ ∧
    s₁ = invSSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  obtain ⟨⟨k, j', hrq⟩, hS, rfl⟩ := invalidateS_inv h₂
  -- l'`rsIμ v` in `queue_cip i₁` non è toccato dall'invalidate
  have hj' : ((invSSt s i₂).parent.queue_cip i₁)[j]? = some (CPEvent.rsIμ v) := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` arriva a `invSSt s' i₁`
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq : q = i₁
        · subst hq; simp only [downgradeMSt, invSSt, update_Fin_gss]
        · simp only [downgradeMSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    -- l'`rqM` di `k` sopravvive alla cancellazione dell'`rsIμ` (spostato se `k = i₁`)
    have hsurv : ∃ j'' : Nat, ((downgradeMSt s v i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqM := by
      by_cases hk : k = i₁
      · subst hk
        have hjj : j' ≠ j := by
          intro h; rw [h, hj] at hrq; cases hrq
        rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
        · -- prima della posizione cancellata: stessa posizione
          refine ⟨j', ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_lt hlt]; exact hrq
        · -- dopo la posizione cancellata: scala di uno
          refine ⟨j' - 1, ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hrq
      · exact ⟨j', by simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hk]; exact hrq⟩
    obtain ⟨j'', hj''⟩ := hsurv
    -- la riga `i₂` resta `S` dopo il downgrade di `i₁`
    have hS' : (downgradeMSt s v i₁ j).parent.shared_state i₂ = Bstate.S := by
      simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₂ j'' hj'' hS')) ?eq⟩
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl


/-- Downgrade da `M` di `i₁` e invalidate `rqIσ` verso `i₂` per la richiesta `rqS` di `k ≠ i₂`
(riga `i₂ = S`). Con `i₁ ≠ i₂` il diamante: la riga `i₂` e l'`rsIμ v` non cambiano e l'`rqS`
di `k` sopravvive alla cancellazione (spostato se `k = i₁`). Con `i₁ = i₂` la riga va a `I`:
il downgrade da `s''` arriva esattamente a `invSSt s' i₂` (invalidate assorbito). -/
theorem old_downgrade_from_M_rq1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s₁ ∧
    s₁ = invSSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  obtain ⟨⟨j', hrq⟩, hki, hS, rfl⟩ := invalidateS2_inv h₂
  -- l'`rsIμ v` in `queue_cip i₁` non è toccato dall'invalidate
  have hj' : ((invSSt s i₂).parent.queue_cip i₁)[j]? = some (CPEvent.rsIμ v) := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` arriva a `invSSt s' i₁`
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq : q = i₁
        · subst hq; simp only [downgradeMSt, invSSt, update_Fin_gss]
        · simp only [downgradeMSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    -- l'`rqS` di `k` sopravvive alla cancellazione dell'`rsIμ` (spostato se `k = i₁`)
    have hsurv : ∃ j'' : Nat, ((downgradeMSt s v i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqS := by
      by_cases hk : k = i₁
      · subst hk
        have hjj : j' ≠ j := by
          intro h; rw [h, hj] at hrq; cases hrq
        rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
        · -- prima della posizione cancellata: stessa posizione
          refine ⟨j', ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_lt hlt]; exact hrq
        · -- dopo la posizione cancellata: scala di uno
          refine ⟨j' - 1, ?_⟩
          simp only [downgradeMSt, update_Fin_gss]
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hrq
      · exact ⟨j', by simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hk]; exact hrq⟩
    obtain ⟨j'', hj''⟩ := hsurv
    -- la riga `i₂` resta `S` dopo il downgrade di `i₁`
    have hS' : (downgradeMSt s v i₁ j).parent.shared_state i₂ = Bstate.S := by
      simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j hj'),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₂ j'' hj'' hki hS')) ?eq⟩
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · exact rfl
      · intro q; exact rfl
      · intro q; exact rfl
      · intro q; exact rfl


/-- Due downgrade da `S` (ciascuno consuma un `rsIσ`). Con `i₁ ≠ i₂` diamante. Con `i₁ = i₂`:
se `j₁ = j₂` è lo stesso passo e `s' = s''`; altrimenti diamante con le posizioni scalate
(togliere prima `b` e poi `a < b` è come togliere prima `a` e poi `b - 1`). -/
theorem old_downgrade_from_M_rq2_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List CPEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  -- `s'` e `s''` sono i record espliciti dei due downgrade
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, rfl⟩ := downgradeS_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice
    subst hne
    by_cases hj : j₁ = j₂
    · -- stessa posizione: stesso passo, stesso stato
      subst hj
      exact Or.inr (Or.inl rfl)
    rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
    · -- j₁ < j₂: il primo `rsIσ` resta in j₁ dopo aver tolto j₂; il secondo scala in j₂ - 1
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₁ ?g1),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ (j₂ - 1) ?g2)) ?eq⟩
      case g1 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
      case g2 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss, key _ _ _ hlt]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · simp only [downgradeSSt]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss, key _ _ _ hlt]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          simp only [downgradeSSt]
    · -- j₂ < j₁: simmetrico, il primo `rsIσ` scala in j₁ - 1 dopo aver tolto j₂
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ (j₁ - 1) ?g1),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₂ ?g2)) ?eq⟩
      case g1 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
      case g2 =>
        simp only [downgradeSSt, update_Fin_gss]
        rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss, key _ _ _ hgt]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · simp only [downgradeSSt]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, update_Fin_gss, key _ _ _ hgt]
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          simp only [downgradeSSt]
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₁ ?g1),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq2 _ i₂ j₂ ?g2)) ?eq⟩
    -- l'`rsIσ` in `queue_cip i₁` non è toccato dal downgrade su `i₂`
    case g1 => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- l'`rsIσ` in `queue_cip i₂` non è toccato dal downgrade su `i₁`
    case g2 => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
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
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        simp only [downgradeSSt]


/-- **Downgrade da `S` / grant di `M`.** Con `i₁ = i₂` il grant vuole la riga `i₁` a `I` mentre
un `rsIσ` è in volo su `i₁`: vista cattiva 2 (`not_reach_of_sig_row`). Con `i₁ ≠ i₂` i passi toccano
indici diversi e il grant resta abilitato da `s'` (il downgrade porta `i₁` a `I`): diamante. -/
theorem old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, hall, rfl⟩ := grantM_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: un `rsIσ` in volo su `i₁` con la riga `i₁` a `I` (vista cattiva 2)
    subst hne
    exact Or.inr (Or.inr (not_reach_of_sig_row (sigMsgs_ne_zero_of_rsIσ hj₁)
      (by rw [hall i₁]; intro h; cases h)))
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₁ ?g₁),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₂ j₂ ?g₂ ?g₃)) ?eq⟩
    -- l'`rsIσ` in `queue_cip i₁` non è toccato dal grant a `i₂`
    case g₁ => simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- l'`rqM` in `queue_cip i₂` non è toccato dal downgrade di `i₁`
    case g₂ => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    -- dopo il downgrade tutte le righe sono a `I`: `i₁` per costruzione, le altre da `hall`
    case g₃ =>
      intro q
      by_cases hq : q = i₁
      · subst hq; simp only [downgradeSSt, update_Fin_gss]
      · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]; exact hall q
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
              update_Fin_gso2 _ _ _ _ hq₂]
      · simp only [grantMSt, downgradeSSt]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
              update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantMSt, downgradeSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁,
              update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₂ : q = i₂
        · subst hq₂; simp only [grantMSt, downgradeSSt, update_Fin_gss]
        · simp only [grantMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- **Downgrade da `S` / grant di `S`.** Con `i₁ ≠ i₂` il diamante: il downgrade porta la riga
`i₁` a `I` e il grant resta abilitato. Con `i₁ = i₂` la richiesta viene comunque servita: da
entrambi i lati la cache (in `I`, altrimenti vista cattiva 3) prende l'`rsS`, rilascia `rsIσ` e
il parent lo consuma; i due cammini di 4 passi riconvergono (le due cancellazioni in `queue_cip`
commutano). -/
theorem old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨
  (∃ t₁ t₂ t₃ u₁ u₂ u₃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) t₁ ∧
    msi_step_internal t₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₂) t₂ ∧
    msi_step_internal t₂ (.cache .ld_rq_data_not_availableS i₂) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) u₁ ∧
    msi_step_internal u₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₂) u₂ ∧
    msi_step_internal u₂ (.cache .ld_rq_data_not_availableS i₂) u₃ ∧
    msi_step_internal u₃ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hI := grantS_rowI h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (Or.inr (not_reach_of_not_synced hsync)))
  -- `s'` e `s''` sono i record espliciti dei due passi del parent
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, hnoM, rfl⟩ := grantS_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: i due messaggi sono diversi, quindi `j₁ ≠ j₂`
    subst hne
    have hjne : j₁ ≠ j₂ := by
      intro h; subst h; rw [hj₁] at hj₂; cases hj₂
    -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
    have key : ∀ (l : List CPEvent) (a b : Nat), a < b →
        (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
      intro l
      induction l with
      | nil => intro a b _; simp
      | cons x xs ih =>
        intro a b hab
        cases a with
        | zero =>
          cases b with
          | zero => omega
          | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
        | succ a =>
          cases b with
          | zero => omega
          | succ b =>
            cases b with
            | zero => omega
            | succ b =>
              simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
              rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
    cases hst : (s.caches i₁).state with
    | M =>
      -- cache in `M` con il proprio `rsIσ` in volo: vista cattiva 3
      exact Or.inr (Or.inr (Or.inr (not_reach_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj₁))))))
    | S =>
      -- cache in `S` con il proprio `rsIσ` in volo: vista cattiva 3
      exact Or.inr (Or.inr (Or.inr (not_reach_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj₁))))))
    | I =>
      -- posizioni dell'`rsIσ` dopo il grant e dell'`rqS` dopo il downgrade; le due cancellazioni commutano
      obtain ⟨j₁', j₂', hj₁', hj₂', hkey⟩ : ∃ j₁' j₂' : Nat,
          ((s.parent.queue_cip i₁).eraseIdx j₂)[j₁']? = some CPEvent.rsIσ ∧
          ((s.parent.queue_cip i₁).eraseIdx j₁)[j₂']? = some CPEvent.rqS ∧
          ((s.parent.queue_cip i₁).eraseIdx j₂).eraseIdx j₁'
            = ((s.parent.queue_cip i₁).eraseIdx j₁).eraseIdx j₂' := by
        rcases Nat.lt_or_gt_of_ne hjne with hlt | hgt
        · -- j₁ < j₂: l'`rsIσ` resta in j₁, l'`rqS` scala in j₂ - 1
          refine ⟨j₁, j₂ - 1, ?_, ?_, key _ _ _ hlt⟩
          · rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
          · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
        · -- j₂ < j₁: l'`rqS` resta in j₂, l'`rsIσ` scala in j₁ - 1
          refine ⟨j₁ - 1, j₂, ?_, ?_, (key _ _ _ hgt).symm⟩
          · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
          · rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
      refine Or.inr (Or.inl ⟨_, _, _, _, _, _, _,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₁' ?l1),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?l2 ?l3),
        msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available1 _ ?l4),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁
            (((s.parent.queue_cip i₁).eraseIdx j₂).eraseIdx j₁').length ?l5),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j₂' ?r1 ?rI ?r2),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?r3 ?r4),
        msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available1 _ ?r5),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq2 _ i₁
            (((s.parent.queue_cip i₁).eraseIdx j₁).eraseIdx j₂').length ?r6)) ?eq⟩)
      -- cammino da `s''` (grant fatto): downgrade, presa dell'`rsS`, rilascio, downgrade
      case l1 => simp only [grantSSt, update_Fin_gss]; exact hj₁'
      case l2 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
      case l3 => simp only [grantSSt, update_Fin_gss]; exact hst
      case l4 => simp only [update_Fin_gss]
      case l5 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
      -- cammino da `s'` (downgrade fatto): grant, presa dell'`rsS`, rilascio, downgrade
      case r1 => simp only [downgradeSSt, update_Fin_gss]; exact hj₂'
      case rI => simp only [downgradeSSt, update_Fin_gss]
      case r2 =>
        intro k
        by_cases hk : k = i₁
        · subst hk; simp only [downgradeSSt, update_Fin_gss]; exact Bstate.noConfusion
        · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hk]; exact hnoM k
      case r3 => simp only [downgradeSSt, update_Fin_gss]; exact lst_get _ _
      case r4 => simp only [downgradeSSt, update_Fin_gss]; exact hst
      case r5 => simp only [update_Fin_gss]
      case r6 => simp only [downgradeSSt, update_Fin_gss]; exact lst_get _ _
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, grantSSt, update_Fin_gss, lst_erase, hkey]
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq]
        · simp only [downgradeSSt, grantSSt]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, grantSSt, update_Fin_gss]
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, grantSSt, update_Fin_gss, lst_erase, hkey]
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq
            simp only [downgradeSSt, grantSSt, update_Fin_gss, lst_erase]
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq]
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq2 _ i₁ j₁ ?g1),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₂ j₂ ?g2 ?gI ?g3)) ?eq⟩
    -- l'`rsIσ` in `queue_cip i₁` non è toccato dal grant a `i₂`
    case g1 => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- l'`rqS` in `queue_cip i₂` non è toccato dal downgrade di `i₁`
    case g2 => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    -- la riga `i₂` non è toccata dal downgrade di `i₁`: resta `I` per il nuovo guard
    case gI => simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
    -- nessuna riga a `M`: la riga `i₁` è ora `I`, le altre sono quelle di `s`
    case g3 =>
      intro k
      by_cases hk : k = i₁
      · subst hk; simp only [downgradeSSt, update_Fin_gss]; exact Bstate.noConfusion
      · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hk]; exact hnoM k
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · simp only [downgradeSSt, grantSSt]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [downgradeSSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [downgradeSSt, grantSSt, update_Fin_gss]
          · simp only [downgradeSSt, grantSSt, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` di `i₁` e invalidate `rqIμ` verso `i₂` (richiesta di `k`).
Con `i₁ ≠ i₂` i due passi commutano: il downgrade tocca solo `cip`/riga di `i₁`, l'invalidate
solo `pci i₂`, e la richiesta di `k` sopravvive alla cancellazione (slitta se `k = i₁`).
Con `i₁ = i₂` il downgrade fatto da `s''` arriva esattamente a `invMSt s' i₂`. -/
theorem old_downgrade_from_M_rq2_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s₁ ∧
    s₁ = invMSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  obtain ⟨⟨j', hj'⟩, hM, rfl⟩ := invalidateM_inv h₂
  -- l'`rsIσ` è ancora in `cip i₁` dopo l'invalidate (che tocca solo `pci`)
  have hj₀ : ((invMSt s i₂).parent.queue_cip i₁)[j]? = some CPEvent.rsIσ := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` assorbe l'invalidate
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq : q = i₁
        · subst hq; simp only [invMSt, downgradeSSt, update_Fin_gss]
        · simp only [invMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
  · -- indici distinti: il diamante
    have hM' : (downgradeSSt s i₁ j).parent.shared_state i₂ = Bstate.M := by
      simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hM
    -- la richiesta di `k` sopravvive al downgrade (slitta oltre `j` se `k = i₁`)
    have hsurv : ∃ j'' : Nat,
        ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqM
        ∨ ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqS := by
      by_cases hk : k = i₁
      · subst hk
        simp only [downgradeSSt, update_Fin_gss]
        have hne' : j' ≠ j := by
          intro h; subst h; rcases hj' with h' | h' <;> (rw [hj] at h'; cases h')
        rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
        · exact ⟨j', by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj'⟩
        · exact ⟨j' - 1, by
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hj'⟩
      · exact ⟨j', by simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hk]; exact hj'⟩
    obtain ⟨j'', hj''⟩ := hsurv
    -- l'invalidate da `s'`: la stessa regola (`rqM` o `rqS`) di prima
    have hIM : parent_msi_step (downgradeSSt s i₁ j).parent
        (.upd_queue (.upgrade_to_M_invalid_all k) i₂)
        { (downgradeSSt s i₁ j).parent with
            queue_pci := update_Fin i₂ ((downgradeSSt s i₁ j).parent.queue_pci i₂ ++ [PCEvent.rqIμ])
                           (downgradeSSt s i₁ j).parent.queue_pci } := by
      rcases hj'' with h | h
      · exact parent_msi_step.upgrade_to_M_invalid_all _ k i₂ j'' h hM'
      · exact parent_msi_step.upgrade_to_M_invalid_all3 _ k i₂ j'' h hM'
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂ hIM) ?eq⟩
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, downgradeSSt, update_Fin_gss,
            update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, downgradeSSt, update_Fin_gss,
              update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
          · simp only [invMSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` di `i₁` e invalidate `rqIσ` verso `i₂` (un `rqM` pendente da qualche `k`).
Con `i₁ ≠ i₂` i due passi commutano: l'`rqM` di `k` sopravvive alla cancellazione (slitta se
`k = i₁`) e la riga `i₂ = S` non è toccata. Con `i₁ = i₂` il downgrade fatto da `s''` arriva
esattamente a `invSSt s' i₂`. -/
theorem old_downgrade_from_M_rq2_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s₁ ∧
    s₁ = invSSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  obtain ⟨⟨k, j', hj'⟩, hS, rfl⟩ := invalidateS_inv h₂
  -- l'`rsIσ` è ancora in `cip i₁` dopo l'invalidate (che tocca solo `pci`)
  have hj₀ : ((invSSt s i₂).parent.queue_cip i₁)[j]? = some CPEvent.rsIσ := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` assorbe l'invalidate
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq : q = i₁
        · subst hq; simp only [invSSt, downgradeSSt, update_Fin_gss]
        · simp only [invSSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
  · -- indici distinti: il diamante
    have hS' : (downgradeSSt s i₁ j).parent.shared_state i₂ = Bstate.S := by
      simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hS
    -- l'`rqM` di `k` sopravvive al downgrade (slitta oltre `j` se `k = i₁`)
    have hsurv : ∃ j'' : Nat, ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqM := by
      by_cases hk : k = i₁
      · subst hk
        simp only [downgradeSSt, update_Fin_gss]
        have hne' : j' ≠ j := by intro h; subst h; rw [hj] at hj'; cases hj'
        rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
        · exact ⟨j', by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj'⟩
        · exact ⟨j' - 1, by
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hj'⟩
      · exact ⟨j', by simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hk]; exact hj'⟩
    obtain ⟨j'', hj''⟩ := hsurv
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₂ j'' hj'' hS')) ?eq⟩
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, downgradeSSt, update_Fin_gss,
            update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, downgradeSSt, update_Fin_gss,
              update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
          · simp only [invSSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Downgrade da `S` di `i₁` e invalidate `rqIσ` verso `i₂` per la richiesta `rqS` di `k ≠ i₂`.
Con `i₁ ≠ i₂` i due passi commutano: l'`rqS` di `k` sopravvive alla cancellazione (slitta se
`k = i₁`), la riga `i₂ = S` e la condizione `i₂ ≠ k` restano. Con `i₁ = i₂` il downgrade fatto
da `s''` arriva esattamente a `invSSt s' i₂`. -/
theorem old_downgrade_from_M_rq2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s₁ ∧
    s₁ = invSSt s' i₂)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  obtain ⟨⟨j', hj'⟩, hik, hS, rfl⟩ := invalidateS2_inv h₂
  -- l'`rsIσ` è ancora in `cip i₁` dopo l'invalidate (che tocca solo `pci`)
  have hj₀ : ((invSSt s i₂).parent.queue_cip i₁)[j]? = some CPEvent.rsIσ := hj
  by_cases hne : i₁ = i₂
  · -- stesso indice: il downgrade da `s''` assorbe l'invalidate
    subst hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀), ?eq⟩)
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq : q = i₁
        · subst hq; simp only [invSSt, downgradeSSt, update_Fin_gss]
        · simp only [invSSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
  · -- indici distinti: il diamante
    have hS' : (downgradeSSt s i₁ j).parent.shared_state i₂ = Bstate.S := by
      simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hS
    -- l'`rqS` di `k` sopravvive al downgrade (slitta oltre `j` se `k = i₁`)
    have hsurv : ∃ j'' : Nat, ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqS := by
      by_cases hk : k = i₁
      · subst hk
        simp only [downgradeSSt, update_Fin_gss]
        have hne' : j' ≠ j := by intro h; subst h; rw [hj] at hj'; cases hj'
        rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
        · exact ⟨j', by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj'⟩
        · exact ⟨j' - 1, by
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hj'⟩
      · exact ⟨j', by simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hk]; exact hj'⟩
    obtain ⟨j'', hj''⟩ := hsurv
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁ (parent_msi_step.downgrade_from_M_rq2 _ i₁ j hj₀),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₂ j'' hj'' hik hS')) ?eq⟩
    case eq =>
      refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      case hc =>
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, downgradeSSt, update_Fin_gss,
            update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, downgradeSSt, update_Fin_gss,
              update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
          · simp only [invSSt, downgradeSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Due grant `M` non commutano mai: la guardia `∀ i, shared_state i = I` è distrutta dal grant
stesso. La riconvergenza è servire le due richieste una dopo l'altra (7 passi per lato,
`grantM_grantM_reconverge`), sia con `i₁ ≠ i₂` sia con `i₁ = i₂` e posizioni distinte; stessa
posizione dà `s' = s''`. Una cache servita non in `I` (riga `I` per `hall`) è una vista cattiva. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
    msi_step_internal s'  (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
    msi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
    msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
    msi_step_internal t₄ (.cache (.upgrade_from_I_rs s.parent.value) i₂) t₅ ∧
    msi_step_internal t₅ (.cache .rq_data_not_available i₂) t₆ ∧
    msi_step_internal t₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) s''' ∧
    msi_step_internal s'' (.cache (.upgrade_from_I_rs s.parent.value) i₂) u₁ ∧
    msi_step_internal u₁ (.cache .rq_data_not_available i₂) u₂ ∧
    msi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) u₃ ∧
    msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
    msi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
    msi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
    msi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, hall, rfl⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grantM_inv h₂
  -- le due cache devono essere in `I`: la riga è `I` (`hall`), altrimenti vista cattiva
  cases hI₁ : (s.caches i₁).state with
  | M => exact Or.inr (Or.inr (not_reach_of_M hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | S => exact Or.inr (Or.inr (not_reach_of_S hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | I =>
    cases hI₂ : (s.caches i₂).state with
    | M => exact Or.inr (Or.inr (not_reach_of_M hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | S => exact Or.inr (Or.inr (not_reach_of_S hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | I =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: stessa posizione dà lo stesso stato, altrimenti i due cammini
        subst hne
        by_cases hj : j₁ = j₂
        · subst hj; exact Or.inr (Or.inl rfl)
        · exact Or.inl (grantM_grantM_reconverge (Or.inr hj) hj₁ hj₂ hall hI₁ hI₂)
      · -- indici distinti: i due cammini
        exact Or.inl (grantM_grantM_reconverge (Or.inl hne) hj₁ hj₂ hall hI₁ hI₂)


/-- Il grant di `M` a `i₁` e il grant di `S` a `i₂` non commutano: ciascuno distrugge la guardia
dell'altro. La riconvergenza è servire le due richieste una dopo l'altra (7 passi per lato,
`grantM_grantS_reconverge`), sia con `i₁ = i₂` (posizioni diverse, `rqM ≠ rqS`) sia con `i₁ ≠ i₂`.
Le due cache devono essere in `I` (righe tutte a `I`), altrimenti `¬ Reach s` (vista cattiva 3). -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
    msi_step_internal s'  (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
    msi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
    msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) t₄ ∧
    msi_step_internal t₄ (.cache (.upgrade_from_I_rsS s.parent.value) i₂) t₅ ∧
    msi_step_internal t₅ (.cache .ld_rq_data_not_availableS i₂) t₆ ∧
    msi_step_internal t₆ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''' ∧
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS s.parent.value) i₂) u₁ ∧
    msi_step_internal u₁ (.cache .ld_rq_data_not_availableS i₂) u₂ ∧
    msi_step_internal u₂ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) u₃ ∧
    msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
    msi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
    msi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
    msi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, hall, rfl⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grantS_inv h₂
  -- la cache `i₁` deve essere in `I`: la riga `i₁` è a `I` (vista cattiva 3 altrimenti)
  cases hI₁ : (s.caches i₁).state with
  | M => exact Or.inr (Or.inr (not_reach_of_M hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | S => exact Or.inr (Or.inr (not_reach_of_S hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | I =>
    -- la cache `i₂` deve essere in `I`: la riga `i₂` è a `I` (vista cattiva 3 altrimenti)
    cases hI₂ : (s.caches i₂).state with
    | M => exact Or.inr (Or.inr (not_reach_of_M hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | S => exact Or.inr (Or.inr (not_reach_of_S hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | I => exact Or.inl (grantM_grantS_reconverge hj₁ hj₂ hall hI₁ hI₂)


/-- **Grant di `M` / invalidate mirato.** Il grant richiede tutte le righe a `I`, l'invalidate
richiede la riga `i₂` a `M`: le due guardie si contraddicono, la coppia è vuota. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, hM, _⟩ := invalidateM_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `M` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hM


/-- **Grant di `M` / invalidate `rqIσ` (`invalid_allS`).** Il grant richiede tutte le righe a
`I`, l'invalidate richiede la riga `i₂` a `S`: guardie contraddittorie, coppia vuota. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, hS, _⟩ := invalidateS_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `S` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hS


/-- **Grant di `M` / invalidate `rqIσ` mirato (`upgrade_to_S_invalid_2_rq1S k`).** Il grant
richiede tutte le righe a `I`, l'invalidate richiede la riga `i₂` a `S`: guardie
contraddittorie, coppia vuota. -/
theorem old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, _, hS, _⟩ := invalidateS2_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `S` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hS


/-- Due grant di `S`: con indici distinti commutano (diamante: la guardia "riga a `I`" di ciascuno
non è toccata dall'altro); con lo stesso indice e la stessa posizione danno lo stesso stato; con lo
stesso indice e posizioni distinte il secondo grant non può più scattare (riga a `S`) e si riconverge
servendo le due richieste una dopo l'altra (`grantS_grantS_reconverge`), se la cache è in `I`. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨
  (∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
    msi_step_internal s'  (.cache (.upgrade_from_I_rsS s.parent.value) i₁) t₁ ∧
    msi_step_internal t₁ (.cache .ld_rq_data_not_availableS i₁) t₂ ∧
    msi_step_internal t₂ (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) t₄ ∧
    msi_step_internal t₄ (.cache (.upgrade_from_I_rsS s.parent.value) i₂) t₅ ∧
    msi_step_internal t₅ (.cache .ld_rq_data_not_availableS i₂) t₆ ∧
    msi_step_internal t₆ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''' ∧
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS s.parent.value) i₂) u₁ ∧
    msi_step_internal u₁ (.cache .ld_rq_data_not_availableS i₂) u₂ ∧
    msi_step_internal u₂ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) u₃ ∧
    msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) u₄ ∧
    msi_step_internal u₄ (.cache (.upgrade_from_I_rsS s.parent.value) i₁) u₅ ∧
    msi_step_internal u₅ (.cache .ld_rq_data_not_availableS i₁) u₆ ∧
    msi_step_internal u₆ (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- le guardie dei due grant: le righe di `i₁` e `i₂` sono a `I`
  have hI₁ := grantS_rowI h₁
  have hI₂ := grantS_rowI h₂
  -- `s'` e `s''` sono i record espliciti dei due grant
  obtain ⟨j₁, hj₁, hnoM, rfl⟩ := grantS_inv h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grantS_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice
    subst hne
    by_cases hj : j₁ = j₂
    · -- stessa posizione: stesso passo, stesso stato
      subst hj
      exact Or.inr (Or.inr (Or.inl rfl))
    · -- posizioni distinte: la cache deve essere in `I` (la riga è `I`), poi i due cammini
      cases hc : (s.caches i₁).state with
      | M => exact Or.inr (Or.inr (Or.inr (not_reach_of_M hc (Or.inr (Or.inr (by simp [hI₁]))))))
      | S => exact Or.inr (Or.inr (Or.inr (not_reach_of_S hc (Or.inr (Or.inr (by simp [hI₁]))))))
      | I => exact Or.inr (Or.inl (grantS_grantS_reconverge hj hj₁ hj₂ hI₁ hnoM hc))
  · -- indici distinti: il diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    -- dopo un grant di `S` su `i` nessuna riga è a `M`
    have hnoM' : ∀ (i : Fin n) (k : Fin n),
        ¬(update_Fin i Bstate.S s.parent.shared_state k = Bstate.M) := by
      intro i k
      by_cases hk : k = i
      · subst hk; rw [update_Fin_gss]; exact fun h => Bstate.noConfusion h
      · rw [update_Fin_gso2 _ _ _ _ hk]; exact hnoM k
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j₁ ?g1 ?hI1 ?d1),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₂ j₂ ?g2 ?hI2 ?d2)) ?eq⟩
    -- l'`rqS` in `queue_cip i₁` non è toccato dal grant su `i₂`
    case g1 => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    -- la riga di `i₁` non è toccata dal grant su `i₂`
    case hI1 => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne]; exact hI₁
    -- nessuna riga a `M` dopo il grant su `i₂`
    case d1 => intro k; simp only [grantSSt]; exact hnoM' i₂ k
    -- l'`rqS` in `queue_cip i₂` non è toccato dal grant su `i₁`
    case g2 => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    -- la riga di `i₂` non è toccata dal grant su `i₁`
    case hI2 => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']; exact hI₂
    -- nessuna riga a `M` dopo il grant su `i₁`
    case d2 => intro k; simp only [grantSSt]; exact hnoM' i₁ k
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
      · simp only [grantSSt]
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
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- **Grant di `S` / invalidate mirato.** Il grant di `S` richiede nessuna riga a `M`,
l'invalidate richiede la riga `i₂` a `M`: guardie contraddittorie, coppia vuota. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  obtain ⟨_, _, hnoM, _⟩ := grantS_inv h₁
  obtain ⟨_, hM, _⟩ := invalidateM_inv h₂
  -- la riga `i₂` non è a `M` per il grant di `S` ma è a `M` per l'invalidate: assurdo
  exact absurd hM (hnoM i₂)


/-- Grant di `S` a `i₁` e `invalid_allS` a `i₂` (un `rqM` pendente da `k`, riga `i₂ = S`).
Con `i₁ ≠ i₂` diamante (se `k = i₁` l'`rqM` scorre oltre l'`rqS` cancellato dal grant).
Con `i₁ = i₂` la cache riceve `rsS` e `rqIσ` in ordine opposto sui due lati: in `I` prende
il grant e poi cede (2 + 2 passi), in `S` cede e poi prende il grant; in `M` è `not_reach_of_M`. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
  (∃ x y t₁ u₁ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) x ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) y ∧
    msi_step_internal x (.cache (.upgrade_from_I_rsS s.parent.value) i₁) t₁ ∧
    msi_step_internal t₁ (.cache .downgrade_from_S_rsS i₁) s''' ∧
    msi_step_internal y (.cache (.upgrade_from_I_rsS s.parent.value) i₁) u₁ ∧
    msi_step_internal u₁ (.cache .downgrade_from_S_rsS i₁) s''')
  ∨
  (∃ x y t₁ u₁ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) x ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) y ∧
    msi_step_internal x (.cache .downgrade_from_S_rsS i₁) t₁ ∧
    msi_step_internal t₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₁) s''' ∧
    msi_step_internal y (.cache .downgrade_from_S_rsS i₁) u₁ ∧
    msi_step_internal u₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₁) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (Or.inr (Or.inr (not_reach_of_not_synced hsync))))
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  obtain ⟨⟨k, j', hk⟩, hS, rfl⟩ := invalidateS_inv h₂
  -- l'`rqM` del richiedente `k` sopravvive al grant (scorre di uno se `k = i₁` e `j < j'`)
  have hk' : ∃ j'' : Nat, ((grantSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqM := by
    simp only [grantSSt]
    by_cases hki : k = i₁
    · subst hki
      rw [update_Fin_gss]
      have hjj : j' ≠ j := by
        intro h; subst h; rw [hj] at hk; cases hk
      rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
      · exact ⟨j', by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hk⟩
      · exact ⟨j' - 1, by
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hk⟩
    · exact ⟨j', by rw [update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
  obtain ⟨j'', hk''⟩ := hk'
  by_cases hne : i₁ = i₂
  · -- stesso indice: `x` = grant da `s''`, `y` = invalidate da `s'`, poi la cache riconverge
    subst hne
    cases hst : (s.caches i₁).state with
    | I =>
      -- cache in `I`: prende il grant `rsS` e poi cede sull'`rqIσ`
      refine Or.inr (Or.inl ⟨_, _, _, _, _,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?gx1 ?gxI ?gx2),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' hk'' ?gy),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ s.parent.value
            (s.parent.queue_pci i₁ ++ [PCEvent.rqIσ]).length ?tx1 ?tx2),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?hx1 ?hx2),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ s.parent.value
            (s.parent.queue_pci i₁).length ?ty1 ?ty2),
        msi_step_congr (msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?hy1 ?hy2))
          ?eq⟩)
      -- il grant da `s''`: `rqS` e righe non toccati dall'invalidate
      case gx1 => exact hj
      case gxI => exact hI
      case gx2 => exact hnoM
      -- l'invalidate da `s'`: la riga `i₁` è `S` dopo il grant
      case gy => simp only [grantSSt, update_Fin_gss]
      -- da `x`: l'`rsS` è in fondo a `pci i₁ ++ [rqIσ]`, cache in `I`
      case tx1 => simp only [invSSt, update_Fin_gss]; exact lst_get _ _
      case tx2 => simp only [invSSt, update_Fin_gss]; exact hst
      -- poi l'`rqIσ` è in fondo a `pci i₁`, cache in `S`
      case hx1 => simp only [invSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
      case hx2 => simp only [invSSt, update_Fin_gss]
      -- da `y`: l'`rsS` è in posizione `(pci i₁).length` di `pci i₁ ++ [rsS] ++ [rqIσ]`
      case ty1 => simp only [grantSSt, update_Fin_gss]; exact lst_get2 _ _ _
      case ty2 => simp only [grantSSt, update_Fin_gss]; exact hst
      -- poi l'`rqIσ` è in fondo a `pci i₁ ++ [rqIσ]`, cache in `S`
      case hy1 => simp only [grantSSt, update_Fin_gss, lst_erase2]; exact lst_get _ _
      case hy2 => simp only [grantSSt, update_Fin_gss]
      -- i due stati finali coincidono campo per campo
      case eq =>
        refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q; rfl
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
    | S =>
      -- cache in `S`: cede sull'`rqIσ` e poi prende il grant `rsS`
      refine Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?gx1 ?gxI ?gx2),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₁ j'' hk'' ?gy),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?hx1 ?hx2),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ s.parent.value
            (s.parent.queue_pci i₁).length ?tx1 ?tx2),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.downgrade_from_M_rs1 _
            (s.parent.queue_pci i₁ ++ [PCEvent.rsS s.parent.value]).length ?hy1 ?hy2),
        msi_step_congr (msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rsS _ s.parent.value
            (s.parent.queue_pci i₁).length ?ty1 ?ty2))
          ?eq⟩))
      -- il grant da `s''`: `rqS` e righe non toccati dall'invalidate
      case gx1 => exact hj
      case gxI => exact hI
      case gx2 => exact hnoM
      -- l'invalidate da `s'`: la riga `i₁` è `S` dopo il grant
      case gy => simp only [grantSSt, update_Fin_gss]
      -- da `x`: l'`rqIσ` è in posizione `(pci i₁).length` di `pci i₁ ++ [rqIσ] ++ [rsS]`, cache in `S`
      case hx1 => simp only [invSSt, update_Fin_gss]; exact lst_get2 _ _ _
      case hx2 => simp only [invSSt, update_Fin_gss]; exact hst
      -- poi l'`rsS` è in fondo a `pci i₁ ++ [rsS]`, cache in `I`
      case tx1 => simp only [invSSt, update_Fin_gss, lst_erase2]; exact lst_get _ _
      case tx2 => simp only [invSSt, update_Fin_gss]
      -- da `y`: l'`rqIσ` è in fondo a `pci i₁ ++ [rsS] ++ [rqIσ]`, cache in `S`
      case hy1 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
      case hy2 => simp only [grantSSt, update_Fin_gss]; exact hst
      -- poi l'`rsS` è in fondo a `pci i₁ ++ [rsS]`, cache in `I`
      case ty1 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
      case ty2 => simp only [grantSSt, update_Fin_gss]
      -- i due stati finali coincidono campo per campo
      case eq =>
        refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q; rfl
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
    | M =>
      -- cache in `M` con la riga `i₁ = S`: stato incoerente
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (not_reach_of_M hst (Or.inr (Or.inr (by rw [hS]; intro h; cases h)))))))
  · -- indici distinti: diamante
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?gp1 ?gpI ?gp2),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₂ j'' hk'' ?gi)) ?eq⟩
    -- il grant da `s''`: `rqS` e righe non toccati dall'invalidate su `i₂`
    case gp1 => exact hj
    case gpI => exact hI
    case gp2 => exact hnoM
    -- l'invalidate da `s'`: la riga `i₂` non è toccata dal grant a `i₁`
    case gi => simp only [grantSSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
    -- i due stati finali coincidono campo per campo
    case eq =>
      refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · intro q; rfl
      · intro q; rfl
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Grant di `S` a `i₁` (consuma l'`rqS` in posizione `j`) e `upgrade_to_S_invalid_2_rq1S k` a `i₂`
(accoda `rqIσ`, riga `i₂ = S`, giustificato da un `rqS` pendente da `k ≠ i₂`). Con `i₁ ≠ i₂` l'effetto
dell'invalidate (`invSSt`) commuta con il grant anche quando il grant ha consumato proprio l'`rqS` che
lo giustificava: il grant da `s''` è abilitato e porta a `invSSt s' i₂`. Con `i₁ = i₂` la cache vede
`rqIσ` e `rsS` in ordine diverso: in `I` prende e poi cede, in `S` cede e poi prende, in `M` è incoerente. -/
theorem old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
  (∃ s₁,
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s₁ ∧
    s₁ = invSSt s' i₂)
  ∨
  (∃ x y t₁ u₁ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) x ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) y ∧
    msi_step_internal x (.cache (.upgrade_from_I_rsS s.parent.value) i₁) t₁ ∧
    msi_step_internal t₁ (.cache .downgrade_from_S_rsS i₁) s''' ∧
    msi_step_internal y (.cache (.upgrade_from_I_rsS s.parent.value) i₁) u₁ ∧
    msi_step_internal u₁ (.cache .downgrade_from_S_rsS i₁) s''')
  ∨
  (∃ x y t₁ u₁ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) x ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) y ∧
    msi_step_internal x (.cache .downgrade_from_S_rsS i₁) t₁ ∧
    msi_step_internal t₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₁) s''' ∧
    msi_step_internal y (.cache .downgrade_from_S_rsS i₁) u₁ ∧
    msi_step_internal u₁ (.cache (.upgrade_from_I_rsS s.parent.value) i₁) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  obtain ⟨⟨j', hk⟩, hik, hS, rfl⟩ := invalidateS2_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: la cache `i₁` riceve `rqIσ` e `rsS` nei due ordini
    subst hne
    -- qui `k ≠ i₁`, quindi l'`rqS` di `k` sopravvive al grant
    have hk'' : ((grantSSt s i₁ j).parent.queue_cip k)[j']? = some CPEvent.rqS := by
      simp only [grantSSt, update_Fin_gso _ _ _ _ hik]; exact hk
    cases hst : (s.caches i₁).state with
    | M =>
      -- cache in `M` con la riga a `S`: stato incoerente
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (not_reach_of_M hst (Or.inr (Or.inr (hnoM i₁))))))))
    | I =>
      -- cache in `I`: prende l'`rsS` e poi cede sull'`rqIσ`
      refine Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _,
        msi_step_internal.parent_upd_queue _ ?q1 _ _ ?px,
        msi_step_internal.parent_upd_queue _ ?q2 _ _ ?py,
        msi_step_internal.cache _ ?c1 _ _ ?p1,
        msi_step_internal.cache _ ?c2 _ _ ?p2,
        msi_step_internal.cache _ ?c3 _ _ ?p3,
        msi_step_congr (msi_step_internal.cache _ ?c4 _ _ ?p4) ?eq⟩))
      -- x: il grant da s'' (l'`rqS` e le righe sono intatti)
      case px =>
        refine .upgrade_to_M_data_avilable_rq2 _ i₁ j ?_ ?_ ?_
        · exact hj
        · simp only [invSSt]; exact hI
        · exact hnoM
      -- y: l'invalidate da s' (la riga `i₁` è `S` dopo il grant)
      case py =>
        refine .upgrade_to_M_invalid_all2 _ k i₁ j' hk'' hik ?_
        simp only [grantSSt, update_Fin_gss]
      -- da x: la cache prende l'`rsS` in fondo a `pci i₁ ++ [rqIσ, rsS]`
      case p1 =>
        simp only [invSSt, update_Fin_gss]
        refine .upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁ ++ [PCEvent.rqIσ]).length ?_ ?_
        · exact lst_get _ _
        · exact hst
      -- poi cede la linea sull'`rqIσ`
      case p2 =>
        simp only [update_Fin_gss, lst_erase]
        refine .downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get _ _
        · rfl
      -- da y: la cache prende l'`rsS` in mezzo a `pci i₁ ++ [rsS, rqIσ]`
      case p3 =>
        simp only [grantSSt, update_Fin_gss]
        refine .upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get2 _ _ _
        · exact hst
      -- poi cede la linea sull'`rqIσ`
      case p4 =>
        simp only [update_Fin_gss, lst_erase2]
        refine .downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get _ _
        · rfl
      -- i due stati finali coincidono, campo per campo
      case eq =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · rfl
        · intro q; rfl
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
    | S =>
      -- cache in `S`: cede sull'`rqIσ` e poi prende l'`rsS`
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _,
        msi_step_internal.parent_upd_queue _ ?q1S _ _ ?pxS,
        msi_step_internal.parent_upd_queue _ ?q2S _ _ ?pyS,
        msi_step_internal.cache _ ?c1S _ _ ?p1S,
        msi_step_internal.cache _ ?c2S _ _ ?p2S,
        msi_step_internal.cache _ ?c3S _ _ ?p3S,
        msi_step_congr (msi_step_internal.cache _ ?c4S _ _ ?p4S) ?eqS⟩)))
      -- x: il grant da s'' (l'`rqS` e le righe sono intatti)
      case pxS =>
        refine .upgrade_to_M_data_avilable_rq2 _ i₁ j ?_ ?_ ?_
        · exact hj
        · simp only [invSSt]; exact hI
        · exact hnoM
      -- y: l'invalidate da s' (la riga `i₁` è `S` dopo il grant)
      case pyS =>
        refine .upgrade_to_M_invalid_all2 _ k i₁ j' hk'' hik ?_
        simp only [grantSSt, update_Fin_gss]
      -- da x: la cache cede sull'`rqIσ` in mezzo a `pci i₁ ++ [rqIσ, rsS]`
      case p1S =>
        simp only [invSSt, update_Fin_gss]
        refine .downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get2 _ _ _
        · exact hst
      -- poi (in `I`) prende l'`rsS`
      case p2S =>
        simp only [update_Fin_gss, lst_erase2]
        refine .upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get _ _
        · rfl
      -- da y: la cache cede sull'`rqIσ` in fondo a `pci i₁ ++ [rsS, rqIσ]`
      case p3S =>
        simp only [grantSSt, update_Fin_gss]
        refine .downgrade_from_M_rs1 _
          (s.parent.queue_pci i₁ ++ [PCEvent.rsS s.parent.value]).length ?_ ?_
        · exact lst_get _ _
        · exact hst
      -- poi (in `I`) prende l'`rsS`
      case p4S =>
        simp only [update_Fin_gss, lst_erase]
        refine .upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?_ ?_
        · exact lst_get _ _
        · rfl
      -- i due stati finali coincidono, campo per campo
      case eqS =>
        refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · rfl
        · intro q; rfl
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
        · intro q
          by_cases hq : q = i₁
          · subst hq; simp only [grantSSt, invSSt, update_Fin_gss, lst_erase, lst_erase2]
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq]
  · -- indici distinti: il grant da `s'' = invSSt s i₂` porta proprio a `invSSt s' i₂`
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inr (Or.inl ⟨_,
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?hjD ?hID ?hnoMD), ?eqD⟩)
    -- l'`rqS` in `cip i₁` e le righe non cambiano con l'invalidate a `i₂`
    case hjD => simp only [invSSt]; exact hj
    case hID => simp only [invSSt]; exact hI
    case hnoMD => simp only [invSSt]; exact hnoM
    -- i due stati coincidono, campo per campo
    case eqD =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · rfl
      · intro q; rfl
      · intro q; rfl
      · intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [grantSSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantSSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Due invalidate mirati `upgrade_to_M_invalid_all k₁` a `i₁` e `upgrade_to_M_invalid_all k₂` a `i₂`
(il parent accoda un `rqIμ` a `queue_pci`). Con `i₁ = i₂` lo stesso `rqIμ` è accodato due volte e
l'ordine non conta; con `i₁ ≠ i₂` i due passi toccano code diverse. Sempre il diamante, ristabilendo
da ogni lato la stessa regola (`rqM` oppure `rqS` pendente dal richiedente). -/
theorem old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invMSt`
  obtain ⟨⟨j₁, hj₁⟩, hM₁, rfl⟩ := invalidateM_inv h₁
  obtain ⟨⟨j₂, hj₂⟩, hM₂, rfl⟩ := invalidateM_inv h₂
  -- l'invalidate mirato da uno stato qualsiasi, con la stessa regola (`rqM` o `rqS`)
  have stepM : ∀ (t : MSIState n) (k i : Fin n) (j : Nat),
      ((t.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (t.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      t.parent.shared_state i = Bstate.M →
      msi_step_internal t (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) (invMSt t i) := by
    intro t k i j hj hM
    rcases hj with hj | hj
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all _ k i j hj hM)
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i j hj hM)
  -- le guardie (richiesta pendente, riga `M`) non sono toccate dall'altro passo
  refine Or.inl ⟨_, stepM (invMSt s i₂) k₁ i₁ j₁ hj₁ hM₁,
    msi_step_congr (stepM (invMSt s i₁) k₂ i₂ j₂ hj₂ hM₂) ?eq⟩
  case eq =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: lo stesso `rqIμ` accodato due volte, i due lati coincidono
      subst hne; rfl
    · -- indici distinti: i due append lavorano su code diverse
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: i due append su indici diversi commutano
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato `upgrade_to_M_invalid_all k` a `i₁` (riga `i₁ = M`, accoda `rqIμ`) e
`invalid_allS` a `i₂` (riga `i₂ = S`, accoda `rqIσ`). Con `i₁ = i₂` la riga dovrebbe essere
insieme `M` e `S`: coppia vuota; con `i₁ ≠ i₂` i due passi toccano code diverse: diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invMSt` e `invSSt`
  obtain ⟨⟨j₁, hj₁⟩, hM₁, rfl⟩ := invalidateM_inv h₁
  obtain ⟨⟨k', j₂, hj₂⟩, hS₂, rfl⟩ := invalidateS_inv h₂
  -- l'invalidate mirato da uno stato qualsiasi, con la stessa regola (`rqM` o `rqS`)
  have stepM : ∀ (t : MSIState n) (k i : Fin n) (j : Nat),
      ((t.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (t.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      t.parent.shared_state i = Bstate.M →
      msi_step_internal t (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) (invMSt t i) := by
    intro t k i j hj hM
    rcases hj with hj | hj
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all _ k i j hj hM)
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i j hj hM)
  by_cases hne : i₁ = i₂
  · -- stesso indice: la riga non può essere insieme `M` e `S`
    subst hne
    cases hM₁.symm.trans hS₂
  · -- indici distinti: le guardie sopravvivono all'altro passo
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_, stepM (invSSt s i₂) k i₁ j₁ hj₁ hM₁,
      msi_step_congr (msi_step_internal.parent_upd_queue (invMSt s i₁) _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all1 (invMSt s i₁).parent k' i₂ j₂ hj₂ hS₂)) ?eq⟩
    case eq =>
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: `rqIμ` su `i₁` e `rqIσ` su `i₂`, in qualunque ordine
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Invalidate mirato `upgrade_to_M_invalid_all k₁` a `i₁` (riga `i₁ = M`, accoda `rqIμ`) e
`upgrade_to_S_invalid_2_rq1S k₂` a `i₂` (riga `i₂ = S`, accoda `rqIσ`). Con `i₁ = i₂` la riga
dovrebbe essere insieme `M` e `S`: coppia vuota; con `i₁ ≠ i₂` diamante. -/
theorem old_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invMSt` e `invSSt`
  obtain ⟨⟨j₁, hj₁⟩, hM₁, rfl⟩ := invalidateM_inv h₁
  obtain ⟨⟨j₂, hj₂⟩, hk₂, hS₂, rfl⟩ := invalidateS2_inv h₂
  -- l'invalidate mirato da uno stato qualsiasi, con la stessa regola (`rqM` o `rqS`)
  have stepM : ∀ (t : MSIState n) (k i : Fin n) (j : Nat),
      ((t.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (t.parent.queue_cip k)[j]? = some CPEvent.rqS) →
      t.parent.shared_state i = Bstate.M →
      msi_step_internal t (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) (invMSt t i) := by
    intro t k i j hj hM
    rcases hj with hj | hj
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all _ k i j hj hM)
    · exact msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_invalid_all3 _ k i j hj hM)
  by_cases hne : i₁ = i₂
  · -- stesso indice: la riga non può essere insieme `M` e `S`
    subst hne
    cases hM₁.symm.trans hS₂
  · -- indici distinti: le guardie sopravvivono all'altro passo
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine Or.inl ⟨_, stepM (invSSt s i₂) k₁ i₁ j₁ hj₁ hM₁,
      msi_step_congr (msi_step_internal.parent_upd_queue (invMSt s i₁) _ _ i₂
        (parent_msi_step.upgrade_to_M_invalid_all2 (invMSt s i₁).parent k₂ i₂ j₂ hj₂ hk₂ hS₂)) ?eq⟩
    case eq =>
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: `rqIμ` su `i₁` e `rqIσ` su `i₂`, in qualunque ordine
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invMSt, invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invMSt, invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Due `invalid_allS` a `i₁` e a `i₂` (riga `S`, il parent accoda un `rqIσ` a `queue_pci`).
Con `i₁ = i₂` lo stesso `rqIσ` è accodato due volte e l'ordine non conta; con `i₁ ≠ i₂` i due
passi toccano code diverse. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invSSt`
  obtain ⟨⟨k₁, j₁, hj₁⟩, hS₁, rfl⟩ := invalidateS_inv h₁
  obtain ⟨⟨k₂, j₂, hj₂⟩, hS₂, rfl⟩ := invalidateS_inv h₂
  -- le guardie (`rqM` pendente, riga `S`) non sono toccate dall'altro passo
  refine Or.inl ⟨_,
    msi_step_internal.parent_upd_queue (invSSt s i₂) _ _ i₁
      (parent_msi_step.upgrade_to_M_invalid_all1 (invSSt s i₂).parent k₁ i₁ j₁ hj₁ hS₁),
    msi_step_congr (msi_step_internal.parent_upd_queue (invSSt s i₁) _ _ i₂
      (parent_msi_step.upgrade_to_M_invalid_all1 (invSSt s i₁).parent k₂ i₂ j₂ hj₂ hS₂)) ?eq⟩
  case eq =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: lo stesso `rqIσ` accodato due volte, i due lati coincidono
      subst hne; rfl
    · -- indici distinti: i due append lavorano su code diverse
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: i due append su indici diversi commutano
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- `invalid_allS` a `i₁` e `upgrade_to_S_invalid_2_rq1S k` a `i₂` (entrambi con riga `S`,
accodano un `rqIσ` a `queue_pci`). Con `i₁ = i₂` lo stesso `rqIσ` è accodato due volte e
l'ordine non conta; con `i₁ ≠ i₂` i due passi toccano code diverse. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invSSt`
  obtain ⟨⟨k₁, j₁, hj₁⟩, hS₁, rfl⟩ := invalidateS_inv h₁
  obtain ⟨⟨j₂, hj₂⟩, hk₂, hS₂, rfl⟩ := invalidateS2_inv h₂
  -- le guardie (richieste pendenti, righe `S`, `i₂ ≠ k`) non sono toccate dall'altro passo
  refine Or.inl ⟨_,
    msi_step_internal.parent_upd_queue (invSSt s i₂) _ _ i₁
      (parent_msi_step.upgrade_to_M_invalid_all1 (invSSt s i₂).parent k₁ i₁ j₁ hj₁ hS₁),
    msi_step_congr (msi_step_internal.parent_upd_queue (invSSt s i₁) _ _ i₂
      (parent_msi_step.upgrade_to_M_invalid_all2 (invSSt s i₁).parent k i₂ j₂ hj₂ hk₂ hS₂)) ?eq⟩
  case eq =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: lo stesso `rqIσ` accodato due volte, i due lati coincidono
      subst hne; rfl
    · -- indici distinti: i due append lavorano su code diverse
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: i due append su indici diversi commutano
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]


/-- Due `upgrade_to_S_invalid_2_rq1S k₁` a `i₁` e `upgrade_to_S_invalid_2_rq1S k₂` a `i₂`
(riga `S`, richiedente diverso dall'indice, accodano un `rqIσ` a `queue_pci`). Con `i₁ = i₂` lo
stesso `rqIσ` è accodato due volte e l'ordine non conta; con `i₁ ≠ i₂` i due passi toccano code
diverse. Sempre il diamante. -/
theorem old_upgrade_to_M_invalid_all2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- `s'` e `s''` sono i record espliciti `invSSt`
  obtain ⟨⟨j₁, hj₁⟩, hk₁, hS₁, rfl⟩ := invalidateS2_inv h₁
  obtain ⟨⟨j₂, hj₂⟩, hk₂, hS₂, rfl⟩ := invalidateS2_inv h₂
  -- le guardie (`rqS` pendenti, righe `S`, indici diversi dai richiedenti) non sono toccate dall'altro passo
  refine Or.inl ⟨_,
    msi_step_internal.parent_upd_queue (invSSt s i₂) _ _ i₁
      (parent_msi_step.upgrade_to_M_invalid_all2 (invSSt s i₂).parent k₁ i₁ j₁ hj₁ hk₁ hS₁),
    msi_step_congr (msi_step_internal.parent_upd_queue (invSSt s i₁) _ _ i₂
      (parent_msi_step.upgrade_to_M_invalid_all2 (invSSt s i₁).parent k₂ i₂ j₂ hj₂ hk₂ hS₂)) ?eq⟩
  case eq =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: lo stesso `rqIσ` accodato due volte, i due lati coincidono
      subst hne; rfl
    · -- indici distinti: i due append lavorano su code diverse
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) ?_
      · -- le cache: `i₁` e `i₂` riallineate, le altre intatte
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
      · -- `queue_pci`: i due append su indici diversi commutano
        intro q
        by_cases hq₁ : q = i₁
        · subst hq₁
          simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne']
        · by_cases hq₂ : q = i₂
          · subst hq₂
            simp only [invSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne']
          · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]




end MSITrial
