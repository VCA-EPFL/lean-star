import StarExperimental.MSI_trial_bridge

/-!
# `MSI_trial`: i diamanti locali di `MSI.lean` riusati (cache–cache, stessa cache)

Copie testuali dei teoremi `comm_*` di `MSI.lean`: stesse ipotesi (passi di `MSI_def`), stesso
ricongiungimento, stessa dimostrazione. Cambia solo l'uscita: `¬ Reach s` (raggiungibilità di ARS di
`MSI_trial`, passi interni ed esterni) al posto di `¬ MSI.reachable s` (soli passi interni), tramite i
lemmi ponte di `MSI_trial_bridge.lean`. Ogni teorema è `old_<nome>`; il sollevamento ai passi di
`MSI_trial` e alla forma `DecJoin` è in `MSI_trial_peaks_*.lean`.
-/

open THEORY Relation MSIView

namespace MSITrial

/-- Due rilasci spontanei da `M` della stessa cache `i`: entrambi accodano `rsIμ value`
e portano la cache in `I`, quindi i due stati di arrivo coincidono (`s' = s''`). -/
theorem old_rq_data_not_available_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .rq_data_not_available i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM₁ =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | rq_data_not_available hM₂ =>
          -- stesso record di arrivo da entrambe le parti
          exact Or.inr (Or.inl rfl)


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, quello da `S`
richiede `state = S`. -/
theorem old_rq_data_not_available_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | rq_data_not_available1 hS =>
          -- `M = S`: assurdo
          cases hM.symm.trans hS


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, la richiesta di `M`
richiede `state = I`. -/
theorem old_rq_data_not_available_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rq hI =>
          -- `M = I`: assurdo
          cases hM.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, la richiesta di `S`
richiede `state = I`. -/
theorem old_rq_data_not_available_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rq1 hI =>
          -- `M = I`: assurdo
          cases hM.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, la presa del grant
di `M` richiede `state = I`. -/
theorem old_rq_data_not_available_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rs _ j hj hI =>
          -- `M = I`: assurdo
          cases hM.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, la presa del grant
di `S` richiede `state = I`. -/
theorem old_rq_data_not_available_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j hj hI =>
          -- `M = I`: assurdo
          cases hM.symm.trans hI


/-- Entrambe le azioni portano la cache `i` in `I` accodando `rsIμ value`; il rilascio
spontaneo lascia però l'`rqIμ` in `queue_pc` (posizione `j`), mentre l'invalidate lo consuma.
Il modello non ha una regola per scartare lo stantio: `s''` è esattamente `dropSt s' i j`
(quarto disgiunto): le due copie di `queue_pc` coincidono punto per punto (`update_Fin_gss`, `update_Fin_gso2`). -/
theorem old_rq_data_not_available_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
  (∃ j, (s.caches i).queue_pc[j]? = some PCEvent.rqIμ ∧ s'' = dropSt s' i j)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | downgrade_from_M_rs j hj _ =>
          -- l'`rqIμ` stantio sta in posizione `j`: `s''` è `s'` senza quella posizione
          refine Or.inr (Or.inl ⟨j, hj, ?eq⟩)
          case eq =>
            refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) ?hq2
            case hc =>
              intro k
              by_cases hk : k = i
              · -- indice `i`: stesso record, doppio aggiornamento collassato
                subst hk
                simp only [dropSt, update_Fin_gss]
              · -- altri indici: intoccati
                simp only [dropSt, update_Fin_gso2 _ _ _ _ hk]
            case hq2 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [dropSt, update_Fin_gss]
              · simp only [dropSt, update_Fin_gso2 _ _ _ _ hk]


/-- Coppia vuota: il rilascio spontaneo da `M` richiede `state = M`, l'invalidate
ricevuto in `S` richiede `state = S`. -/
theorem old_rq_data_not_available_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | downgrade_from_M_rs1 j hj hS =>
          -- `M = S`: assurdo
          cases hM.symm.trans hS


/-- Due rilasci spontanei da `S` sulla stessa cache `i`: la regola è deterministica
(accoda `rsIσ` e porta la cache a `I`), quindi `s' = s''`. -/
theorem old_rq_data_not_available1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 _ =>
        cases hc₂ with
        | rq_data_not_available1 _ =>
          -- stessa regola, stesso stato di arrivo
          exact Or.inr (Or.inl rfl)


/-- Coppia vuota: il rilascio spontaneo da `S` richiede `state = S`, la richiesta di `M`
richiede `state = I`. -/
theorem old_rq_data_not_available1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 hS =>
        cases hc₂ with
        | upgrade_from_I_rq hI =>
          -- guardie incompatibili: `S` contro `I`
          cases hS.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `S` richiede `state = S`, la richiesta di `S`
richiede `state = I`. -/
theorem old_rq_data_not_available1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 hS =>
        cases hc₂ with
        | upgrade_from_I_rq1 hI =>
          -- guardie incompatibili: `S` contro `I`
          cases hS.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `S` richiede `state = S`, la presa del grant di `M`
richiede `state = I`. -/
theorem old_rq_data_not_available1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 hS =>
        cases hc₂ with
        | upgrade_from_I_rs _ _ _ hI =>
          -- guardie incompatibili: `S` contro `I`
          cases hS.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `S` richiede `state = S`, la presa del grant di `S`
richiede `state = I`. -/
theorem old_rq_data_not_available1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 hS =>
        cases hc₂ with
        | upgrade_from_I_rsS _ _ _ hI =>
          -- guardie incompatibili: `S` contro `I`
          cases hS.symm.trans hI


/-- Coppia vuota: il rilascio spontaneo da `S` richiede `state = S`, l'invalidate ricevuto
in `M` richiede `state = M`. -/
theorem old_rq_data_not_available1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | rq_data_not_available1 hS =>
        cases hc₂ with
        | downgrade_from_M_rs _ _ hM =>
          -- guardie incompatibili: `S` contro `M`
          cases hS.symm.trans hM


/-- Entrambe le azioni portano la cache `i` in `I` accodando `rsIσ`; il rilascio
spontaneo lascia però l'`rqIσ` in `queue_pc` (posizione `j`), mentre l'invalidate lo consuma.
Il modello non ha una regola per scartare lo stantio: `s''` è esattamente `dropSt s' i j`
(quarto disgiunto): le due copie di `queue_pc` coincidono punto per punto (`update_Fin_gss`, `update_Fin_gso2`). -/
theorem old_rq_data_not_available1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
  (∃ j, (s.caches i).queue_pc[j]? = some PCEvent.rqIσ ∧ s'' = dropSt s' i j)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available1 hS =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | downgrade_from_M_rs1 j hj _ =>
          -- l'`rqIσ` stantio sta in posizione `j`: `s''` è `s'` senza quella posizione
          refine Or.inr (Or.inl ⟨j, hj, ?eq⟩)
          case eq =>
            refine MSIState.ext_all ?hc rfl (fun _ => rfl) (fun _ => rfl) ?hq2
            case hc =>
              intro k
              by_cases hk : k = i
              · -- indice `i`: stesso record, doppio aggiornamento collassato
                subst hk
                simp only [dropSt, update_Fin_gss]
              · -- altri indici: intoccati
                simp only [dropSt, update_Fin_gso2 _ _ _ _ hk]
            case hq2 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [dropSt, update_Fin_gss]
              · simp only [dropSt, update_Fin_gso2 _ _ _ _ hk]


/-- Due richieste `rqM` dalla stessa cache `i` in `I`: lo stato resta `I`, quindi da ciascuno
dei due stati di arrivo la cache può accodare un secondo `rqM` e i due cammini si chiudono
sullo stesso stato (rombo, come in `MI`). -/
theorem old_upgrade_from_I_rq_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq hI₁ =>
        cases hc₂ with
        | upgrade_from_I_rq hI₂ =>
          -- rombo: la cache `i` è ancora in `I` dopo il primo `rqM`
          refine Or.inl ⟨_,
            msi_step_internal.cache _ _ _ _ (cache_msi_step_internal.upgrade_from_I_rq _ ?g₁),
            msi_step_internal.cache _ _ _ _ (cache_msi_step_internal.upgrade_from_I_rq _ ?g₂)⟩
          case g₁ => simp only [update_Fin_gss]; exact hI₂
          case g₂ => simp only [update_Fin_gss]; exact hI₁


/-- Richiesta di `M` e richiesta di `S` dalla stessa cache `i` in `I`: lo stato resta `I`, quindi
entrambe le richieste restano abilitate dopo l'altra. Le due code però differiscono per l'ordine
degli `rq` accodati: `t₂` è `t₁` con `queue_cp` (e la copia del parent) uguale a
`cp ++ [rqS, rqM]` (quarto disgiunto, `List.append_assoc`). -/
theorem old_upgrade_from_I_rq_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
  (∃ t₁ t₂,
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) t₁ ∧
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) t₂ ∧
    t₂ = { t₁ with
             caches := update_Fin i { t₁.caches i with
                         queue_cp := (s.caches i).queue_cp ++ [CPEvent.rqS, CPEvent.rqM] } t₁.caches,
             parent.queue_cip := update_Fin i ((s.caches i).queue_cp ++ [CPEvent.rqS, CPEvent.rqM])
                                   t₁.parent.queue_cip })
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq hI =>
        cases hc₂ with
        | upgrade_from_I_rq1 hI' =>
          -- le due richieste si accodano nei due ordini: `t₂` è `t₁` con la coda riordinata
          refine Or.inr (Or.inl ⟨_, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.cache _ ?c2 _ _ ?p2, ?eq⟩)
          -- da `s'` (con `rqM` in coda) la richiesta di `S`: lo stato è ancora `I`
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq1 _ ?_
            exact hI
          -- da `s''` (con `rqS` in coda) la richiesta di `M`: lo stato è ancora `I`
          case p2 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            exact hI'
          case eq =>
            refine MSIState.ext_all ?hc rfl (fun _ => rfl) ?hq1 ?hq2
            case hc =>
              intro k
              by_cases hk : k = i
              · -- indice `i`: `(cp ++ [rqS]) ++ [rqM] = cp ++ [rqS, rqM]`
                subst hk
                simp only [update_Fin_gss, List.append_assoc, List.singleton_append]
              · -- altri indici: intoccati
                simp only [update_Fin_gso2 _ _ _ _ hk]
            case hq1 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, List.append_assoc, List.singleton_append]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            case hq2 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]


/-- **Richiesta `rqM` / presa del grant `rsM v` dalla stessa cache.** Il secondo `rqM` (spedito con
un grant già in volo) è una richiesta doppia: da `s'` la cache prende il grant pendente (stessa
posizione `j`), rilascia (`rsIμ v`), il parent registra il rilascio e concede il duplicato, la cache
riprende la linea: le cache sono come dopo la presa diretta. La concessione vuole la directory tutta
a `I`: le altre righe lo sono, oppure `s` ha una vista cattiva (`rsM` in volo per `i` con una riga
`k ≠ i` non a `I`). -/
theorem old_upgrade_from_I_rq_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅,
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) t₁ ∧
    msi_step_internal t₁ (.cache .rq_data_not_available i) t₂ ∧
    msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t₄ ∧
    msi_step_internal t₄ (.cache (.upgrade_from_I_rs v) i) t₅ ∧
    s''.caches = t₅.caches)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | upgrade_from_I_rq hI =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rs _ j hj hI' =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · -- tutte le altre righe della directory sono a `I`: il cammino esplicito da `s'`
            refine Or.inl ⟨_, _, _, _, _,
              msi_step_internal.cache _ ?c1 _ _ ?p1,
              msi_step_internal.cache _ ?c2 _ _ ?p2,
              msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
              msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
              msi_step_internal.cache _ ?c3 _ _ ?p5,
              ?eq⟩
            -- 1. la cache prende il grant pendente (posizione `j`, coda `pc` intatta)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ j ?_ ?_
              · exact hj
              · exact hI
            -- 2. rilascio spontaneo: `rsIμ v` in coda dopo il duplicato `rqM`
            case p2 =>
              simp only [update_Fin_gss]
              refine .rq_data_not_available _ ?_
              rfl
            -- 3. il parent consuma l'`rsIμ v` (posizione `(cp ++ [rqM]).length`): riga `i := I`, `value := v`
            case p3 =>
              refine .downgrade_from_M_rq1 _ _ _ ((s.caches i).queue_cp ++ [CPEvent.rqM]).length ?_
              simp only [update_Fin_gss]
              exact lst_get _ _
            -- 4. il parent concede il duplicato `rqM` (posizione `cp.length`): `rsM v` in coda
            case p4 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 5. la cache riprende la linea (posizione `(pc.eraseIdx j).length`)
            case p5 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- le cache coincidono: `⟨M, v, cp, pc.eraseIdx j, ext⟩` da entrambi i lati
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- una riga `k ≠ i` non è a `I` mentre un `rsM` è in volo per `i`: vista cattiva
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkI⟩ := Classical.not_imp.mp hk
            have hj' : (s.parent.queue_pci i)[j]? = some (PCEvent.rsM v) := by
              rw [(hsync i).2]; exact hj
            exact Or.inr (Or.inr (not_reach_of_mu_rowJ (Ne.symm hki) (muMsgs_ne_zero_of_rsM hj') hkI))


/-- Richiesta di `M` e presa del grant di `S` dalla stessa cache `i` in `I`: dopo la presa la
cache è in `S`, quindi la richiesta non è più abilitata; da `s'` invece la presa (stessa posizione
`j`, stato ancora `I`) porta esattamente a `reqMSt s'' i` (quarto disgiunto, per estensionalità). -/
theorem old_upgrade_from_I_rq_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) s''')
  ∨
  (∃ t₁, msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) t₁ ∧ t₁ = reqMSt s'' i)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq hI =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j hj hI' =>
          -- da `s'` la presa del grant di `S` in posizione `j`: si arriva a `reqMSt s'' i`
          refine Or.inr (Or.inl ⟨_, msi_step_internal.cache _ ?c1 _ _ ?p1, ?eq⟩)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rsS _ _ j ?_ ?_
            · exact hj
            · exact hI
          case eq =>
            refine MSIState.ext_all ?hc rfl (fun _ => rfl) ?hq1 ?hq2
            case hc =>
              intro k
              by_cases hk : k = i
              · -- indice `i`: `⟨S, v, cp ++ [rqM], pc.eraseIdx j, ext⟩` da entrambi i lati
                subst hk
                simp only [reqMSt, update_Fin_gss]
              · -- altri indici: intoccati
                simp only [reqMSt, update_Fin_gso2 _ _ _ _ hk]
            case hq1 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [reqMSt, update_Fin_gss]
              · simp only [reqMSt, update_Fin_gso2 _ _ _ _ hk]
            case hq2 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [reqMSt, update_Fin_gss]
              · simp only [reqMSt, update_Fin_gso2 _ _ _ _ hk]


/-- Coppia vuota: la richiesta `rqM` vuole la cache `i` in `I`, l'invalidate ricevuto in `M`
(`downgrade_from_M_rs`) la vuole in `M`. -/
theorem old_upgrade_from_I_rq_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq hI =>
        cases hc₂ with
        | downgrade_from_M_rs j hj hM =>
          -- guardie incompatibili: `I` contro `M`
          cases hI.symm.trans hM


/-- Coppia vuota: la richiesta `rqM` vuole la cache `i` in `I`, l'invalidate ricevuto in `S`
(`downgrade_from_M_rs1`) la vuole in `S`. -/
theorem old_upgrade_from_I_rq_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq hI =>
        cases hc₂ with
        | downgrade_from_M_rs1 j hj hS =>
          -- guardie incompatibili: `I` contro `S`
          cases hI.symm.trans hS


/-- Due richieste `rqS` dalla stessa cache `i` in `I`: lo stato resta `I`, quindi da ciascuno
dei due stati di arrivo la cache può accodare un secondo `rqS` e i due cammini si chiudono
sullo stesso stato (rombo). -/
theorem old_upgrade_from_I_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq1 hI₁ =>
        cases hc₂ with
        | upgrade_from_I_rq1 hI₂ =>
          -- rombo: la cache `i` è ancora in `I` dopo il primo `rqS`
          refine Or.inl ⟨_,
            msi_step_internal.cache _ _ _ _ (cache_msi_step_internal.upgrade_from_I_rq1 _ ?g₁),
            msi_step_internal.cache _ _ _ _ (cache_msi_step_internal.upgrade_from_I_rq1 _ ?g₂)⟩
          case g₁ => simp only [update_Fin_gss]; exact hI₂
          case g₂ => simp only [update_Fin_gss]; exact hI₁


/-- Richiesta di `S` e presa del grant di `M` dalla stessa cache `i` in `I`: dopo la presa la
cache è in `M`, quindi la richiesta non è più abilitata; da `s'` invece la presa (stessa posizione
`j`, stato ancora `I`) porta esattamente a `reqSSt s'' i` (quarto disgiunto, per estensionalità). -/
theorem old_upgrade_from_I_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) s''')
  ∨
  (∃ t₁, msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) t₁ ∧ t₁ = reqSSt s'' i)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq1 hI =>
        cases hc₂ with
        | upgrade_from_I_rs _ j hj hI' =>
          -- da `s'` la presa del grant di `M` in posizione `j`: si arriva a `reqSSt s'' i`
          refine Or.inr (Or.inl ⟨_, msi_step_internal.cache _ ?c1 _ _ ?p1, ?eq⟩)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ j ?_ ?_
            · exact hj
            · exact hI
          case eq =>
            refine MSIState.ext_all ?hc rfl (fun _ => rfl) ?hq1 ?hq2
            case hc =>
              intro k
              by_cases hk : k = i
              · -- indice `i`: `⟨M, v, cp ++ [rqS], pc.eraseIdx j, ext⟩` da entrambi i lati
                subst hk
                simp only [reqSSt, update_Fin_gss]
              · -- altri indici: intoccati
                simp only [reqSSt, update_Fin_gso2 _ _ _ _ hk]
            case hq1 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [reqSSt, update_Fin_gss]
              · simp only [reqSSt, update_Fin_gso2 _ _ _ _ hk]
            case hq2 =>
              intro k
              by_cases hk : k = i
              · subst hk
                simp only [reqSSt, update_Fin_gss]
              · simp only [reqSSt, update_Fin_gso2 _ _ _ _ hk]


/-- **Richiesta `rqS` / presa del grant `rsS v` dalla stessa cache.** Il secondo `rqS` è una
richiesta doppia: da `s'` la cache prende il grant pendente (posizione `j`), rilascia (`rsIσ`), il
parent registra il rilascio e concede il duplicato con il proprio valore, la cache riprende la linea:
le cache sono come dopo la presa diretta se `v = s.parent.value` (altrimenti vale il secondo
disgiunto). La concessione vuole nessuna riga a `M`: le altre righe non lo sono, oppure `s` ha una
vista cattiva (`rsS` in volo per `i` con una riga `k ≠ i` a `M`). -/
theorem old_upgrade_from_I_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅,
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) t₁ ∧
    msi_step_internal t₁ (.cache .ld_rq_data_not_availableS i) t₂ ∧
    msi_step_internal t₂ (.parent (.upd_queue .downgrade_from_S_rq1S i)) t₃ ∧
    msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) t₄ ∧
    msi_step_internal t₄ (.cache (.upgrade_from_I_rsS v) i) t₅ ∧
    s''.caches = t₅.caches)
  ∨
    ¬(v = s.parent.value)
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (Or.inr (not_reach_of_not_synced hsync)))
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | upgrade_from_I_rq1 hI =>
      cases h₂ with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j hj hI' =>
          -- il grant porta un valore diverso da quello del parent: secondo disgiunto
          by_cases hv : v = s.parent.value
          swap
          · exact Or.inr (Or.inl hv)
          by_cases hall : ∀ k, k ≠ i → ¬ s.parent.shared_state k = Bstate.M
          · -- nessun'altra riga a `M`: il cammino esplicito da `s'`
            refine Or.inl ⟨_, _, _, _, _,
              msi_step_internal.cache _ ?c1 _ _ ?p1,
              msi_step_internal.cache _ ?c2 _ _ ?p2,
              msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
              msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
              msi_step_internal.cache _ ?c3 _ _ ?p5,
              ?eq⟩
            -- 1. la cache prende il grant pendente (posizione `j`, coda `pc` intatta)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rsS _ _ j ?_ ?_
              · exact hj
              · exact hI
            -- 2. rilascio spontaneo da `S`: `rsIσ` in coda dopo il duplicato `rqS`
            case p2 =>
              simp only [update_Fin_gss]
              refine .rq_data_not_available1 _ ?_
              rfl
            -- 3. il parent consuma l'`rsIσ` (posizione `(cp ++ [rqS]).length`): riga `i := I`
            case p3 =>
              refine .downgrade_from_M_rq2 _ _ ((s.caches i).queue_cp ++ [CPEvent.rqS]).length ?_
              simp only [update_Fin_gss]
              exact lst_get _ _
            -- 4. il parent concede il duplicato `rqS` (posizione `cp.length`): `rsS s.parent.value` in coda
            case p4 =>
              refine .upgrade_to_M_data_avilable_rq2 _ _ (s.caches i).queue_cp.length ?_ ?_ ?_
              · simp only [update_Fin_gss, lst_erase]
                exact lst_get _ _
              · -- il downgrade al passo 3 ha appena posto la riga `i` a `I`: nuovo guard
                simp only [update_Fin_gss]
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                  exact fun h => Bstate.noConfusion h
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 5. la cache riprende la linea in `S` con `v = s.parent.value` (posizione `(pc.eraseIdx j).length`)
            case p5 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rsS _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · rw [hv]
                exact lst_get _ _
              · rfl
            -- le cache coincidono: `⟨S, v, cp, pc.eraseIdx j, ext⟩` da entrambi i lati
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- una riga `k ≠ i` è a `M` mentre un `rsS` è in volo per `i`: vista cattiva
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hj' : (s.parent.queue_pci i)[j]? = some (PCEvent.rsS v) := by
              rw [(hsync i).2]; exact hj
            exact Or.inr (Or.inr (Or.inr
              (not_reach_of_sig_rowM (Ne.symm hki) (sigMsgs_ne_zero_of_rsS hj') (Classical.not_not.mp hkM))))


/-- Coppia vuota: la richiesta `rqS` vuole la cache `i` in `I`, l'invalidate ricevuto in `M`
(`downgrade_from_M_rs`) la vuole in `M`. -/
theorem old_upgrade_from_I_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq1 hI =>
        cases hc₂ with
        | downgrade_from_M_rs j hj hM =>
          -- guardie incompatibili: `I` contro `M`
          cases hI.symm.trans hM


/-- Coppia vuota: la richiesta `rqS` vuole la cache `i` in `I`, l'invalidate ricevuto in `S`
(`downgrade_from_M_rs1`) la vuole in `S`. -/
theorem old_upgrade_from_I_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rq1 hI =>
        cases hc₂ with
        | downgrade_from_M_rs1 j hj hS =>
          -- guardie incompatibili: `I` contro `S`
          cases hI.symm.trans hS


/-- Due prese del grant `rsM` sulla stessa cache `i`. Stessa posizione `j₁ = j₂`: stesso messaggio,
`v₁ = v₂` e `s' = s''`. Posizioni diverse: due `rsM` in volo per `i` sul lato parent (via `synced`),
cioè `2 ≤ muMsgs`, vista cattiva `not_reach_of_two_mu`. -/
theorem old_upgrade_from_I_rs_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | upgrade_from_I_rs _ j₂ hj₂ hI₂ =>
          by_cases hj : j₁ = j₂
          · -- stessa posizione: stesso `rsM`, quindi `v₁ = v₂` e i due stati coincidono
            subst hj
            rw [hj₁] at hj₂
            cases hj₂
            exact Or.inr (Or.inl rfl)
          · -- posizioni diverse: due `rsM` in volo per `i` (contati sul lato parent)
            have hpc := (hsync i).2
            rw [← hpc] at hj₁ hj₂
            have h2 := two_le_countP_of_ne isGrantM _ hj₁ hj₂ hj rfl rfl
            have hmu : 2 ≤ muMsgs s.parent i := by unfold muMsgs; omega
            exact Or.inr (Or.inr (not_reach_of_two_mu hmu))


/-- Presa del grant `rsM` e presa del grant `rsS` sulla stessa cache `i`: un token `M` e un token `S`
in volo per `i` sul lato parent (via `synced`), vista cattiva `not_reach_of_mu_sig`. -/
theorem old_upgrade_from_I_rs_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j₂ hj₂ hI₂ =>
          -- `rsM` e `rsS` in volo per `i`: portati sul lato parent con `synced`
          have hpc := (hsync i).2
          rw [← hpc] at hj₁ hj₂
          exact Or.inr (Or.inr (not_reach_of_mu_sig (muMsgs_ne_zero_of_rsM hj₁) (sigMsgs_ne_zero_of_rsS hj₂)))


/-- Presa del grant `rsM` (cache in `I`) e `downgrade_from_M_rs` (cache in `M`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem old_upgrade_from_I_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | downgrade_from_M_rs j₂ hj₂ hM₂ =>
          -- la cache `i` non può essere insieme in `I` e in `M`
          rw [hI₁] at hM₂
          cases hM₂


/-- Presa del grant `rsM` (cache in `I`) e `downgrade_from_S_rsS` (cache in `S`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem old_upgrade_from_I_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | downgrade_from_M_rs1 j₂ hj₂ hS₂ =>
          -- la cache `i` non può essere insieme in `I` e in `S`
          rw [hI₁] at hS₂
          cases hS₂


/-- Due prese del grant `rsS` sulla stessa cache `i`. Stessa posizione `j₁ = j₂`: stesso messaggio,
`v₁ = v₂` e `s' = s''`. Posizioni diverse: due `rsS` in volo per `i` sul lato parent (via `synced`),
cioè `2 ≤ sigMsgs`, vista cattiva `not_reach_of_two_sig`. -/
theorem old_upgrade_from_I_rsS_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hsync))
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rsS _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j₂ hj₂ hI₂ =>
          by_cases hj : j₁ = j₂
          · -- stessa posizione: stesso `rsS`, quindi `v₁ = v₂` e i due stati coincidono
            subst hj
            rw [hj₁] at hj₂
            cases hj₂
            exact Or.inr (Or.inl rfl)
          · -- posizioni diverse: due `rsS` in volo per `i` (contati sul lato parent)
            have hpc := (hsync i).2
            rw [← hpc] at hj₁ hj₂
            have h2 := two_le_countP_of_ne isGrantS _ hj₁ hj₂ hj rfl rfl
            have hsig : 2 ≤ sigMsgs s.parent i := by unfold sigMsgs; omega
            exact Or.inr (Or.inr (not_reach_of_two_sig hsig))


/-- Presa del grant `rsS` (cache in `I`) e `downgrade_from_M_rs` (cache in `M`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem old_upgrade_from_I_rsS_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rsS _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | downgrade_from_M_rs j₂ hj₂ hM₂ =>
          -- la cache `i` non può essere insieme in `I` e in `M`
          rw [hI₁] at hM₂
          cases hM₂


/-- Presa del grant `rsS` (cache in `I`) e `downgrade_from_S_rsS` (cache in `S`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem old_upgrade_from_I_rsS_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rsS _ j₁ hj₁ hI₁ =>
        cases hc₂ with
        | downgrade_from_M_rs1 j₂ hj₂ hS₂ =>
          -- la cache `i` non può essere insieme in `I` e in `S`
          rw [hI₁] at hS₂
          cases hS₂


/-- Due `downgrade_from_M_rs` sulla stessa cache `i` (in `M`, con due `rqIμ` in `queue_pc`).
Stessa posizione `j₁ = j₂`: stesso messaggio consumato, `s' = s''`. Posizioni diverse: la cache
è ormai in `I` e l'altro invalidate è stantio; le due doppie cancellazioni coincidono (`key`) e
si esprimono con `dropSt` in `min j₁ j₂` da un lato e in `max j₁ j₂ - 1` dall'altro. -/
theorem old_downgrade_from_M_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .downgrade_from_M_rs i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .downgrade_from_M_rs i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
  (∃ t,
    (∃ j, (s'.caches i).queue_pc[j]? = some PCEvent.rqIμ ∧ dropSt s' i j = t) ∧
    (∃ j, (s''.caches i).queue_pc[j]? = some PCEvent.rqIμ ∧ dropSt s'' i j = t))
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List PCEvent) (a b : Nat), a < b →
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
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | downgrade_from_M_rs j₁ hj₁ hM =>
        cases hc₂ with
        | downgrade_from_M_rs j₂ hj₂ _ =>
          by_cases hj : j₁ = j₂
          · -- stessa posizione: stesso messaggio consumato, stesso stato
            subst hj; exact Or.inr (Or.inr (Or.inl rfl))
          · refine Or.inr (Or.inl ?_)
            rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
            · -- j₁ < j₂: lo stantio scala in j₂ - 1 dopo aver tolto j₁, resta in j₁ dopo aver tolto j₂
              refine ⟨_, ⟨j₂ - 1, ?p1, rfl⟩, ⟨j₁, ?p2, ?eq⟩⟩
              case p1 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
              case p2 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
              case eq =>
                simp only [dropSt, update_Fin_gss, update_Fin_update_Fin_same]
                rw [key _ _ _ hlt]
            · -- j₂ < j₁: simmetrico, lo stantio è quello in j₁
              refine ⟨_, ⟨j₂, ?p1, rfl⟩, ⟨j₁ - 1, ?p2, ?eq⟩⟩
              case p1 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
              case p2 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
              case eq =>
                simp only [dropSt, update_Fin_gss, update_Fin_update_Fin_same]
                rw [key _ _ _ hgt]


/-- Coppia vuota: `downgrade_from_M_rs` richiede la cache `i` in `M`, `downgrade_from_S_rsS`
la richiede in `S`; le due guardie si contraddicono. -/
theorem old_downgrade_from_M_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .downgrade_from_M_rs i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .downgrade_from_M_rs i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | downgrade_from_M_rs j₁ hj₁ hM =>
        cases hc₂ with
        | downgrade_from_M_rs1 j₂ hj₂ hS =>
          -- guardie contraddittorie: la cache non può essere in `M` e in `S`
          cases hM.symm.trans hS


/-- Due `downgrade_from_S_rsS` sulla stessa cache `i` (in `S`, con due `rqIσ` in `queue_pc`).
Stessa posizione: `s' = s''`. Posizioni diverse: la cache è ormai in `I` e l'altro invalidate è
stantio; le due doppie cancellazioni coincidono (`key`) e si esprimono con `dropSt`. -/
theorem old_downgrade_from_M_rs1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .downgrade_from_S_rsS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
  (∃ t,
    (∃ j, (s'.caches i).queue_pc[j]? = some PCEvent.rqIσ ∧ dropSt s' i j = t) ∧
    (∃ j, (s''.caches i).queue_pc[j]? = some PCEvent.rqIσ ∧ dropSt s'' i j = t))
  ∨
    s' = s''
  ∨
    ¬ Reach s := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List PCEvent) (a b : Nat), a < b →
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
  cases h₁ with
  | cache c _ _ hc₁ =>
    cases h₂ with
    | cache c' _ _ hc₂ =>
      cases hc₁ with
      | downgrade_from_M_rs1 j₁ hj₁ hS =>
        cases hc₂ with
        | downgrade_from_M_rs1 j₂ hj₂ _ =>
          by_cases hj : j₁ = j₂
          · -- stessa posizione: stesso messaggio consumato, stesso stato
            subst hj; exact Or.inr (Or.inr (Or.inl rfl))
          · refine Or.inr (Or.inl ?_)
            rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
            · -- j₁ < j₂: lo stantio scala in j₂ - 1 dopo aver tolto j₁, resta in j₁ dopo aver tolto j₂
              refine ⟨_, ⟨j₂ - 1, ?p1, rfl⟩, ⟨j₁, ?p2, ?eq⟩⟩
              case p1 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
              case p2 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
              case eq =>
                simp only [dropSt, update_Fin_gss, update_Fin_update_Fin_same]
                rw [key _ _ _ hlt]
            · -- j₂ < j₁: simmetrico, lo stantio è quello in j₁
              refine ⟨_, ⟨j₂, ?p1, rfl⟩, ⟨j₁ - 1, ?p2, ?eq⟩⟩
              case p1 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
              case p2 =>
                simp only [update_Fin_gss]
                rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
              case eq =>
                simp only [dropSt, update_Fin_gss, update_Fin_update_Fin_same]
                rw [key _ _ _ hgt]




end MSITrial
