import StarExperimental.MSI

/-! # `MSI_no_escape`: i teoremi di commutazione che convergono anche nel caso a vista cattiva

Dei 185 teoremi `comm_*` di `MSI.lean`, 41 chiudono almeno un caso con una vista cattiva
(un lemma `not_reachable_of_*`, cioè la via d'uscita `¬ MSI.reachable s`). Qui si ripete
l'analisi caso per caso chiedendo: nello stato "sbagliato" i due passi convergono comunque?

Risultato (2026-09-30, agenti prover + verificatore indipendente):
* **2 teoremi** (grant `S` contro invalidate `S`): il caso a vista cattiva è vuoto, le guardie
  delle due regole si contraddicono con `i₁ = i₂`. Diamante puro, stesso enunciato senza
  `∨ ¬ MSI.reachable s` e senza ipotesi aggiunte (`..._noesc`).
* **21 teoremi parent–cache**: nel caso a vista cattiva i due passi sono indipendenti (il parent
  legge solo la propria coda, la cache solo il proprio stato e la propria coda) e il diamante a
  un passo vale. Serve solo `synced s`, le due copie di ogni coda allineate: senza, il modello a
  liste rompe qualsiasi diamante, ma è un artefatto delle due copie e non del protocollo
  (`synced` vale in `default` ed è preservato da ogni passo, `synced_step`). Enunciato: originale
  meno `∨ ¬ MSI.reachable s`, più l'ipotesi `(hsync : synced s)` (`..._noesc_synced`).
* **18 teoremi** non convergono nel caso a vista cattiva e restano come sono in `MSI.lean`:
  4 downgrade/grant (la riga finisce diversa a seconda dell'ordine), 3 grant/grant (la cache del
  richiedente non è in `I` e non può prendere il grant), 5 cache/cache (dopo la prima presa la
  cache non è più in `I`), 6 esterni (dopo il rilascio la cache è in `I` e non serve la load/store;
  la riacquisizione vuole tutte le righe a `I`).

Nessuna dimostrazione qui usa `MSI.reachable`, `badView`, `badView_unreachable`,
`not_reachable_of_*` o `synced_of_reachable`. Gli originali di `MSI.lean` seguono da questi
con `by_cases synced s` e `not_reachable_of_not_synced`. -/

open THEORY
open Relation
open BackwardGen
open MSIView

/-! ## Cache `i` / cache `j` con `i ≠ j`: diamante puro

`MSI.lean` ha i 36 teoremi cache–cache sulla *stessa* cache. Il caso di due cache diverse
mancava: è un solo lemma, per ogni coppia di regole interne, senza ipotesi. Un passo della
cache `i` legge solo `caches i` e scrive solo `caches i`, `parent.queue_cip i` e
`parent.queue_pci i`; con `i ≠ j` i due passi toccano componenti disgiunte dello stato. -/

/-- **Due passi interni di cache su indici diversi**: diamante a un passo, per ogni coppia di
regole `r₁`, `r₂`. Nessuna ipotesi: né `synced`, né raggiungibilità. -/
theorem comm_cache_cache_ne {n} {s s' s'' : MSIState n} {r₁ r₂ : CacheInternalEvent}
    {i₁ i₂ : Fin n} (hii : ¬ i₁ = i₂)
    (h₁ : msi_step_internal s (.cache r₁ i₁) s') (h₂ : msi_step_internal s (.cache r₂ i₂) s'') :
    ∃ s''', msi_step_internal s'' (.cache r₁ i₁) s''' ∧ msi_step_internal s' (.cache r₂ i₂) s''' := by
  cases h₁
  rename_i c₁ hc₁
  cases h₂
  rename_i c₂ hc₂
  refine ⟨_, msi_step_internal.cache _ c₁ i₁ r₁ (by simp only [update_Fin_gso2 _ _ _ _ hii]; exact hc₁), ?_⟩
  refine msi_step_congr (msi_step_internal.cache _ c₂ i₂ r₂
    (by simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hii)]; exact hc₂)) ?_
  refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · rfl
  · intro k; rfl
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]

#print axioms comm_cache_cache_ne

/-! ## Diamanti puri: il caso a vista cattiva è vuoto -/

/-- Versione senza via d'uscita di `comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1`.
Il grant di `S` a `i₁` richiede la riga `i₁ = I`, l'`invalid_allS` a `i₂` richiede la riga `i₂ = S`:
con `i₁ = i₂` le guardie sono contraddittorie, quindi il caso "stesso indice" (compreso quello in cui
la cache era a `M`, chiuso in origine con `not_reachable_of_M`) è vuoto. Con `i₁ ≠ i₂` diamante.
L'ipotesi `synced s` del proof originale non serviva. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1_noesc {s s' s'' : MSIState n} :
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
    s' = s'' := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
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
  · -- stesso indice: la riga `i₁` sarebbe a `I` (grant) e a `S` (invalidate) insieme
    subst hne
    rw [hI] at hS
    cases hS
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

#print axioms comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1_noesc

/-- Versione senza via d'uscita di `comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2`.
Il grant di `S` a `i₁` richiede la riga `i₁ = I`, l'`upgrade_to_S_invalid_2_rq1S k` a `i₂` richiede la
riga `i₂ = S`: con `i₁ = i₂` le guardie sono contraddittorie, quindi il caso "stesso indice" (compreso
quello in cui la cache era a `M`, chiuso in origine con `not_reachable_of_M`) è vuoto. Con `i₁ ≠ i₂`
il grant da `s'' = invSSt s i₂` porta proprio a `invSSt s' i₂`. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2_noesc {s s' s'' : MSIState n} :
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
    s' = s'' := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  obtain ⟨⟨j', hk⟩, hik, hS, rfl⟩ := invalidateS2_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: la riga `i₁` sarebbe a `I` (grant) e a `S` (invalidate) insieme
    subst hne
    rw [hI] at hS
    cases hS
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

#print axioms comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2_noesc

/-! ## Parent–cache: diamante con `synced s` -/

/-! `comm_downgrade_from_M_rq1_rq_data_not_available` senza la via d'uscita `¬ MSI.reachable s`.

L'enunciato esatto "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con le due copie
della coda `i₁` disallineate (la cache non vede l'`rsIμ v` che il parent consuma), quindi qui si
tiene l'ipotesi `synced s`. Nel caso a vista cattiva (`i₁ = i₂`, cache in `M` con il proprio
`rsIμ` già in volo) i due passi convergono in un solo passo: il parent toglie la posizione `j`
di `queue_cip i₁`, la cache accoda `rsIμ` in fondo alla stessa coda e passa a `I`; i due ordini
danno lo stesso stato. Nessun disgiunto è cambiato o aggiunto. -/
theorem comm_downgrade_from_M_rq1_rq_data_not_available_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?gc)) ?eq⟩
        -- l'`rsIμ v` in posizione `j` sopravvive all'`rsIμ` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `M` dopo il downgrade
        case gc => simp only [downgradeMSt, update_Fin_gss]; exact hM
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
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
            .rq_data_not_available
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value],
                               state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available _ hM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_rq_data_not_available_noesc_synced

/-! `comm_downgrade_from_M_rq1_rq_data_not_available1` senza la via d'uscita `¬ MSI.reachable s`.

L'enunciato esatto "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con le due copie
della coda `i₁` disallineate (la cache non vede l'`rsIμ v` che il parent consuma), quindi qui si
tiene l'ipotesi `synced s`. Nel caso a vista cattiva (`i₁ = i₂`, cache in `S` con un proprio
`rsIμ` da `M` ancora in volo) i due passi convergono in un solo passo: il parent toglie la posizione `j`
di `queue_cip i₁`, la cache accoda `rsIσ` in fondo alla stessa coda e passa a `I`; i due ordini
danno lo stesso stato. Nessun disgiunto è cambiato o aggiunto. -/
theorem comm_downgrade_from_M_rq1_rq_data_not_available1_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeMSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?gc)) ?eq⟩
        -- l'`rsIμ v` in posizione `j` sopravvive all'`rsIσ` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `S` dopo il downgrade
        case gc => simp only [downgradeMSt, update_Fin_gss]; exact hS
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
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
            .ld_rq_data_not_availableS
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIσ],
                               state := Bstate.I } := by
          rw [hci]; exact cache_msi_step_internal.rq_data_not_available1 _ hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_rq_data_not_available1_noesc_synced

/-! `comm_downgrade_from_M_rq1_upgrade_from_I_rs` senza la via d'uscita `¬ MSI.reachable s`.

L'enunciato esatto "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con le due copie
delle code di `i₁` disallineate (dopo il passo di cache il parent vede la copia della cache di
`queue_cip i₁`, dove l'`rsIμ v₁` può mancare), quindi qui si tiene l'ipotesi `synced s`. Nel caso a
vista cattiva (`i₁ = i₂`, `rsM v₂` in `queue_pci` e `rsIμ v₁` in `queue_cip`: due token `M` in volo)
i due passi convergono in un solo passo: il parent toglie la posizione `j` di `queue_cip i₁`, la
cache toglie la posizione `j'` di `queue_pc i₁` e passa a `M`; toccano code diverse dello stesso
indice e i due ordini danno lo stesso stato. Nessun disgiunto è cambiato o aggiunto. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rs_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeMSt s v₁ i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma `j` in `queue_cip`, la cache consuma `j'` in `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v₂ j' ?gc ?gI)) ?eq⟩
        -- l'`rsIμ v₁` in posizione `j` di `queue_cip i₁` non è toccato dalla cache (copia via `hsync`)
        case gp =>
          simp only [update_Fin_gss, ← hs1]; exact hj
        -- l'`rsM v₂` in posizione `j'` di `queue_pc i₁` non è toccato dal downgrade (copia via `hsync`)
        case gc => simp only [downgradeMSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gI => simp only [downgradeMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1, ← hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, ← hs1]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeMSt, update_Fin_gss, ← hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeMSt s v₁ i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_upgrade_from_I_rs_noesc_synced

/-- Same-index case: the two steps are independent (the parent downgrade does not look at the
cache state, the cache grant does not look at the parent row), so the diamond holds whenever the
two copies of the queues of `i₁` agree. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rsS_noesc_synced {s s' s'' : MSIState n} :
  synced s →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i₂) s''')
  ∨
    s' = s'' := by
  intro hsync h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: diamante comunque
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hci : (downgradeMSt s v₁ i₁ j).caches i₁ =
            { s.caches i₁ with queue_cp := (s.parent.queue_cip i₁).eraseIdx j,
                               queue_pc := s.parent.queue_pci i₁ } := by
          simp only [downgradeMSt, update_Fin_gss]
        have hstep : cache_msi_step_internal ((downgradeMSt s v₁ i₁ j).caches i₁)
            (.upgrade_from_I_rsS v₂)
            { s.caches i₁ with
                state := Bstate.S,
                value := v₂,
                queue_cp := (s.parent.queue_cip i₁).eraseIdx j,
                queue_pc := (s.parent.queue_pci i₁).eraseIdx j' } := by
          rw [hci]
          exact cache_msi_step_internal.upgrade_from_I_rsS _ v₂ j' (by rw [hs2]; exact hj') hI
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v₁ i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        case g => simp only [update_Fin_gss]; rw [← hs1]; exact hj
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1, hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeMSt s v₁ i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_upgrade_from_I_rsS_noesc_synced

/-- Same-index case: the two steps are independent (the parent downgrade does not look at the
cache state, the cache release does not look at the parent row), so the diamond holds whenever
the two copies of the queues of `i₁` agree. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs_noesc_synced {s s' s'' : MSIState n} :
  synced s →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s'' := by
  intro hsync h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: diamante comunque
      subst hne
      cases hc with
      | downgrade_from_M_rs j' hj' hM =>
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        have hci : (downgradeMSt s v i₁ j).caches i₁ =
            { s.caches i₁ with queue_cp := (s.parent.queue_cip i₁).eraseIdx j,
                               queue_pc := s.parent.queue_pci i₁ } := by
          simp only [downgradeMSt, update_Fin_gss]
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₁)
            .downgrade_from_M_rs
            { s.caches i₁ with
                state := Bstate.I,
                queue_pc := (s.parent.queue_pci i₁).eraseIdx j',
                queue_cp := (s.parent.queue_cip i₁).eraseIdx j ++ [CPEvent.rsIμ (s.caches i₁).value] } := by
          rw [hci]
          exact cache_msi_step_internal.downgrade_from_M_rs _ j' (by rw [hs2]; exact hj') hM
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        case g =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt, ← hs1]
          exact hj
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1, hs2]
              rw [List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1]
              rw [List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
    · -- indici distinti: il diamante (prova originale)
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
        simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
      have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₂)
          .downgrade_from_M_rs c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_downgrade_from_M_rs_noesc_synced

/-- Same-index case: the two steps are independent (the parent downgrade does not look at the
cache state, the cache release does not look at the parent row), so the diamond holds whenever
the two copies of the queues of `i₁` agree. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs1_noesc_synced {s s' s'' : MSIState n} :
  synced s →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s'' := by
  intro hsync h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgradeM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: diamante comunque
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        have hci : (downgradeMSt s v i₁ j).caches i₁ =
            { s.caches i₁ with queue_cp := (s.parent.queue_cip i₁).eraseIdx j,
                               queue_pc := s.parent.queue_pci i₁ } := by
          simp only [downgradeMSt, update_Fin_gss]
        have hstep : cache_msi_step_internal ((downgradeMSt s v i₁ j).caches i₁)
            .downgrade_from_S_rsS
            { s.caches i₁ with
                state := Bstate.I,
                queue_pc := (s.parent.queue_pci i₁).eraseIdx j',
                queue_cp := (s.parent.queue_cip i₁).eraseIdx j ++ [CPEvent.rsIσ] } := by
          rw [hci]
          exact cache_msi_step_internal.downgrade_from_M_rs1 _ j' (by rw [hs2]; exact hj') hS
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        case g =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt, ← hs1]
          exact hj
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1, hs2]
              rw [List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · simp only [downgradeMSt]
          · intro q
            simp only [downgradeMSt]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs1]
              rw [List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeMSt, update_Fin_gss, hs2]
            · simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeMSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeMSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq1_downgrade_from_M_rs1_noesc_synced

/-! `comm_downgrade_from_M_rq2_rq_data_not_available` senza la via d'uscita per vista cattiva.

L'enunciato "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con code non allineate
(`¬ synced s`) e `i₁ = i₂` (es. `queue_cip i₁ = [rsIσ]` lato parent, `queue_cp = []` lato cache:
`s''` ha `queue_cip i₁ = [rsIμ v]`, nessun `rsIσ` da consumare, e `s' ≠ s''` perché la cache è
in `M` in `s'` e in `I` in `s''`). Qui si dimostra che la via d'uscita per vista cattiva
(`not_reachable_of_M`: cache in `M` con un `rsIσ` in volo per sé) NON serve: con `i₁ = i₂` e code
allineate i due passi commutano sulla stessa coda (il parent consuma la posizione `j`, la cache
accoda in fondo). L'unica via d'uscita rimasta è `¬ synced s`. -/
theorem comm_downgrade_from_M_rq2_rq_data_not_available_noesc_synced {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ synced s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr hsync)
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda `rsIμ` in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?gc)) ?eq⟩
        -- l'`rsIσ` in posizione `j` sopravvive all'`rsIμ` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `M` dopo il downgrade
        case gc => simp only [downgradeSSt, update_Fin_gss]; exact hM
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
      · -- indici distinti: il diamante (identico all'originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq2_rq_data_not_available_noesc_synced

/-! `comm_downgrade_from_M_rq2_rq_data_not_available1` senza la via d'uscita per vista cattiva.

L'enunciato "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con code non allineate
(`¬ synced s`) e `i₁ = i₂` (es. `queue_cip i₁ = [rsIσ]` lato parent, `queue_cp = []` lato cache:
da `s''` l'unico downgrade possibile consuma l'`rsIσ` appena accodato e dà coda `[]`, mentre da
`s'` la cache accoda e dà coda `[rsIσ]`; `s' ≠ s''` perché la cache è in `S` in `s'` e in `I` in
`s''`). Qui si dimostra che la via d'uscita per vista cattiva (`not_reachable_of_S`: cache in `S`
con un `rsIσ` in volo per sé) NON serve: con `i₁ = i₂` e code allineate i due passi commutano
sulla stessa coda (il parent consuma la posizione `j`, la cache accoda in fondo). L'unica via
d'uscita rimasta è `¬ synced s`. -/
theorem comm_downgrade_from_M_rq2_rq_data_not_available1_noesc_synced {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ synced s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr hsync)
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available1 hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda `rsIσ` in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?gc)) ?eq⟩
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        case gc => simp only [downgradeSSt, update_Fin_gss]; exact hS
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
      · -- indici distinti: il diamante (identico all'originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq2_rq_data_not_available1_noesc_synced

/-! `comm_downgrade_from_M_rq2_upgrade_from_I_rs` senza la via d'uscita per vista cattiva.

L'enunciato "originale meno `∨ ¬ MSI.reachable s`" è FALSO negli stati con code non allineate
(`¬ synced s`) e `i₁ = i₂` (es. `queue_pc = [rsM v]` lato cache e `queue_pci i₁ = []` lato parent:
il downgrade riallinea la copia della cache a `[]` e da `s'` nessun `rsM` è più consumabile;
`s' ≠ s''` perché la cache è in `I` in `s'` e in `M` in `s''`). Qui si dimostra che la via
d'uscita per vista cattiva (`not_reachable_of_mu_sig`: token `M` e token `S` in volo per lo stesso
indice) NON serve: con `i₁ = i₂` e code allineate i due passi toccano code diverse dello stesso
indice (`queue_cip` e `queue_pci`) e commutano. L'unica via d'uscita rimasta è `¬ synced s`. -/
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rs_noesc_synced {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ synced s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr hsync)
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma `rsIσ` da `queue_cip`, la cache `rsM v` da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rsIσ` in posizione `j` di `queue_cip i₁` non è toccato dalla cache
        case gp => simp only [update_Fin_gss, ← hs1]; exact hj
        -- l'`rsM v` in posizione `j'` di `queue_pc` (copia del parent, via `hsync`)
        case gc1 => simp only [downgradeSSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc2 => simp only [downgradeSSt, update_Fin_gss]; exact hI
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs1]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (identico all'originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (downgradeSSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
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

#print axioms comm_downgrade_from_M_rq2_upgrade_from_I_rs_noesc_synced

/-! `comm_downgrade_from_M_rq2_upgrade_from_I_rsS` senza la via d'uscita di vista cattiva.

Il caso `i₁ = i₂` (due token `S` in volo per lo stesso indice: `rsIσ` in `queue_cip i₁`,
`rsS v` in `queue_pci i₁`) converge davvero: il parent consuma la posizione `j` di `queue_cip`,
la cache la posizione `j'` di `queue_pc`, code diverse, e i due passi commutano. L'unica via
d'uscita che non si può eliminare è `¬ synced s` (copie delle code non allineate): lì il passo di
cache sovrascrive `queue_cip i₁` con la copia della cache, che può non contenere alcun `rsIσ`, e
il passo del parent da `s''` diventa impossibile mentre `s' ≠ s''` (stato della cache `I` vs `S`).
Per questo l'ipotesi `synced s` è esplicita. -/
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rsS_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma `j` in `queue_cip`, la cache `j'` in `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rsIσ` in posizione `j` di `queue_cip i₁` non è toccato dalla cache
        case gp => simp only [update_Fin_gss, ← hs1]; exact hj
        -- l'`rsS v` in posizione `j'` di `queue_pc i₁` non è toccato dal parent
        case gc1 => simp only [downgradeSSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc2 => simp only [downgradeSSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSSt, update_Fin_gss, ← hs1, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs1]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (identico all'originale)
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

#print axioms comm_downgrade_from_M_rq2_upgrade_from_I_rsS_noesc_synced

/-! `comm_downgrade_from_M_rq2_downgrade_from_M_rs` senza la via d'uscita di vista cattiva.

Il caso `i₁ = i₂` (cache in `M` con un proprio `rsIσ` già in volo in `queue_cip i₁` e un `rqIμ`
in `queue_pc i₁`) converge davvero: il parent consuma la posizione `j` di `queue_cip`, la cache
consuma la posizione `j'` di `queue_pc` e accoda `rsIμ` in fondo a `queue_cp`; l'`rsIσ` in
posizione `j` sopravvive all'accodamento (`j < length`) e `(l ++ [x]).eraseIdx j = l.eraseIdx j ++ [x]`.
L'unica via d'uscita che non si può eliminare è `¬ synced s`: lì il passo di cache sovrascrive
`queue_cip i₁` con la copia della cache, che può non contenere alcun `rsIσ`, e il passo del parent
da `s''` diventa impossibile mentre `s' ≠ s''` (stato della cache `M` vs `I`). Per questo l'ipotesi
`synced s` è esplicita. -/
theorem comm_downgrade_from_M_rq2_downgrade_from_M_rs_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma `j` in `queue_cip`, la cache `j'` in `queue_pc`
        -- e accoda `rsIμ` in fondo a `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rsIσ` in posizione `j` sopravvive all'`rsIμ` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- l'`rqIμ` in posizione `j'` di `queue_pc i₁` non è toccato dal parent
        case gc1 => simp only [downgradeSSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il downgrade
        case gc2 => simp only [downgradeSSt, update_Fin_gss]; exact hM
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
      · -- indici distinti: il diamante (identico all'originale)
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

#print axioms comm_downgrade_from_M_rq2_downgrade_from_M_rs_noesc_synced

/-! `comm_downgrade_from_M_rq2_downgrade_from_M_rs1` senza la via d'uscita di vista cattiva.

Il caso `i₁ = i₂` (cache in `S` con un proprio `rsIσ` già in volo in `queue_cip i₁` e un `rqIσ`
in `queue_pc i₁`) converge davvero: il parent consuma la posizione `j` di `queue_cip`, la cache
consuma la posizione `j'` di `queue_pc` e accoda `rsIσ` in fondo a `queue_cp`; l'`rsIσ` in
posizione `j` sopravvive all'accodamento (`j < length`) e `(l ++ [x]).eraseIdx j = l.eraseIdx j ++ [x]`.
L'unica via d'uscita che non si può eliminare è `¬ synced s`: lì il passo di cache sovrascrive
`queue_cip i₁` con la copia della cache, che può non contenere alcun `rsIσ`, e il passo del parent
da `s''` diventa impossibile mentre `s' ≠ s''` (stato della cache `S` vs `I`). Per questo l'ipotesi
`synced s` è esplicita. -/
theorem comm_downgrade_from_M_rq2_downgrade_from_M_rs1_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `downgradeSSt s i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgradeS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma `j` in `queue_cip`, la cache `j'` in `queue_pc`
        -- e accoda `rsIσ` in fondo a `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.downgrade_from_M_rq2 _ i₁ j ?gp),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rsIσ` in posizione `j` sopravvive all'`rsIσ` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- l'`rqIσ` in posizione `j'` di `queue_pc i₁` non è toccato dal parent
        case gc1 => simp only [downgradeSSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il downgrade
        case gc2 => simp only [downgradeSSt, update_Fin_gss]; exact hS
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
      · -- indici distinti: il diamante (identico all'originale)
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

#print axioms comm_downgrade_from_M_rq2_downgrade_from_M_rs1_noesc_synced

/-! Variante senza via d'uscita `¬ MSI.reachable s` di
`comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available`, sotto l'ipotesi `synced s`.
Il caso "vista cattiva" (`i₁ = i₂`, cache in `M` con la riga a `I`) converge con un diamante
a un passo: il grant cancella la posizione `j` di `queue_cip i₁`, il rilascio accoda in fondo;
le due operazioni commutano (`List.eraseIdx_append_of_lt_length`). -/
theorem comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `M` con la riga a `I`; il diamante vale comunque
      subst hne
      cases hc with
      | rq_data_not_available hM =>
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rsIμ (s.caches i₁).value]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rsIμ (s.caches i₁).value] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?gc)) ?eq⟩
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        case g2 => exact hall
        case gc => simp only [grantMSt, update_Fin_gss]; exact hM
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
    · -- indici distinti: il diamante (prova originale)
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
        simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
      have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .rq_data_not_available c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      case g2 => exact hall
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available_noesc_synced

/-! Variante senza via d'uscita `¬ MSI.reachable s` di
`comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available1`, sotto l'ipotesi `synced s`.
Il caso "vista cattiva" (`i₁ = i₂`, cache in `S` con la riga a `I`) converge con un diamante
a un passo: il grant cancella la posizione `j` di `queue_cip i₁`, il rilascio accoda in fondo;
le due operazioni commutano (`List.eraseIdx_append_of_lt_length`). -/
theorem comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available1_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: cache in `S` con la riga a `I`; il diamante vale comunque
      subst hne
      cases hc with
      | rq_data_not_available1 hS =>
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rsIσ]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rsIσ] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available1 _ ?gc)) ?eq⟩
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        case g2 => exact hall
        case gc => simp only [grantMSt, update_Fin_gss]; exact hS
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
    · -- indici distinti: il diamante (prova originale)
      have hne' : i₂ ≠ i₁ := Ne.symm hne
      have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
        simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
      have hstep : cache_msi_step_internal ((grantMSt s i₁ j).caches i₂) .ld_rq_data_not_availableS c := by
        rw [hci]; exact hc
      refine Or.inl ⟨_,
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
        msi_step_congr (msi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
      case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
      case g2 => exact hall
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available1_noesc_synced

/-! Variante senza via d'uscita `¬ MSI.reachable s` di
`comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs`, sotto l'ipotesi `synced s`.
Il caso "vista cattiva" (`i₁ = i₂`, un `rsM v` in volo verso `i₁` con la riga `i₁` a `I`)
converge con un diamante a un passo: il grant accoda un secondo `rsM` in fondo a `queue_pci i₁`
mentre la cache consuma la posizione `j'`; le due operazioni commutano
(`List.eraseIdx_append_of_lt_length`). -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM v` in volo con la riga a `I`; il diamante vale comunque
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida di `queue_cip i₁` (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- `j'` è una posizione valida di `queue_pc i₁`
        have hb' : j' < (s.caches i₁).queue_pc.length :=
          (List.getElem?_eq_some_iff.mp hj').1
        have herase : ((s.caches i₁).queue_pc ++ [PCEvent.rsM s.parent.value]).eraseIdx j'
            = (s.caches i₁).queue_pc.eraseIdx j' ++ [PCEvent.rsM s.parent.value] :=
          List.eraseIdx_append_of_lt_length hb' _
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?gj ?gI)) ?eq⟩
        -- l'`rqM` in posizione `j` di `queue_cip i₁` non è toccato dalla cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [← hs1]
          exact hj
        case g2 => exact hall
        -- l'`rsM v` in posizione `j'` sopravvive all'append del grant
        case gj =>
          simp only [grantMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hb']
          exact hj'
        case gI => simp only [grantMSt, update_Fin_gss]; exact hI
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
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs2, herase]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale)
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        have hci : (grantMSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']
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
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        case g2 => exact hall
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs_noesc_synced

/-! Gruppo C3b, teorema 1: `comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS` senza la via
d'uscita `¬ MSI.reachable s`.

La versione letterale (enunciato originale meno l'ultimo disgiunto, nessuna ipotesi in più) è
FALSA per gli stati con le copie delle code non allineate e `i₁ = i₂`: il grant riallinea la copia
della cache a quella del parent, il passo di cache riallinea la copia del parent a quella della
cache, e da `s''` il parent può non avere più alcun `rqM` in `queue_cip i₁`. Qui si dimostra
quindi la versione con l'ipotesi `synced s`: essa mostra che la *vista cattiva* (token `S` in volo
verso `i₁` con la riga `i₁` a `I`) NON è un ostacolo alla convergenza: anche lì c'è il diamante. -/

theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il grant accoda `rsM` in fondo a `queue_pci i₁` e toglie l'`rqM` da
        -- `queue_cip i₁`; la cache toglie l'`rsS` da `queue_pc`. Nessuno dei due disabilita l'altro.
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        -- l'`rqM` sta anche nella copia della cache (che il passo di cache non tocca)
        have hj₂ : (s.caches i₁).queue_cp[j]? = some CPEvent.rqM := by rw [← hs1]; exact hj
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.upgrade_from_I_rsS _ v j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqM` è ancora in posizione `j` in `queue_cip i₁` (copia della cache)
        case g1 => simp only [update_Fin_gss]; exact hj₂
        -- le righe non sono toccate dal passo di cache
        case g2 => exact hall
        -- lato destro: l'`rsS v` è ancora in posizione `j'` dopo l'append dell'`rsM`
        case c1 =>
          simp only [grantMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il grant
        case c2 => simp only [grantMSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs1, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantMSt, update_Fin_gss, hs1]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale, invariata)
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS_noesc_synced

/-! Gruppo C3b, teorema 2: `comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs` senza la via
d'uscita `¬ MSI.reachable s`.

La versione letterale (senza ipotesi in più) è FALSA per gli stati con le copie delle code non
allineate e `i₁ = i₂` (vedi il file del teorema 1). Qui si dimostra la versione con l'ipotesi
`synced s`: la *vista cattiva* (cache `i₁` in `M` con la riga `i₁` a `I`) NON è un ostacolo alla
convergenza: anche lì c'è il diamante. -/

theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    by_cases hne : i₁ = i₂
    · -- stesso indice: il grant toglie l'`rqM` da `queue_cip i₁` e accoda `rsM` a `queue_pci i₁`;
      -- la cache toglie l'`rqIμ` da `queue_pc` e accoda `rsIμ` a `queue_cp`. Nessuno dei due
      -- disabilita l'altro: diamante.
      subst hne
      cases hc with
      | downgrade_from_M_rs j' hj' hM =>
        obtain ⟨hs1, hs2⟩ := hsync i₁
        obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hj'
        -- l'`rqM` sta anche nella copia della cache, prima dell'`rsIμ` accodato
        have hj₂ : (s.caches i₁).queue_cp[j]? = some CPEvent.rqM := by rw [← hs1]; exact hj
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj₂
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqM` è ancora in posizione `j` dopo l'append dell'`rsIμ`
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt]; exact hj₂
        -- le righe non sono toccate dal passo di cache
        case g2 => exact hall
        -- lato destro: l'`rqIμ` è ancora in posizione `j'` dopo l'append dell'`rsM`
        case c1 =>
          simp only [grantMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il grant
        case c2 => simp only [grantMSt, update_Fin_gss]; exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt, List.eraseIdx_append_of_lt_length hlt']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs1, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
    · -- indici distinti: il diamante (prova originale, invariata)
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs_noesc_synced

/-! Gruppo C3b, teorema 3: `comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1` senza la via
d'uscita `¬ MSI.reachable s`.

La versione letterale (senza ipotesi in più) è FALSA per gli stati con le copie delle code non
allineate e `i₁ = i₂` (vedi il file del teorema 1). Qui si dimostra la versione con l'ipotesi
`synced s`: la *vista cattiva* (cache `i₁` in `S` con la riga `i₁` a `I`) NON è un ostacolo alla
convergenza: anche lì c'è il diamante. -/

theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1_noesc_synced {s s' s'' : MSIState n}
  (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- `s'` è il record esplicito `grantMSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grantM_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hS =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il grant toglie l'`rqM` da `queue_cip i₁` e accoda `rsM` a `queue_pci i₁`;
        -- la cache toglie l'`rqIσ` da `queue_pc` e accoda `rsIσ` a `queue_cp`. Nessuno dei due
        -- disabilita l'altro: diamante.
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hj'
        -- l'`rqM` sta anche nella copia della cache, prima dell'`rsIσ` accodato
        have hj₂ : (s.caches i₁).queue_cp[j]? = some CPEvent.rqM := by rw [← hs1]; exact hj
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj₂
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs1 _ j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqM` è ancora in posizione `j` dopo l'append dell'`rsIσ`
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt]; exact hj₂
        -- le righe non sono toccate dal passo di cache
        case g2 => exact hall
        -- lato destro: l'`rqIσ` è ancora in posizione `j'` dopo l'append dell'`rsM`
        case c1 =>
          simp only [grantMSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `S` dopo il grant
        case c2 => simp only [grantMSt, update_Fin_gss]; exact hS
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt, List.eraseIdx_append_of_lt_length hlt']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs1, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantMSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt']
            · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante (prova originale, invariata)
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

#print axioms comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1_noesc_synced

/-! `comm_upgrade_to_M_data_avilable_rq2_rq_data_not_available` senza la via d'uscita
`¬ MSI.reachable s` sulla *vista cattiva*.

Il caso di fuga originale (`i₁ = i₂`, cache in `M` con riga a `I`: `not_reachable_of_M`) converge
davvero: il parent cancella l'`rqS` in posizione `j` di `queue_cip i₁` e accoda `rsS` in fondo a
`queue_pci i₁`, la cache accoda `rsIμ` in fondo a `queue_cp` e passa a `I`; i due effetti
commutano (`(l ++ [x]).eraseIdx j = l.eraseIdx j ++ [x]` per `j < l.length`) e il diamante a un
passo esiste, esattamente come nel gemello `..._rq_data_not_available1` (cache in `S`).

L'enunciato *esatto* `_noesc` (senza alcuna ipotesi aggiuntiva) è però falso quando le due copie
di `queue_cip i₁`/`queue_cp` non coincidono (stato non `synced`): allora l'`rqS` che il parent
consuma può non essere nella copia della cache, il grant non è più abilitato da `s''`, e
`s' ≠ s''` (riga `S` contro riga `I`). Perciò qui l'unica ipotesi in più è `synced s`: la via
d'uscita per vista cattiva è eliminata, e nessun disgiunto è cambiato o aggiunto. -/
theorem comm_upgrade_to_M_data_avilable_rq2_rq_data_not_available_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent cancella da `queue_cip i₁`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- l'`rqS` sta nella copia della cache, prima dell'`rsIμ` accodato
        have hj' : (s.caches i₁).queue_cp[j]? = some CPEvent.rqS := by rw [← hs1]; exact hj
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- lato sinistro: l'`rqS` è ancora in posizione `j` dopo l'append dell'`rsIμ`
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- le righe della directory non sono toccate dal passo di cache
        case hI1 => exact hI
        case g2 => exact hnoM
        -- la cache `i₁` è ancora in `M` dopo il grant
        case c1 => simp only [grantSSt, update_Fin_gss]; exact hM
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

#print axioms comm_upgrade_to_M_data_avilable_rq2_rq_data_not_available_noesc_synced

/-! `comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs` senza la via d'uscita
`¬ MSI.reachable s` sulla *vista cattiva*.

Il caso di fuga originale (`i₁ = i₂`, `rsM v` in volo verso `i₁` con riga `i₁` a `I`:
`not_reachable_of_mu_row`) converge davvero: il parent cancella l'`rqS` in posizione `j` di
`queue_cip i₁` e accoda `rsS` in fondo a `queue_pci i₁`; la cache (in `I`) consuma l'`rsM v` in
posizione interna `j'` di `queue_pc` e passa a `M`. Append in fondo e cancellazione interna
commutano e la cache resta in `I` per la seconda mossa: il diamante a un passo esiste, come nel
gemello `..._upgrade_from_I_rsS`.

L'enunciato *esatto* `_noesc` è però falso se le copie delle code non coincidono (stato non
`synced`): l'`rsM` consumato dalla cache può mancare nella copia del parent, o l'`rqS` consumato
dal parent mancare nella copia della cache, e allora nessuno dei due passi è più abilitato
dall'altro lato, mentre `s' ≠ s''` (riga `S` contro riga `I`). Perciò qui l'unica ipotesi in più
è `synced s`: la via d'uscita per vista cattiva è eliminata, nessun disgiunto cambiato o aggiunto. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  have hIrow := grantS_rowI h₁
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
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
            (cache_msi_step_internal.upgrade_from_I_rs _ v j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqS` in `queue_cip i₁` (= `queue_cp`, per `hs1`) non è toccato
        case g1 => simp only [update_Fin_gss]; rw [← hs1]; exact hj
        -- la directory non è toccata dal passo di cache
        case gI => exact hIrow
        case g2 => exact hnoM
        -- lato destro: l'`rsM v` è ancora in posizione `j'` dopo l'append dell'`rsS`
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

#print axioms comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs_noesc_synced

/-! `comm_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs` senza la via d'uscita
`¬ MSI.reachable s` sulla *vista cattiva*.

Il caso di fuga originale (`i₁ = i₂`, cache in `M` con riga a `I`: `not_reachable_of_M`)
converge davvero: il parent cancella l'`rqS` in posizione `j` di `queue_cip i₁` e accoda `rsS` in
fondo a `queue_pci i₁`; la cache (in `M`) consuma l'`rqIμ` in posizione interna `j'` di `queue_pc`,
accoda `rsIμ` in fondo a `queue_cp` e passa a `I`. Su ciascuna coda uno dei due passi accoda in
fondo e l'altro cancella una posizione interna: i due effetti commutano e il diamante a un passo
esiste, come nel gemello `..._downgrade_from_M_rs1` (cache in `S`).

L'enunciato *esatto* `_noesc` è però falso se le copie delle code non coincidono (stato non
`synced`): l'`rqS` consumato dal parent può mancare nella copia della cache, o l'`rqIμ` consumato
dalla cache mancare nella copia del parent, e nessuno dei due passi è più abilitato dall'altro
lato, mentre `s' ≠ s''` (riga `S` contro riga `I`). Perciò qui l'unica ipotesi in più è
`synced s`: la via d'uscita per vista cattiva è eliminata, nessun disgiunto cambiato o aggiunto. -/
theorem comm_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs_noesc_synced
    {s s' s'' : MSIState n} (hsync : synced s) :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  -- `s'` è il record esplicito `grantSSt s i₁ j`
  obtain ⟨j, hj, hnoM, rfl⟩ := grantS_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: append in fondo e cancellazione interna commutano su entrambe le code
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida di `queue_cp`: sopravvive all'append dell'`rsIμ`
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- `j'` è una posizione valida di `queue_pc`: sopravvive all'append dell'`rsS`
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          msi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j ?g1 ?hI1 ?g2),
          msi_step_congr (msi_step_internal.cache _ _ i₁ _
            (cache_msi_step_internal.downgrade_from_M_rs _ j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqS` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la directory non è toccata dal passo di cache
        case hI1 => exact hI
        case g2 => exact hnoM
        -- lato destro: l'`rqIμ` è ancora in posizione `j'` dopo l'append dell'`rsS`
        case c1 =>
          simp only [grantSSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il grant
        case c2 => simp only [grantSSt, update_Fin_gss]; exact hM
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

#print axioms comm_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs_noesc_synced

