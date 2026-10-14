import StarExperimental.MSI_trial_dec
import StarExperimental.MSI_trial_old_pp
import StarExperimental.MSI_trial_old_cc
import StarExperimental.MSI_trial_old_pc1
import StarExperimental.MSI_trial_old_pc2

/-!
# `MSI_trial`: i picchi che in `MSI.lean` si ricongiungevano solo "a meno di" un messaggio

Per ogni coppia di regole di `MSI_def` il teorema `old_*` (copia di `MSI.lean`) dà il ricongiungimento
con passi di `MSI_def`; qui lo si trasporta ai passi di `MSI_trial` (`step_int_old` in entrata,
`step_int_of_old_*` in uscita) e lo si mette nella forma `DecJoin` di `DecreasingDiagrams`.
In `MSI.lean` questi 17 picchi si chiudevano solo a meno di un invalidate stantio (`invMSt`, `dropSt`),
di una richiesta doppia (`reqMSt`) o del valore del parent. Con le regole nuove (scarto, una richiesta
per volta del tipo richiesto) diventano veri ricongiungimenti, vuoti, o uscite per irraggiungibilità.

I lemmi ausiliari (`drop_of_invMSt`, `drop_of_invSSt`, `dropM_dropSt`, `dropS_dropSt`, `honor_of_invSSt`)
dicono che gli stati "a meno di un messaggio" di `MSI.lean` sono raggiunti da uno scarto (etichetta 0)
o da una cessione (etichetta 2) della cache interessata.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Lemmi ausiliari -/

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem step_int_congr {a b b' : MSIState n} {e : IEvent n} (h : step_int a e b) (heq : b = b') :
    step_int a e b' := heq ▸ h

/-- Lo scarto di un `rqIμ` in posizione `j` da una cache in `I` è esattamente `dropSt`
(se la copia `queue_cip i` è allineata). -/
theorem dropM_dropSt {s : MSIState n} {i : Fin n} {j : Nat}
    (hs : s.parent.queue_cip i = (s.caches i).queue_cp)
    (hI : (s.caches i).state = Bstate.I) (hj : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ) :
    step_int s (.cache .drop_rqIμ i) (dropSt s i j) := by
  refine step_int_congr (step_int.cache _ _ i _ (cache_step.drop_rqIμ _ j hj hI)) ?_
  simp only [dropSt]
  rw [← hs, update_Fin_self]

/-- Lo scarto di un `rqIσ` in posizione `j` da una cache in `I` è esattamente `dropSt`. -/
theorem dropS_dropSt {s : MSIState n} {i : Fin n} {j : Nat}
    (hs : s.parent.queue_cip i = (s.caches i).queue_cp)
    (hI : (s.caches i).state = Bstate.I) (hj : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIσ) :
    step_int s (.cache .drop_rqIσ i) (dropSt s i j) := by
  refine step_int_congr (step_int.cache _ _ i _ (cache_step.drop_rqIσ _ j hj hI)) ?_
  simp only [dropSt]
  rw [← hs, update_Fin_self]

/-- Da `invMSt s i` con la cache `i` in `I`: lo scarto dell'`rqIμ` appena accodato riporta a `s`. -/
theorem drop_of_invMSt {s : MSIState n} {i : Fin n} (hs : synced s) (hI : (s.caches i).state = Bstate.I) :
    step_int (invMSt s i) (.cache .drop_rqIμ i) s := by
  obtain ⟨h1, h2⟩ := hs i
  refine step_int_congr (step_int.cache _ _ i _
    (cache_step.drop_rqIμ _ (s.parent.queue_pci i).length ?_ ?_)) ?_
  · simp only [invMSt, update_Fin_gss]; exact lst_get _ _
  · simp only [invMSt, update_Fin_gss]; exact hI
  · refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invMSt, update_Fin_gss, lst_erase, h1, h2]
      · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invMSt, update_Fin_gss, h1]
      · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invMSt, update_Fin_gss, lst_erase, h2]
      · simp only [invMSt, update_Fin_gso2 _ _ _ _ hq]

/-- Da `invSSt s i` con la cache `i` in `I`: lo scarto dell'`rqIσ` appena accodato riporta a `s`. -/
theorem drop_of_invSSt {s : MSIState n} {i : Fin n} (hs : synced s) (hI : (s.caches i).state = Bstate.I) :
    step_int (invSSt s i) (.cache .drop_rqIσ i) s := by
  obtain ⟨h1, h2⟩ := hs i
  refine step_int_congr (step_int.cache _ _ i _
    (cache_step.drop_rqIσ _ (s.parent.queue_pci i).length ?_ ?_)) ?_
  · simp only [invSSt, update_Fin_gss]; exact lst_get _ _
  · simp only [invSSt, update_Fin_gss]; exact hI
  · refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, lst_erase, h1, h2]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, h1]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, lst_erase, h2]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]

/-- Da `invSSt s i` con la cache `i` in `S`: cedere sull'`rqIσ` appena accodato porta esattamente
dove porta il rilascio spontaneo da `s`. -/
theorem honor_of_invSSt {s : MSIState n} {i : Fin n} (hs : synced s) (hS : (s.caches i).state = Bstate.S) :
    ∃ d, step_int (invSSt s i) (.cache .downgrade_from_S_rsS i) d ∧
      step_int s (.cache .ld_rq_data_not_availableS i) d := by
  obtain ⟨h1, h2⟩ := hs i
  refine ⟨_, step_int.cache _ _ i _
    (cache_step.downgrade_from_M_rs1 _ (s.parent.queue_pci i).length ?_ ?_),
    step_int_congr (step_int.cache _ _ i _ (cache_step.rq_data_not_available1 _ hS)) ?_⟩
  · simp only [invSSt, update_Fin_gss]; exact lst_get _ _
  · simp only [invSSt, update_Fin_gss]; exact hS
  · refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, lst_erase, h1, h2]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, h1]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]
    · intro q
      by_cases hq : q = i
      · subst hq; simp only [invSSt, update_Fin_gss, lst_erase, h2]
      · simp only [invSSt, update_Fin_gso2 _ _ _ _ hq]

/-- Un passo del parent non cambia lo stato di nessuna cache. -/
theorem state_parent_step {s t : MSIState n} {e : ParentUpdQueueInternalEvent n} {i : Fin n}
    (h : step_int s (.parent e i) t) (k : Fin n) : (t.caches k).state = (s.caches k).state := by
  cases h with
  | parent_upd_queue _ _ _ _ =>
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss]
      · simp [update_Fin_gso2 _ _ _ _ hk]

/-- Dopo `downgrade_from_M_rs` la cache è in `I`. -/
theorem honorM_state {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .downgrade_from_M_rs i) s') :
    (s'.caches i).state = Bstate.I := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | downgrade_from_M_rs _ _ _ => simp [update_Fin_gss]

/-- Dopo `downgrade_from_S_rsS` la cache è in `I`. -/
theorem honorS_state {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .downgrade_from_S_rsS i) s') :
    (s'.caches i).state = Bstate.I := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | downgrade_from_M_rs1 _ _ _ => simp [update_Fin_gss]

/-- Un messaggio diverso da quello cancellato sopravvive alla cancellazione (eventualmente slittato). -/
theorem getElem?_eraseIdx_survive {α} {l : List α} {j j' : Nat} {a b : α}
    (hj : l[j]? = some a) (hj' : l[j']? = some b) (hne : b ≠ a) :
    ∃ j'' : Nat, (l.eraseIdx j)[j'']? = some b := by
  have hjj : j' ≠ j := fun h => hne (by rw [h, hj] at hj'; exact (Option.some.inj hj').symm)
  rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
  · exact ⟨j', by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj'⟩
  · exact ⟨j' - 1, by
      rw [List.getElem?_eraseIdx_of_ge (by omega), show j' - 1 + 1 = j' by omega]; exact hj'⟩

/-! ## I picchi -/

/-- Picco `old_downgrade_from_M_rq1_downgrade_from_M_rq1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Due consumi di `rsIμ`. Stesso indice e stessa posizione: lo stesso passo, `s' = s''`. Stesso indice e posizioni
diverse: due token `M` in volo per `i₁`, uscita `not_reach_of_two_mu`. Indici diversi: se la riga `i₂` è `M`
uscita `not_reach_of_mu_rowJ` (token `M` per `i₁` con la riga di `i₂ ≠ i₁` non a `I`), altrimenti
`not_reach_of_mu_row` (token `M` per `i₂` con la riga `i₂` non a `M`). Nessun quadrato: in `MSI.lean` i due ordini
differivano nel valore del parent. -/
theorem peak_downgrade_from_M_rq1_downgrade_from_M_rq1 {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v₁) i₁) s') (h2 : step_int s (.parent (.downgrade_from_M_rq1 v₂) i₂) s'') :
    DecJoin 1 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeM_inv (step_int_old h1 (fun h => h))
  obtain ⟨j₂, hj₂, rfl⟩ := downgradeM_inv (step_int_old h2 (fun h => h))
  by_cases hne : i₁ = i₂
  · subst hne
    by_cases hj : j₁ = j₂
    · subst hj
      rw [hj₁] at hj₂
      cases hj₂
      exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr (not_reach_of_two_mu (i := i₁) ?_))
      have := two_le_countP_of_ne isReleaseM (s.parent.queue_cip i₁) hj₁ hj₂ hj rfl rfl
      unfold muMsgs; omega
  · by_cases hrow : s.parent.shared_state i₂ = Bstate.M
    · exact Or.inr (Or.inr (not_reach_of_mu_rowJ hne (muMsgs_ne_zero_of_rsIμ hj₁) (by rw [hrow]; nofun)))
    · exact Or.inr (Or.inr (not_reach_of_mu_row (muMsgs_ne_zero_of_rsIμ hj₂) hrow))

/-- Picco `old_downgrade_from_M_rq1_upgrade_to_M_invalid_all` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIμ v` su `i₁` e invalidate `rqIμ` verso `i₂` (riga `i₂ = M`). Il disgiunto "quadrato" del vecchio
teorema si solleva a `DecJoin.square`. Il disgiunto `s₁ = invMSt s' i₂` (consumo da `s''`): con `i₁ ≠ i₂` lo
stato è irraggiungibile (`not_reach_of_mu_rowJ`); con `i₁ = i₂` la cache `i₁`, che ha un rilascio in volo, è in
`I` (altrimenti `not_reach_of_M`/`not_reach_of_S`) e scarta l'`rqIμ` stantio: `DecJoin.mix 1 < 6` con
`s'' →1→ invMSt s' i₂ →0→ s'`. Senza `synced s` si esce con `not_reach_of_not_synced`. -/
theorem peak_downgrade_from_M_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have h1o := step_int_old h1 (fun h => h)
  have h2o := step_int_old h2 (fun h => h)
  rcases old_downgrade_from_M_rq1_upgrade_to_M_invalid_all h1o h2o with
    ⟨d, hb, hc⟩ | ⟨s₁, hb, rfl⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hc) (step_int_of_old_parent hb) rfl rfl)
  · obtain ⟨j, hj, rfl⟩ := downgradeM_inv h1o
    obtain ⟨_, hM, rfl⟩ := invalidateM_inv h2o
    have hmu := muMsgs_ne_zero_of_rsIμ hj
    by_cases hne : i₁ = i₂
    · subst hne
      cases hst : (s.caches i₁).state with
      | M => exact Or.inr (Or.inr (not_reach_of_M hst (Or.inl hmu)))
      | S => exact Or.inr (Or.inr (not_reach_of_S hst (Or.inl hmu)))
      | I =>
        have hs' : synced (downgradeMSt s v i₁ j) := synced_step_int hs h1
        have hI' : ((downgradeMSt s v i₁ j).caches i₁).state = Bstate.I := by
          simp only [downgradeMSt, update_Fin_gss]; exact hst
        exact Or.inl (DecJoin.mix (by decide) (Or.inl rfl) trans_refl.refl
          (ltStar_cons (step_int_of_old_parent hb) (by simp [lab])
            (ltStar_single (drop_of_invMSt hs' hI') (by simp [lab]))))
    · exact Or.inr (Or.inr (not_reach_of_mu_rowJ hne hmu (by rw [hM]; nofun)))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

/-- Picco `old_downgrade_from_M_rq1_upgrade_to_M_invalid_all1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIμ v` su `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`). Sempre un'uscita: con `i₁ = i₂` un
token `M` in volo per `i₁` con la riga `i₁` a `S` (`not_reach_of_mu_row`); con `i₁ ≠ i₂` un token `M` per `i₁`
con la riga di `i₂` non a `I` (`not_reach_of_mu_rowJ`). -/
theorem peak_downgrade_from_M_rq1_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨j, hj, -⟩ := downgradeM_inv (step_int_old h1 (fun h => h))
  obtain ⟨-, hS, -⟩ := invalidateS_inv (step_int_old h2 (fun h => h))
  have hmu := muMsgs_ne_zero_of_rsIμ hj
  by_cases hne : i₁ = i₂
  · subst hne
    exact Or.inr (Or.inr (not_reach_of_mu_row hmu (by rw [hS]; nofun)))
  · exact Or.inr (Or.inr (not_reach_of_mu_rowJ hne hmu (by rw [hS]; nofun)))

/-- Picco `old_downgrade_from_M_rq1_upgrade_to_M_invalid_all2` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIμ v` su `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`, richiesta `rqS` di `k ≠ i₂`).
Sempre un'uscita, come per `invalid_allS`: `not_reach_of_mu_row` se `i₁ = i₂`, `not_reach_of_mu_rowJ` altrimenti. -/
theorem peak_downgrade_from_M_rq1_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨j, hj, -⟩ := downgradeM_inv (step_int_old h1 (fun h => h))
  obtain ⟨-, -, hS, -⟩ := invalidateS2_inv (step_int_old h2 (fun h => h))
  have hmu := muMsgs_ne_zero_of_rsIμ hj
  by_cases hne : i₁ = i₂
  · subst hne
    exact Or.inr (Or.inr (not_reach_of_mu_row hmu (by rw [hS]; nofun)))
  · exact Or.inr (Or.inr (not_reach_of_mu_rowJ hne hmu (by rw [hS]; nofun)))

/-- Picco `old_downgrade_from_M_rq2_upgrade_to_M_invalid_all` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIσ` su `i₁` e invalidate `rqIμ` verso `i₂` (riga `i₂ = M`). Sempre un'uscita: con `i₁ = i₂` un
token `S` in volo per `i₁` con la riga `i₁` a `M` (`not_reach_of_sig_row`); con `i₁ ≠ i₂` un token `S` per `i₁`
con la riga di `i₂` a `M` (`not_reach_of_sig_rowM`). -/
theorem peak_downgrade_from_S_rq1S_upgrade_to_M_invalid_all {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨j, hj, -⟩ := downgradeS_inv (step_int_old h1 (fun h => h))
  obtain ⟨-, hM, -⟩ := invalidateM_inv (step_int_old h2 (fun h => h))
  have hsig := sigMsgs_ne_zero_of_rsIσ hj
  by_cases hne : i₁ = i₂
  · subst hne
    exact Or.inr (Or.inr (not_reach_of_sig_row hsig (by rw [hM]; nofun)))
  · exact Or.inr (Or.inr (not_reach_of_sig_rowM hne hsig hM))

/-- Picco `old_downgrade_from_M_rq2_upgrade_to_M_invalid_all1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIσ` su `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`, un `rqM` di qualche `k`). Il disgiunto
"quadrato" si solleva a `DecJoin.square`. Il disgiunto `s₁ = invSSt s' i₂`: con `i₁ = i₂` la cache `i₁` (rilascio
in volo) è in `I` (altrimenti `not_reach_of_M`/`not_reach_of_S`) e scarta l'`rqIσ` stantio, `DecJoin.mix 1 < 6` con
`s'' →1→ invSSt s' i₂ →0→ s'`; con `i₁ ≠ i₂` è in realtà un quadrato: l'invalidate è ancora abilitato da `s'`
(la riga `i₂` non cambia, l'`rqM` di `k` sopravvive alla cancellazione dell'`rsIσ`, `getElem?_eraseIdx_survive`).
Senza `synced s` si esce con `not_reach_of_not_synced`. -/
theorem peak_downgrade_from_S_rq1S_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have h1o := step_int_old h1 (fun h => h)
  have h2o := step_int_old h2 (fun h => h)
  rcases old_downgrade_from_M_rq2_upgrade_to_M_invalid_all1 h1o h2o with
    ⟨d, hb, hc⟩ | ⟨s₁, hb, rfl⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hc) (step_int_of_old_parent hb) rfl rfl)
  · obtain ⟨j, hj, rfl⟩ := downgradeS_inv h1o
    obtain ⟨⟨k, j', hk⟩, hS, rfl⟩ := invalidateS_inv h2o
    have hsig := sigMsgs_ne_zero_of_rsIσ hj
    by_cases hne : i₁ = i₂
    · subst hne
      cases hst : (s.caches i₁).state with
      | M => exact Or.inr (Or.inr (not_reach_of_M hst (Or.inr (Or.inl hsig))))
      | S => exact Or.inr (Or.inr (not_reach_of_S hst (Or.inr (Or.inl hsig))))
      | I =>
        have hs' : synced (downgradeSSt s i₁ j) := synced_step_int hs h1
        have hI' : ((downgradeSSt s i₁ j).caches i₁).state = Bstate.I := by
          simp only [downgradeSSt, update_Fin_gss]; exact hst
        exact Or.inl (DecJoin.mix (by decide) (Or.inl rfl) trans_refl.refl
          (ltStar_cons (step_int_of_old_parent hb) (by simp [lab])
            (ltStar_single (drop_of_invSSt hs' hI') (by simp [lab]))))
    · have hne' : i₂ ≠ i₁ := Ne.symm hne
      have hS' : (downgradeSSt s i₁ j).parent.shared_state i₂ = Bstate.S := by
        simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
      obtain ⟨j'', hk''⟩ : ∃ j'', ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqM := by
        by_cases hki : k = i₁
        · subst hki
          simp only [downgradeSSt, update_Fin_gss]
          exact getElem?_eraseIdx_survive hj hk nofun
        · exact ⟨j', by simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      exact Or.inl (DecJoin.square
        (step_int.parent_upd_queue _ _ _ i₂
          (parent_msi_step.upgrade_to_M_invalid_all1 _ k i₂ j'' hk'' hS'))
        (step_int_of_old_parent hb) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

/-- Picco `old_downgrade_from_M_rq2_upgrade_to_M_invalid_all2` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Consumo di `rsIσ` su `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`, un `rqS` di `k ≠ i₂`). Come per
`invalid_allS`: quadrato sollevato; disgiunto `s₁ = invSSt s' i₂` con `i₁ = i₂` → scarto (`DecJoin.mix 1 < 6`,
cache in `I` o uscita), con `i₁ ≠ i₂` → quadrato ricostruito (`getElem?_eraseIdx_survive`); `s' = s''`; uscita. -/
theorem peak_downgrade_from_S_rq1S_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 1 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have h1o := step_int_old h1 (fun h => h)
  have h2o := step_int_old h2 (fun h => h)
  rcases old_downgrade_from_M_rq2_upgrade_to_M_invalid_all2 h1o h2o with
    ⟨d, hb, hc⟩ | ⟨s₁, hb, rfl⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hc) (step_int_of_old_parent hb) rfl rfl)
  · obtain ⟨j, hj, rfl⟩ := downgradeS_inv h1o
    obtain ⟨⟨j', hk⟩, hik, hS, rfl⟩ := invalidateS2_inv h2o
    have hsig := sigMsgs_ne_zero_of_rsIσ hj
    by_cases hne : i₁ = i₂
    · subst hne
      cases hst : (s.caches i₁).state with
      | M => exact Or.inr (Or.inr (not_reach_of_M hst (Or.inr (Or.inl hsig))))
      | S => exact Or.inr (Or.inr (not_reach_of_S hst (Or.inr (Or.inl hsig))))
      | I =>
        have hs' : synced (downgradeSSt s i₁ j) := synced_step_int hs h1
        have hI' : ((downgradeSSt s i₁ j).caches i₁).state = Bstate.I := by
          simp only [downgradeSSt, update_Fin_gss]; exact hst
        exact Or.inl (DecJoin.mix (by decide) (Or.inl rfl) trans_refl.refl
          (ltStar_cons (step_int_of_old_parent hb) (by simp [lab])
            (ltStar_single (drop_of_invSSt hs' hI') (by simp [lab]))))
    · have hne' : i₂ ≠ i₁ := Ne.symm hne
      have hS' : (downgradeSSt s i₁ j).parent.shared_state i₂ = Bstate.S := by
        simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hne']; exact hS
      obtain ⟨j'', hk''⟩ : ∃ j'', ((downgradeSSt s i₁ j).parent.queue_cip k)[j'']? = some CPEvent.rqS := by
        by_cases hki : k = i₁
        · subst hki
          simp only [downgradeSSt, update_Fin_gss]
          exact getElem?_eraseIdx_survive hj hk nofun
        · exact ⟨j', by simp only [downgradeSSt, update_Fin_gso2 _ _ _ _ hki]; exact hk⟩
      exact Or.inl (DecJoin.square
        (step_int.parent_upd_queue _ _ _ i₂
          (parent_msi_step.upgrade_to_M_invalid_all2 _ k i₂ j'' hk'' hik hS'))
        (step_int_of_old_parent hb) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

/-- Picco `old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Grant di `S` a `i₁` e invalidate `rqIσ` verso `i₂` (riga `i₂ = S`). Quadrato → `DecJoin.square`. Disgiunto
`s₁ = invSSt s' i₂` (il grant da `s''`): si guarda la cache `i₂`: in `M` uscita (`not_reach_of_M`, riga a `S`);
in `I` scarta l'`rqIσ` (`DecJoin.mix 4 < 6`, `s'' →4→ s₁ →0→ s'`); in `S` cede sull'`rqIσ` da `s₁` e rilascia
spontaneamente da `s'`, stesso stato (`honor_of_invSSt`): `s' →2→ d`, `s'' →4→ s₁ →2→ d`. I due disgiunti con
i cammini 4+3+2 / 6+3+2 e 4+2+3 / 6+2+3 diventano `DecJoin.mix 4 < 6` con il passo `6` da `s'` come `b'`.
Poi `s' = s''` e l'uscita; senza `synced s` si esce con `not_reach_of_not_synced`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have h1o := step_int_old h1 (fun h => h)
  have h2o := step_int_old h2 (fun h => h)
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2 h1o h2o with
    ⟨d, hb, hc⟩ | ⟨s₁, hb, rfl⟩ | ⟨x, y, t₁, u₁, d, hx, hy, hxt, htd, hyu, hud⟩ |
    ⟨x, y, t₁, u₁, d, hx, hy, hxt, htd, hyu, hud⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hc) (step_int_of_old_parent hb) rfl rfl)
  · have hs' : synced s' := synced_step_int hs h1
    obtain ⟨-, -, hS, rfl⟩ := invalidateS2_inv h2o
    have hst' : (s'.caches i₂).state = (s.caches i₂).state := state_parent_step h1 i₂
    cases hst : (s.caches i₂).state with
    | M => exact Or.inr (Or.inr (not_reach_of_M hst (Or.inr (Or.inr (by rw [hS]; nofun)))))
    | I =>
      exact Or.inl (DecJoin.mix (by decide) (Or.inl rfl) trans_refl.refl
        (ltStar_cons (step_int_of_old_parent hb) (by simp [lab])
          (ltStar_single (drop_of_invSSt hs' (hst'.trans hst)) (by simp [lab]))))
    | S =>
      obtain ⟨d, hd₁, hd₂⟩ := honor_of_invSSt hs' (hst'.trans hst)
      exact Or.inl (DecJoin.mix (by decide) (Or.inl rfl)
        (ltStar_single hd₂ (by simp [lab]))
        (ltStar_cons (step_int_of_old_parent hb) (by simp [lab])
          (ltStar_single hd₁ (by simp [lab]))))
  · exact Or.inl (DecJoin.mix (by decide)
      (Or.inr (lstep_of' (step_int_of_old_parent hy) rfl))
      (ltStar_cons (step_int_of_old_cache hyu ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
        (ltStar_single (step_int_of_old_cache hud ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))
      (ltStar_cons (step_int_of_old_parent hx) (by simp [lab])
        (ltStar_cons (step_int_of_old_cache hxt ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_single (step_int_of_old_cache htd ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))))
  · exact Or.inl (DecJoin.mix (by decide)
      (Or.inr (lstep_of' (step_int_of_old_parent hy) rfl))
      (ltStar_cons (step_int_of_old_cache hyu ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
        (ltStar_single (step_int_of_old_cache hud ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))
      (ltStar_cons (step_int_of_old_parent hx) (by simp [lab])
        (ltStar_cons (step_int_of_old_cache hxt ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_single (step_int_of_old_cache htd ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

/-- Picco `old_rq_data_not_available_downgrade_from_M_rs` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Rilascio spontaneo da `M` e cessione sull'`rqIμ` in posizione `j`, stessa cache `i`. Entrambi accodano
`rsIμ value` e portano la cache in `I`; il rilascio spontaneo lascia l'`rqIμ`, ormai stantio, in `queue_pc`:
la cache (in `I`) lo scarta e arriva esattamente in `s''`. `DecJoin.top` con `s' →0→ s''` da un lato e
`big_refl` dall'altro. -/
theorem peak_rq_data_not_available_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available hM =>
      cases h2 with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | downgrade_from_M_rs j hj _ =>
          refine Or.inl (DecJoin.top (big_of_ltStar (ltStar_single
            (step_int_congr (step_int.cache _ _ i _ (cache_step.drop_rqIμ _ j ?_ ?_)) ?_)
            (by simp [lab]))) (big_refl _ _))
          · simp only [update_Fin_gss]; exact hj
          · simp only [update_Fin_gss]
          · simp only [update_Fin_gss, update_Fin_update_Fin_same]

/-- Picco `old_rq_data_not_available1_downgrade_from_M_rs1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Rilascio spontaneo da `S` e cessione sull'`rqIσ` in posizione `j`, stessa cache `i`: come per `M`, la cache
in `I` scarta l'`rqIσ` stantio e arriva in `s''` (`DecJoin.top`, `s' →0→ s''`, `big_refl`). -/
theorem peak_ld_rq_data_not_availableS_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache c₁ _ _ hc₁ =>
    cases hc₁ with
    | rq_data_not_available1 hS =>
      cases h2 with
      | cache c₂ _ _ hc₂ =>
        cases hc₂ with
        | downgrade_from_M_rs1 j hj _ =>
          refine Or.inl (DecJoin.top (big_of_ltStar (ltStar_single
            (step_int_congr (step_int.cache _ _ i _ (cache_step.drop_rqIσ _ j ?_ ?_)) ?_)
            (by simp [lab]))) (big_refl _ _))
          · simp only [update_Fin_gss]; exact hj
          · simp only [update_Fin_gss]
          · simp only [update_Fin_gss, update_Fin_update_Fin_same]

/-- Picco `old_upgrade_from_I_rq_upgrade_from_I_rq1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Vuoto: la richiesta di `M` vuole una store in testa a `extqueue.rq` (`wantsM`), quella di `S` una load
(`wantsS`); le due teste non coincidono. -/
theorem peak_upgrade_from_I_rq_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i) s'') :
    DecJoin 7 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨-, -, -, v, rst, hM⟩ := reqM_guards h1
  obtain ⟨-, -, -, rst', hS⟩ := reqS_guards h2
  rw [hM] at hS
  cases hS

/-- Picco `old_upgrade_from_I_rq_upgrade_from_I_rs` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Vuoto: la richiesta vuole `¬ grantInFlight`, la presa del grant vuole un `rsM v` in `queue_pc`. -/
theorem peak_upgrade_from_I_rq_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i) s'') :
    DecJoin 7 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨-, -, hg, -⟩ := reqM_guards h1
  cases h2 with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | upgrade_from_I_rs _ j hj _ =>
      exact absurd (Or.inl ⟨v, List.mem_of_getElem? hj⟩) hg

/-- Picco `old_upgrade_from_I_rq_upgrade_from_I_rsS` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Vuoto: la richiesta vuole `¬ grantInFlight`, la presa del grant vuole un `rsS v` in `queue_pc`. -/
theorem peak_upgrade_from_I_rq_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i) s'') :
    DecJoin 7 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨-, -, hg, -⟩ := reqM_guards h1
  cases h2 with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | upgrade_from_I_rsS _ j hj _ =>
      exact absurd (Or.inr ⟨v, List.mem_of_getElem? hj⟩) hg

/-- Picco `old_upgrade_from_I_rq1_upgrade_from_I_rs` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Vuoto: la richiesta di `S` vuole `¬ grantInFlight`, la presa del grant vuole un `rsM v` in `queue_pc`. -/
theorem peak_upgrade_from_I_rqS_upgrade_from_I_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rqS i) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i) s'') :
    DecJoin 7 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨-, -, hg, -⟩ := reqS_guards h1
  cases h2 with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | upgrade_from_I_rs _ j hj _ =>
      exact absurd (Or.inl ⟨v, List.mem_of_getElem? hj⟩) hg

/-- Picco `old_upgrade_from_I_rq1_upgrade_from_I_rsS` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Vuoto: la richiesta di `S` vuole `¬ grantInFlight`, la presa del grant vuole un `rsS v` in `queue_pc`. -/
theorem peak_upgrade_from_I_rqS_upgrade_from_I_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rqS i) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i) s'') :
    DecJoin 7 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  obtain ⟨-, -, hg, -⟩ := reqS_guards h1
  cases h2 with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | upgrade_from_I_rsS _ j hj _ =>
      exact absurd (Or.inr ⟨v, List.mem_of_getElem? hj⟩) hg

/-- Picco `old_downgrade_from_M_rs_downgrade_from_M_rs` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Due cessioni sull'`rqIμ` della stessa cache `i`. Stessa posizione: `s' = s''`. Posizioni diverse: la cache è in
`I` e l'altro `rqIμ` è stantio, `dropSt s' i j = t = dropSt s'' i j'`: entrambe lo scartano (`dropM_dropSt`,
servono le code allineate, `synced s`), `DecJoin.top` con `s' →0→ t` e `s'' →0→ t`. Il disgiunto "quadrato"
del vecchio teorema (mai prodotto) si solleva comunque con `step_int_of_old_cache`. -/
theorem peak_downgrade_from_M_rs_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .downgrade_from_M_rs i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have hI' := honorM_state h1
  have hI'' := honorM_state h2
  have hs' := synced_step_int hs h1
  have hs'' := synced_step_int hs h2
  rcases old_downgrade_from_M_rs_downgrade_from_M_rs (step_int_old h1 (fun h => h))
      (step_int_old h2 (fun h => h)) with
    ⟨d, hb, hc⟩ | ⟨t, ⟨j₁, hj₁, rfl⟩, ⟨j₂, hj₂, heq⟩⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hc ⟨nofun, nofun⟩)
      (step_int_of_old_cache hb ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inl (DecJoin.top
      (big_of_ltStar (ltStar_single (dropM_dropSt (hs' i).1 hI' hj₁) (by simp [lab])))
      (big_of_ltStar (ltStar_single (step_int_congr (dropM_dropSt (hs'' i).1 hI'' hj₂) heq)
        (by simp [lab]))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

/-- Picco `old_downgrade_from_M_rs1_downgrade_from_M_rs1` di `MSI.lean`, ricongiunto solo "a meno di" un messaggio: qui con la regola nuova.
Due cessioni sull'`rqIσ` della stessa cache `i`: come per `M`, stessa posizione → `s' = s''`; posizioni diverse →
entrambe scartano l'altro `rqIσ` stantio (`dropS_dropSt`, `DecJoin.top`). -/
theorem peak_downgrade_from_S_rsS_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .downgrade_from_S_rsS i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 2 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  have hI' := honorS_state h1
  have hI'' := honorS_state h2
  have hs' := synced_step_int hs h1
  have hs'' := synced_step_int hs h2
  rcases old_downgrade_from_M_rs1_downgrade_from_M_rs1 (step_int_old h1 (fun h => h))
      (step_int_old h2 (fun h => h)) with
    ⟨d, hb, hc⟩ | ⟨t, ⟨j₁, hj₁, rfl⟩, ⟨j₂, hj₂, heq⟩⟩ | heq | hnr
  · exact Or.inl (DecJoin.square (step_int_of_old_cache hc ⟨nofun, nofun⟩)
      (step_int_of_old_cache hb ⟨nofun, nofun⟩) rfl rfl)
  · exact Or.inl (DecJoin.top
      (big_of_ltStar (ltStar_single (dropS_dropSt (hs' i).1 hI' hj₁) (by simp [lab])))
      (big_of_ltStar (ltStar_single (step_int_congr (dropS_dropSt (hs'' i).1 hI'' hj₂) heq)
        (by simp [lab]))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hnr)

end MSITrial
