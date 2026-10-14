import StarExperimental.MSI_trial_dec

/-!
# `MSI_trial`: i picchi con uno scarto (`drop_rqIμ`, `drop_rqIσ`) contro un evento di cache

I 19 picchi `drop × drop` e `drop × (evento di cache)` nella forma `DecJoin` di `MSI_trial_dec`
(etichette: scarto 0, rilascio/onore 2, presa 3, richiesta 7). Forme ricorrenti:

* **cache diverse**: i due passi toccano record e code diverse, quadrato (`dropA_cache_cache_ne`);
* **stessa cache, guardie incompatibili** (lo scarto vuole `I`, rilasci e onori vogliono `M` o `S`):
  picco vuoto, si deriva `False`;
* **stessa cache, scarto / richiesta**: quadrato (la richiesta accoda in `queue_cp`, lo scarto toglie
  da `queue_pc`; togliere un `rqIμ`/`rqIσ` non crea grant in volo, `List.mem_of_mem_eraseIdx`);
* **stessa cache, due scarti**: stessa posizione `s' = s''`, posizioni diverse quadrato con il secondo
  indice riaggiustato (`dropA_two_pos`: doppia cancellazione);
* **stessa cache, scarto / presa del grant**: ricongiungimento in tre passi con `DecJoin.mix`
  (`0 < 3`): da `s'` la presa (`= 3`) poi rilascio e consumo al parent (`2`, `1`); da `s''` solo passi
  `< 3` (onore `2` e consumo `1`, oppure rilascio `2`, scarto `0` e consumo `1`). Il consumo al parent
  legge la copia `queue_cip` **appena riallineata** dal passo di cache che lo precede, quindi non serve
  `synced s`: i due lati finiscono letteralmente nello stesso stato senza uscita `¬ Reach s`.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Mattoni -/

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem dropA_step_int_congr {s s' s'' : MSIState n} {e : IEvent n}
    (h : step_int s e s') (heq : s' = s'') : step_int s e s'' := heq ▸ h

/-- Inversione di un passo di cache: la regola applicata e lo stato di arrivo esplicito. -/
theorem dropA_cache_inv {s s' : MSIState n} {e : CEvent} {i : Fin n}
    (h : step_int s (.cache e i) s') :
    ∃ c, cache_step (s.caches i) e c ∧
      s' = { s with caches := update_Fin i c s.caches,
                    parent.queue_cip := update_Fin i c.queue_cp s.parent.queue_cip,
                    parent.queue_pci := update_Fin i c.queue_pc s.parent.queue_pci } := by
  cases h with
  | cache c _ _ hc => exact ⟨c, hc, rfl⟩

/-- Due passi di cache su indici diversi commutano: ciascuno legge e scrive solo il proprio record e
le proprie copie delle code. -/
theorem dropA_cache_cache_ne {s s' s'' : MSIState n} {e₁ e₂ : CEvent} {i₁ i₂ : Fin n}
    (hne : ¬ i₁ = i₂)
    (h1 : step_int s (.cache e₁ i₁) s') (h2 : step_int s (.cache e₂ i₂) s'') :
    ∃ d, step_int s' (.cache e₂ i₂) d ∧ step_int s'' (.cache e₁ i₁) d := by
  obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
  obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
  refine ⟨_, step_int.cache _ c₂ i₂ e₂ (by simp only [update_Fin_gso _ _ _ _ hne]; exact hc₂), ?_⟩
  refine dropA_step_int_congr
    (step_int.cache _ c₁ i₁ e₁ (by simp only [update_Fin_gso _ _ _ _ (Ne.symm hne)]; exact hc₁)) ?_
  simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ hne]

/-- Togliere prima `b` e poi `a` (con `a < b`) è come togliere prima `a` e poi `b - 1`. -/
theorem dropA_eraseIdx_swap {α : Type} : ∀ (l : List α) (a b : Nat), a < b →
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

/-- Due posizioni `j₁ ≠ j₂` della stessa lista: dopo aver tolto `j₁` l'elemento di `j₂` sta in `k₂`
(`j₂ - 1` se `j₁ < j₂`, `j₂` altrimenti), dopo aver tolto `j₂` quello di `j₁` sta in `k₁`, e le due
doppie cancellazioni coincidono. -/
theorem dropA_two_pos {α : Type} (l : List α) {j₁ j₂ : Nat} (hne : j₁ ≠ j₂) :
    ∃ k₁ k₂, (l.eraseIdx j₁)[k₂]? = l[j₂]? ∧ (l.eraseIdx j₂)[k₁]? = l[j₁]? ∧
      (l.eraseIdx j₁).eraseIdx k₂ = (l.eraseIdx j₂).eraseIdx k₁ := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨j₁, j₂ - 1, ?_, ?_, ?_⟩
    · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]
    · rw [List.getElem?_eraseIdx_of_lt hlt]
    · exact (dropA_eraseIdx_swap l j₁ j₂ hlt).symm
  · refine ⟨j₁ - 1, j₂, ?_, ?_, ?_⟩
    · rw [List.getElem?_eraseIdx_of_lt hgt]
    · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]
    · exact dropA_eraseIdx_swap l j₂ j₁ hgt

/-- Togliere un elemento da `queue_pc` non crea grant in volo. -/
theorem dropA_grantInFlight_eraseIdx {c : CacheState} {j : Nat} (hg : ¬ grantInFlight c) :
    ¬ grantInFlight { c with queue_pc := c.queue_pc.eraseIdx j } := by
  intro h
  apply hg
  rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨v, List.mem_of_mem_eraseIdx hv⟩
  · exact Or.inr ⟨v, List.mem_of_mem_eraseIdx hv⟩

/-! ## Scarto × scarto -/

/-- Due scarti di `rqIμ`. Cache diverse: quadrato (primo disgiunto). Stessa cache e stessa posizione:
lo stesso messaggio è tolto, `s' = s''` (secondo disgiunto). Stessa cache e posizioni diverse:
quadrato, ciascun lato toglie l'altro `rqIμ` nella posizione riaggiustata (`dropA_two_pos`). -/
theorem peak_drop_rqIμ_drop_rqIμ {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .drop_rqIμ i₂) s'') :
    DecJoin 0 0 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | drop_rqIμ j₂ hj₂ _ =>
        by_cases hj : j₁ = j₂
        · subst hj; exact Or.inr (Or.inl rfl)
        · obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
          refine Or.inl (DecJoin.square
            (step_int.cache _ _ i₁ .drop_rqIμ (cache_step.drop_rqIμ _ k₂ ?_ ?_))
            (dropA_step_int_congr
              (step_int.cache _ _ i₁ .drop_rqIμ (cache_step.drop_rqIμ _ k₁ ?_ ?_)) ?_) rfl rfl)
          · simp only [update_Fin_gss, hk₂, hj₂]
          · simpa only [update_Fin_gss] using hI
          · simp only [update_Fin_gss, hk₁, hj₁]
          · simpa only [update_Fin_gss] using hI
          · simp only [update_Fin_gss, update_Fin_update_Fin_same, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e scarto di `rqIσ`. Cache diverse: quadrato. Stessa cache: le due posizioni
sono necessariamente diverse (contengono messaggi diversi), quadrato con gli indici riaggiustati
(primo disgiunto in ogni caso). -/
theorem peak_drop_rqIμ_drop_rqIσ {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .drop_rqIσ i₂) s'') :
    DecJoin 0 0 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | drop_rqIσ j₂ hj₂ _ =>
        have hj : j₁ ≠ j₂ := by rintro rfl; rw [hj₁] at hj₂; cases hj₂
        obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
        refine Or.inl (DecJoin.square
          (step_int.cache _ _ i₁ .drop_rqIσ (cache_step.drop_rqIσ _ k₂ ?_ ?_))
          (dropA_step_int_congr
            (step_int.cache _ _ i₁ .drop_rqIμ (cache_step.drop_rqIμ _ k₁ ?_ ?_)) ?_) rfl rfl)
        · simp only [update_Fin_gss, hk₂, hj₂]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, hk₁, hj₁]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, update_Fin_update_Fin_same, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Due scarti di `rqIσ`. Cache diverse: quadrato. Stessa cache e stessa posizione: `s' = s''`.
Stessa cache e posizioni diverse: quadrato con gli indici riaggiustati. -/
theorem peak_drop_rqIσ_drop_rqIσ {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .drop_rqIσ i₂) s'') :
    DecJoin 0 0 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | drop_rqIσ j₂ hj₂ _ =>
        by_cases hj : j₁ = j₂
        · subst hj; exact Or.inr (Or.inl rfl)
        · obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
          refine Or.inl (DecJoin.square
            (step_int.cache _ _ i₁ .drop_rqIσ (cache_step.drop_rqIσ _ k₂ ?_ ?_))
            (dropA_step_int_congr
              (step_int.cache _ _ i₁ .drop_rqIσ (cache_step.drop_rqIσ _ k₁ ?_ ?_)) ?_) rfl rfl)
          · simp only [update_Fin_gss, hk₂, hj₂]
          · simpa only [update_Fin_gss] using hI
          · simp only [update_Fin_gss, hk₁, hj₁]
          · simpa only [update_Fin_gss] using hI
          · simp only [update_Fin_gss, update_Fin_update_Fin_same, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-! ## Scarto di `rqIμ` × evento di cache -/

/-- Scarto di `rqIμ` e rilascio spontaneo da `M`. Cache diverse: quadrato. Stessa cache: picco
vuoto, lo scarto vuole la cache in `I` e il rilascio in `M`. -/
theorem peak_drop_rqIμ_rq_data_not_available {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | rq_data_not_available hM => cases hI.symm.trans hM
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e rilascio spontaneo da `S`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `S`). -/
theorem peak_drop_rqIμ_ld_rq_data_not_availableS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | rq_data_not_available1 hS => cases hI.symm.trans hS
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e richiesta di `M`. Cache diverse: quadrato. Stessa cache: quadrato, la
richiesta accoda `rqM` in `queue_cp` e lo scarto toglie da `queue_pc`; dopo lo scarto la cache è
ancora in `I`, senza richieste in sospeso, senza grant in volo (`dropA_grantInFlight_eraseIdx`) e con
la stessa store in testa. -/
theorem peak_drop_rqIμ_upgrade_from_I_rq {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 0 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rq _ hp hg hw =>
        refine Or.inl (DecJoin.square
          (step_int.cache _ _ i₁ .upgrade_from_I_rq (cache_step.upgrade_from_I_rq _ ?_ ?_ ?_ ?_))
          (dropA_step_int_congr
            (step_int.cache _ _ i₁ .drop_rqIμ (cache_step.drop_rqIμ _ j₁ ?_ ?_)) ?_) rfl rfl)
        · simpa only [update_Fin_gss] using hI
        · simpa only [update_Fin_gss, pending] using hp
        · simp only [update_Fin_gss]; exact dropA_grantInFlight_eraseIdx hg
        · simpa only [update_Fin_gss, wantsM] using hw
        · simpa only [update_Fin_gss] using hj₁
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, update_Fin_update_Fin_same]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e richiesta di `S`. Cache diverse: quadrato. Stessa cache: quadrato, come per
la richiesta di `M` (la guardia della richiesta sopravvive allo scarto). -/
theorem peak_drop_rqIμ_upgrade_from_I_rqS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 0 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rq1 _ hp hg hw =>
        refine Or.inl (DecJoin.square
          (step_int.cache _ _ i₁ .upgrade_from_I_rqS (cache_step.upgrade_from_I_rq1 _ ?_ ?_ ?_ ?_))
          (dropA_step_int_congr
            (step_int.cache _ _ i₁ .drop_rqIμ (cache_step.drop_rqIμ _ j₁ ?_ ?_)) ?_) rfl rfl)
        · simpa only [update_Fin_gss] using hI
        · simpa only [update_Fin_gss, pending] using hp
        · simp only [update_Fin_gss]; exact dropA_grantInFlight_eraseIdx hg
        · simpa only [update_Fin_gss, wantsS] using hw
        · simpa only [update_Fin_gss] using hj₁
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, update_Fin_update_Fin_same]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e presa del grant di `M`. Cache diverse: quadrato. Stessa cache
(`DecJoin.mix`, `0 < 3`): da `s'` la presa nella posizione riaggiustata (`= 3`), poi rilascio
spontaneo da `M` (`2`) e consumo dell'`rsIμ v` al parent (`1`); da `s''` (in `M` con l'`rqIμ`
stantio) l'onore dell'invalidate (`2`) e lo stesso consumo (`1`). I due lati finiscono nello
stesso stato: cache in `I` con valore `v`, `queue_pc` doppiamente cancellata, riga `I` e valore
`v` al parent. -/
theorem peak_drop_rqIμ_upgrade_from_I_rs {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 0 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rs _ j₂ hj₂ _ =>
        have hj : j₁ ≠ j₂ := by rintro rfl; rw [hj₁] at hj₂; cases hj₂
        obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
        refine Or.inl (DecJoin.mix (by decide)
          (Or.inr (lstep_of' (step_int.cache _ _ i₁ (.upgrade_from_I_rs v)
            (cache_step.upgrade_from_I_rs _ v k₂ ?_ ?_)) rfl))
          (ltStar_cons (step_int.cache _ _ i₁ .rq_data_not_available
              (cache_step.rq_data_not_available _ ?_)) (by simp [lab])
            (ltStar_single (step_int.parent_upd_queue _ _ (.downgrade_from_M_rq1 v) i₁
              (parent_msi_step.downgrade_from_M_rq1 _ v i₁ (s.caches i₁).queue_cp.length ?_))
              (by simp [lab])))
          (ltStar_cons (step_int.cache _ _ i₁ .downgrade_from_M_rs
              (cache_step.downgrade_from_M_rs _ k₁ ?_ ?_)) (by simp [lab])
            (ltStar_single (dropA_step_int_congr
              (step_int.parent_upd_queue _ _ (.downgrade_from_M_rq1 v) i₁
                (parent_msi_step.downgrade_from_M_rq1 _ v i₁ (s.caches i₁).queue_cp.length ?_)) ?_)
              (by simp [lab]))))
        · simp only [update_Fin_gss, hk₂, hj₂]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, hk₁, hj₁]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, update_Fin_update_Fin_same, lst_erase, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e presa del grant di `S`. Cache diverse: quadrato. Stessa cache
(`DecJoin.mix`, `0 < 3`): da `s'` la presa di `S` (`= 3`), poi rilascio spontaneo da `S` (`2`) e
consumo dell'`rsIσ` al parent (`1`); da `s''` (in `S` con l'`rqIμ` stantio, che in `S` non si può
onorare) rilascio spontaneo da `S` (`2`), scarto dell'`rqIμ` (`0`) e consumo (`1`). Stesso stato
finale: cache in `I` con valore `v`, `queue_pc` doppiamente cancellata, riga `I` al parent. -/
theorem peak_drop_rqIμ_upgrade_from_I_rsS {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 0 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rsS _ j₂ hj₂ _ =>
        have hj : j₁ ≠ j₂ := by rintro rfl; rw [hj₁] at hj₂; cases hj₂
        obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
        refine Or.inl (DecJoin.mix (by decide)
          (Or.inr (lstep_of' (step_int.cache _ _ i₁ (.upgrade_from_I_rsS v)
            (cache_step.upgrade_from_I_rsS _ v k₂ ?_ ?_)) rfl))
          (ltStar_cons (step_int.cache _ _ i₁ .ld_rq_data_not_availableS
              (cache_step.rq_data_not_available1 _ ?_)) (by simp [lab])
            (ltStar_single (step_int.parent_upd_queue _ _ .downgrade_from_S_rq1S i₁
              (parent_msi_step.downgrade_from_M_rq2 _ i₁ (s.caches i₁).queue_cp.length ?_))
              (by simp [lab])))
          (ltStar_cons (step_int.cache _ _ i₁ .ld_rq_data_not_availableS
              (cache_step.rq_data_not_available1 _ ?_)) (by simp [lab])
            (ltStar_cons (step_int.cache _ _ i₁ .drop_rqIμ
                (cache_step.drop_rqIμ _ k₁ ?_ ?_)) (by simp [lab])
              (ltStar_single (dropA_step_int_congr
                (step_int.parent_upd_queue _ _ .downgrade_from_S_rq1S i₁
                  (parent_msi_step.downgrade_from_M_rq2 _ i₁ (s.caches i₁).queue_cp.length ?_)) ?_)
                (by simp [lab])))))
        · simp only [update_Fin_gss, hk₂, hj₂]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, hk₁, hj₁]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, update_Fin_update_Fin_same, lst_erase, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e onore di un invalidate in `M`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `M`). -/
theorem peak_drop_rqIμ_downgrade_from_M_rs {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | downgrade_from_M_rs j₂ hj₂ hM => cases hI.symm.trans hM
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIμ` e onore di un invalidate in `S`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `S`). -/
theorem peak_drop_rqIμ_downgrade_from_S_rsS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIμ j₁ hj₁ hI =>
      cases hc₂ with
      | downgrade_from_M_rs1 j₂ hj₂ hS => cases hI.symm.trans hS
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-! ## Scarto di `rqIσ` × evento di cache -/

/-- Scarto di `rqIσ` e rilascio spontaneo da `M`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `M`). -/
theorem peak_drop_rqIσ_rq_data_not_available {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .rq_data_not_available i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | rq_data_not_available hM => cases hI.symm.trans hM
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e rilascio spontaneo da `S`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `S`). -/
theorem peak_drop_rqIσ_ld_rq_data_not_availableS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .ld_rq_data_not_availableS i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | rq_data_not_available1 hS => cases hI.symm.trans hS
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e richiesta di `M`. Cache diverse: quadrato. Stessa cache: quadrato, la guardia
della richiesta sopravvive allo scarto (togliere un `rqIσ` non crea grant in volo). -/
theorem peak_drop_rqIσ_upgrade_from_I_rq {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 0 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rq _ hp hg hw =>
        refine Or.inl (DecJoin.square
          (step_int.cache _ _ i₁ .upgrade_from_I_rq (cache_step.upgrade_from_I_rq _ ?_ ?_ ?_ ?_))
          (dropA_step_int_congr
            (step_int.cache _ _ i₁ .drop_rqIσ (cache_step.drop_rqIσ _ j₁ ?_ ?_)) ?_) rfl rfl)
        · simpa only [update_Fin_gss] using hI
        · simpa only [update_Fin_gss, pending] using hp
        · simp only [update_Fin_gss]; exact dropA_grantInFlight_eraseIdx hg
        · simpa only [update_Fin_gss, wantsM] using hw
        · simpa only [update_Fin_gss] using hj₁
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, update_Fin_update_Fin_same]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e richiesta di `S`. Cache diverse: quadrato. Stessa cache: quadrato, come per
la richiesta di `M`. -/
theorem peak_drop_rqIσ_upgrade_from_I_rqS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 0 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rq1 _ hp hg hw =>
        refine Or.inl (DecJoin.square
          (step_int.cache _ _ i₁ .upgrade_from_I_rqS (cache_step.upgrade_from_I_rq1 _ ?_ ?_ ?_ ?_))
          (dropA_step_int_congr
            (step_int.cache _ _ i₁ .drop_rqIσ (cache_step.drop_rqIσ _ j₁ ?_ ?_)) ?_) rfl rfl)
        · simpa only [update_Fin_gss] using hI
        · simpa only [update_Fin_gss, pending] using hp
        · simp only [update_Fin_gss]; exact dropA_grantInFlight_eraseIdx hg
        · simpa only [update_Fin_gss, wantsS] using hw
        · simpa only [update_Fin_gss] using hj₁
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss, update_Fin_update_Fin_same]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e presa del grant di `M`. Cache diverse: quadrato. Stessa cache
(`DecJoin.mix`, `0 < 3`): da `s'` la presa di `M` (`= 3`), poi rilascio spontaneo da `M` (`2`) e
consumo dell'`rsIμ v` al parent (`1`); da `s''` (in `M` con l'`rqIσ` stantio, che in `M` non si può
onorare) rilascio spontaneo da `M` (`2`), scarto dell'`rqIσ` (`0`) e consumo (`1`). Stesso stato
finale: cache in `I` con valore `v`, `queue_pc` doppiamente cancellata, riga `I` e valore `v` al
parent. -/
theorem peak_drop_rqIσ_upgrade_from_I_rs {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rs v) i₂) s'') :
    DecJoin 0 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rs _ j₂ hj₂ _ =>
        have hj : j₁ ≠ j₂ := by rintro rfl; rw [hj₁] at hj₂; cases hj₂
        obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
        refine Or.inl (DecJoin.mix (by decide)
          (Or.inr (lstep_of' (step_int.cache _ _ i₁ (.upgrade_from_I_rs v)
            (cache_step.upgrade_from_I_rs _ v k₂ ?_ ?_)) rfl))
          (ltStar_cons (step_int.cache _ _ i₁ .rq_data_not_available
              (cache_step.rq_data_not_available _ ?_)) (by simp [lab])
            (ltStar_single (step_int.parent_upd_queue _ _ (.downgrade_from_M_rq1 v) i₁
              (parent_msi_step.downgrade_from_M_rq1 _ v i₁ (s.caches i₁).queue_cp.length ?_))
              (by simp [lab])))
          (ltStar_cons (step_int.cache _ _ i₁ .rq_data_not_available
              (cache_step.rq_data_not_available _ ?_)) (by simp [lab])
            (ltStar_cons (step_int.cache _ _ i₁ .drop_rqIσ
                (cache_step.drop_rqIσ _ k₁ ?_ ?_)) (by simp [lab])
              (ltStar_single (dropA_step_int_congr
                (step_int.parent_upd_queue _ _ (.downgrade_from_M_rq1 v) i₁
                  (parent_msi_step.downgrade_from_M_rq1 _ v i₁ (s.caches i₁).queue_cp.length ?_)) ?_)
                (by simp [lab])))))
        · simp only [update_Fin_gss, hk₂, hj₂]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, hk₁, hj₁]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, update_Fin_update_Fin_same, lst_erase, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e presa del grant di `S`. Cache diverse: quadrato. Stessa cache
(`DecJoin.mix`, `0 < 3`): da `s'` la presa di `S` nella posizione riaggiustata (`= 3`), poi rilascio
spontaneo da `S` (`2`) e consumo dell'`rsIσ` al parent (`1`); da `s''` (in `S` con l'`rqIσ` stantio)
l'onore dell'invalidate (`2`) e lo stesso consumo (`1`). Stesso stato finale: cache in `I` con
valore `v`, `queue_pc` doppiamente cancellata, riga `I` al parent. -/
theorem peak_drop_rqIσ_upgrade_from_I_rsS {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache (.upgrade_from_I_rsS v) i₂) s'') :
    DecJoin 0 3 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | upgrade_from_I_rsS _ j₂ hj₂ _ =>
        have hj : j₁ ≠ j₂ := by rintro rfl; rw [hj₁] at hj₂; cases hj₂
        obtain ⟨k₁, k₂, hk₂, hk₁, hL⟩ := dropA_two_pos (s.caches i₁).queue_pc hj
        refine Or.inl (DecJoin.mix (by decide)
          (Or.inr (lstep_of' (step_int.cache _ _ i₁ (.upgrade_from_I_rsS v)
            (cache_step.upgrade_from_I_rsS _ v k₂ ?_ ?_)) rfl))
          (ltStar_cons (step_int.cache _ _ i₁ .ld_rq_data_not_availableS
              (cache_step.rq_data_not_available1 _ ?_)) (by simp [lab])
            (ltStar_single (step_int.parent_upd_queue _ _ .downgrade_from_S_rq1S i₁
              (parent_msi_step.downgrade_from_M_rq2 _ i₁ (s.caches i₁).queue_cp.length ?_))
              (by simp [lab])))
          (ltStar_cons (step_int.cache _ _ i₁ .downgrade_from_S_rsS
              (cache_step.downgrade_from_M_rs1 _ k₁ ?_ ?_)) (by simp [lab])
            (ltStar_single (dropA_step_int_congr
              (step_int.parent_upd_queue _ _ .downgrade_from_S_rq1S i₁
                (parent_msi_step.downgrade_from_M_rq2 _ i₁ (s.caches i₁).queue_cp.length ?_)) ?_)
              (by simp [lab]))))
        · simp only [update_Fin_gss, hk₂, hj₂]
        · simpa only [update_Fin_gss] using hI
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, hk₁, hj₁]
        · simp only [update_Fin_gss]
        · simp only [update_Fin_gss, lst_get]
        · simp only [update_Fin_gss, update_Fin_update_Fin_same, lst_erase, hL]
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e onore di un invalidate in `M`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `M`). -/
theorem peak_drop_rqIσ_downgrade_from_M_rs {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .downgrade_from_M_rs i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | downgrade_from_M_rs j₂ hj₂ hM => cases hI.symm.trans hM
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

/-- Scarto di `rqIσ` e onore di un invalidate in `S`. Cache diverse: quadrato. Stessa cache: picco
vuoto (`I` contro `S`). -/
theorem peak_drop_rqIσ_downgrade_from_S_rsS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i₂) s'') :
    DecJoin 0 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := dropA_cache_inv h1
    obtain ⟨c₂, hc₂, rfl⟩ := dropA_cache_inv h2
    cases hc₁ with
    | drop_rqIσ j₁ hj₁ hI =>
      cases hc₂ with
      | downgrade_from_M_rs1 j₂ hj₂ hS => cases hI.symm.trans hS
  · obtain ⟨d, hb, hc⟩ := dropA_cache_cache_ne hii h1 h2
    exact Or.inl (DecJoin.square hb hc rfl rfl)

end MSITrial
