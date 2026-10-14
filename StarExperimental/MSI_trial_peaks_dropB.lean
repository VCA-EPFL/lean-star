import StarExperimental.MSI_trial_dec

/-!
# `MSI_trial`: picchi scarto–parent

I 14 picchi fra uno scarto (`drop_rqIμ`, `drop_rqIσ`, etichetta 0) della cache `i₁` e una regola del
parent sull'indice `i₂` (consumi, etichetta 1; grant, etichetta 4; invalidate, etichetta 6).
Sono tutti quadrati (`DecJoin.square`): i due passi commutano.

* `i₁ ≠ i₂`: lo scarto tocca la cache `i₁` e la copia `queue_pci i₁`; il passo del parent tocca le code
  della cache `i₂`, la riga `i₂`, `queue_cip i₂`/`queue_pci i₂` e il valore. Parti indipendenti.
* `i₁ = i₂`: il passo del parent riscrive `queue_pc i₁` con la copia `queue_pci i₁` (un append per grant
  e invalidate, nessun cambiamento per i consumi), lo scarto cancella la posizione `j`. Con le code
  allineate (`synced s`) cancellare `j` e accodare in fondo commutano (`List.eraseIdx_append_of_lt_length`),
  e la posizione `j` tiene ancora lo stesso messaggio dopo l'append (`List.getElem?_append_left`).

Senza `synced s` si esce con `¬ Reach s` (`not_reach_of_not_synced`). Il lavoro è fatto una volta sola
nel lemma `drop_parent_join`, generico nell'evento del parent (così sono coperti insieme i due
costruttori `upgrade_to_M_invalid_all`/`upgrade_to_M_invalid_all3` dello stesso evento); i 14 teoremi
sono corollari.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Lemmi ausiliari -/

theorem update_Fin_self {α : Type} (i : Fin n) (f : Fin n → α) : update_Fin i (f i) f = f := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hk]

/-- Cancellare la posizione `j` della lista all'indice `i₁` e accodare `m` all'indice `i₂` commutano
(se `j` è una posizione valida). -/
theorem update_erase_append {α : Type} {f : Fin n → List α} {i₁ i₂ : Fin n} {j : Nat} {m : α}
    (hj : j < (f i₁).length) :
    update_Fin i₂ (update_Fin i₁ ((f i₁).eraseIdx j) f i₂ ++ [m]) (update_Fin i₁ ((f i₁).eraseIdx j) f)
    = update_Fin i₁ ((update_Fin i₂ (f i₂ ++ [m]) f i₁).eraseIdx j) (update_Fin i₂ (f i₂ ++ [m]) f) := by
  funext k
  by_cases h12 : i₁ = i₂
  · subst h12
    by_cases hk : k = i₁
    · subst hk
      simp only [update_Fin_gss]
      exact (List.eraseIdx_append_of_lt_length hj _).symm
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  · by_cases hk1 : k = i₁
    · subst hk1
      simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ h12]
    · by_cases hk2 : k = i₂
      · subst hk2
        have h21 : ¬ k = i₁ := hk1
        simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ h21]
      · simp only [update_Fin_gso2 _ _ _ _ hk1, update_Fin_gso2 _ _ _ _ hk2]

theorem step_int_congr {a b c : MSIState n} {e : IEvent n} (h : step_int a e b) (heq : b = c) :
    step_int a e c := heq ▸ h

theorem parent_msi_step_src {p p' q : ParentState n} {e : ParentInternalEvent n}
    (h : parent_msi_step p e q) (heq : p = p') : parent_msi_step p' e q := heq ▸ h

/-! ## Gli scarti -/

/-- `ce` è lo scarto del messaggio `m`. -/
def IsDropOf (ce : CEvent) (m : PCEvent) : Prop :=
  (ce = .drop_rqIμ ∧ m = .rqIμ) ∨ (ce = .drop_rqIσ ∧ m = .rqIσ)

theorem drop_step {c : CacheState} {ce : CEvent} {m : PCEvent} (j : Nat) (hcm : IsDropOf ce m)
    (hj : c.queue_pc[j]? = some m) (hI : c.state = .I) :
    cache_step c ce { c with queue_pc := c.queue_pc.eraseIdx j } := by
  rcases hcm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cache_step.drop_rqIμ _ j hj hI
  · exact cache_step.drop_rqIσ _ j hj hI

theorem drop_inv {c c' : CacheState} {ce : CEvent} (hc : cache_step c ce c')
    (hd : ce = .drop_rqIμ ∨ ce = .drop_rqIσ) :
    ∃ (j : Nat) (m : PCEvent), IsDropOf ce m ∧ c.queue_pc[j]? = some m ∧ c.state = .I
      ∧ c' = { c with queue_pc := c.queue_pc.eraseIdx j } := by
  rcases hd with rfl | rfl
  · cases hc with
    | drop_rqIμ j hj hI => exact ⟨j, _, Or.inl ⟨rfl, rfl⟩, hj, hI, rfl⟩
  · cases hc with
    | drop_rqIσ j hj hI => exact ⟨j, _, Or.inr ⟨rfl, rfl⟩, hj, hI, rfl⟩

/-! ## Il parent dopo uno scarto -/

/-- Il parent con la posizione `j` di `queue_pci i` cancellata: è `s'.parent` dopo uno scarto della
cache `i` quando le code sono allineate. -/
def pdrop (p : ParentState n) (i : Fin n) (j : Nat) : ParentState n :=
  { p with queue_pci := update_Fin i ((p.queue_pci i).eraseIdx j) p.queue_pci }

/-- Le regole del parent non guardano `queue_pci`: si applicano ancora dopo uno scarto, con lo stesso
risultato a meno dello scarto. -/
theorem parent_step_pdrop {p p' : ParentState n} {e : ParentUpdQueueInternalEvent n} {i₂ i₁ : Fin n}
    {j : Nat} (hp : parent_msi_step p (.upd_queue e i₂) p') (hj : j < (p.queue_pci i₁).length) :
    parent_msi_step (pdrop p i₁ j) (.upd_queue e i₂) (pdrop p' i₁ j) := by
  cases hp with
  | downgrade_from_M_rq1 _ _ k hk =>
      exact parent_msi_step.downgrade_from_M_rq1 _ _ _ k hk
  | downgrade_from_M_rq2 _ k hk =>
      exact parent_msi_step.downgrade_from_M_rq2 _ _ k hk
  | upgrade_to_M_data_avilable_rq1 _ k hk hall =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ _ k hk hall) ?_
      simp only [pdrop, update_erase_append hj]
  | upgrade_to_M_data_avilable_rq2 _ k hk hI hall =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ _ k hk hI hall) ?_
      simp only [pdrop, update_erase_append hj]
  | upgrade_to_M_invalid_all _ _ k hk hM =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_invalid_all _ _ _ k hk hM) ?_
      simp only [pdrop, update_erase_append hj]
  | upgrade_to_M_invalid_all1 _ _ k hk hS =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_invalid_all1 _ _ _ k hk hS) ?_
      simp only [pdrop, update_erase_append hj]
  | upgrade_to_M_invalid_all2 _ _ k hk hne hS =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_invalid_all2 _ _ _ k hk hne hS) ?_
      simp only [pdrop, update_erase_append hj]
  | upgrade_to_M_invalid_all3 _ _ k hk hM =>
      refine parent_msi_step_congr (parent_msi_step.upgrade_to_M_invalid_all3 _ _ _ k hk hM) ?_
      simp only [pdrop, update_erase_append hj]

/-- Un passo del parent sull'indice `i` lascia `queue_pci i` com'è o vi accoda un messaggio. -/
theorem parent_step_pci {p p' : ParentState n} {e : ParentUpdQueueInternalEvent n} {i : Fin n}
    (hp : parent_msi_step p (.upd_queue e i) p') :
    p'.queue_pci i = p.queue_pci i ∨ ∃ m, p'.queue_pci i = p.queue_pci i ++ [m] := by
  cases hp
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, update_Fin_gss _ _ _⟩

/-! ## Il lemma generale -/

/-- Uno scarto della cache `i₁` e una regola del parent sull'indice `i₂` commutano (code allineate). -/
theorem drop_parent_join {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {ce : CEvent}
    {e : ParentUpdQueueInternalEvent n} (hs : synced s)
    (h1 : step_int s (.cache ce i₁) s') (hd : ce = .drop_rqIμ ∨ ce = .drop_rqIσ)
    (h2 : step_int s (.parent e i₂) s'') :
    ∃ d, step_int s'' (.cache ce i₁) d ∧ step_int s' (.parent e i₂) d := by
  cases h1 with
  | cache c' _ _ hc =>
  obtain ⟨j, m, hdm, hj, hI, rfl⟩ := drop_inv hc hd
  cases h2 with
  | parent_upd_queue p' _ _ hp =>
  obtain ⟨hcip, hpci⟩ := hs i₁
  have hj' : (s.parent.queue_pci i₁)[j]? = some m := by rw [hpci]; exact hj
  have hjl : j < (s.parent.queue_pci i₁).length := (List.getElem?_eq_some_iff.mp hj').1
  have hp' : parent_msi_step (pdrop s.parent i₁ j) (.upd_queue e i₂) (pdrop p' i₁ j) :=
    parent_step_pdrop hp hjl
  -- `s'.parent` è `pdrop s.parent i₁ j`
  have hsp : pdrop s.parent i₁ j =
      ({ s.parent with queue_cip := update_Fin i₁ (s.caches i₁).queue_cp s.parent.queue_cip,
                       queue_pci := update_Fin i₁ ((s.caches i₁).queue_pc.eraseIdx j) s.parent.queue_pci }
        : ParentState n) := by
    simp only [pdrop, ← hcip, ← hpci, update_Fin_self]
  by_cases h12 : i₁ = i₂
  · subst h12
    refine ⟨_, step_int.cache _ _ _ _ (drop_step j hdm ?_ ?_),
      step_int_congr (step_int.parent_upd_queue _ (pdrop p' i₁ j) e i₁ (parent_msi_step_src hp' hsp)) ?_⟩
    · simp only [update_Fin_gss]
      rcases parent_step_pci hp with h | ⟨m', h⟩
      · rw [h]; exact hj'
      · rw [h, List.getElem?_append_left hjl]; exact hj'
    · simp only [update_Fin_gss]; exact hI
    · refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [pdrop, update_Fin_gss]
        · simp only [update_Fin_gso2 _ _ _ _ hk]
      · rfl
      · intro k; rfl
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [pdrop, update_Fin_gss]
        · simp only [pdrop, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [pdrop, update_Fin_gss]
        · simp only [pdrop, update_Fin_gso2 _ _ _ _ hk]
  · have h21 : ¬ i₂ = i₁ := fun h => h12 h.symm
    obtain ⟨hl1, hl2, _⟩ := parent_step_local hp i₁ h12
    refine ⟨_, step_int.cache _ _ _ _ (drop_step j hdm ?_ ?_),
      step_int_congr (step_int.parent_upd_queue _ (pdrop p' i₁ j) e i₂ (parent_msi_step_src hp' hsp)) ?_⟩
    · simp only [update_Fin_gso2 _ _ _ _ h12]; exact hj
    · simp only [update_Fin_gso2 _ _ _ _ h12]; exact hI
    · refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk1 : k = i₁
        · subst hk1
          simp only [pdrop, update_Fin_gss, update_Fin_gso2 _ _ _ _ h12]
        · by_cases hk2 : k = i₂
          · subst hk2
            simp only [pdrop, update_Fin_gss, update_Fin_gso2 _ _ _ _ h21]
          · simp only [update_Fin_gso2 _ _ _ _ hk1, update_Fin_gso2 _ _ _ _ hk2]
      · rfl
      · intro k; rfl
      · intro k
        by_cases hk : k = i₁
        · subst hk
          simp only [pdrop, update_Fin_gss, update_Fin_gso2 _ _ _ _ h12, hl1, hcip]
        · simp only [pdrop, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i₁
        · subst hk
          simp only [pdrop, update_Fin_gss, update_Fin_gso2 _ _ _ _ h12, hl2, hpci]
        · simp only [pdrop, update_Fin_gso2 _ _ _ _ hk]


/-! ## `drop_rqIμ` contro le regole del parent -/

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il consumo del parent `downgrade_from_M_rq1 v` su `i₂` (consuma un `rsIμ v` in `queue_cip i₂`, riga
`i₂ := I`; etichetta 1). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁`
con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale
append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto).
Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_downgrade_from_M_rq1 {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent (.downgrade_from_M_rq1 v) i₂) s'') :
    DecJoin 0 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il consumo del parent `downgrade_from_S_rq1S` su `i₂` (consuma un `rsIσ` in `queue_cip i₂`, riga `i₂
:= I`; etichetta 1). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁`
con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale
append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto).
Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_downgrade_from_S_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent .downgrade_from_S_rq1S i₂) s'') :
    DecJoin 0 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il grant di `M` `upgrade_to_M_data_avilable_rq1` su `i₂` (consuma un `rqM`, riga `i₂ := M`, accoda
`rsM` in `queue_pci i₂`; etichetta 4). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₂) s'') :
    DecJoin 0 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il grant di `S` `upgrade_to_S_data_avilable_rq1S` su `i₂` (consuma un `rqS`, riga `i₂ := S`, accoda
`rsS` in `queue_pci i₂`; etichetta 4). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 0 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `upgrade_to_M_invalid_all k` su `i₂` (riga `i₂ = M`, una richiesta `rqM` o `rqS` di `k`
pendente: entrambi i costruttori `upgrade_to_M_invalid_all`/`upgrade_to_M_invalid_all3`; accoda
`rqIμ` in `queue_pci i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_upgrade_to_M_invalid_all {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {k : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `invalid_allS` su `i₂` (riga `i₂ = S`, un `rqM` pendente; accoda `rqIσ` in `queue_pci
i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁` con la
copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale append in
fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto). Il secondo
disgiunto non serve mai. -/
theorem peak_drop_rqIμ_invalid_allS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIμ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `upgrade_to_S_invalid_2_rq1S k` su `i₂` (riga `i₂ = S`, un `rqS` di `k ≠ i₂` pendente;
accoda `rqIσ` in `queue_pci i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo
disgiunto): con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del
parent riscrive `queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la
posizione `j` e l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬
Reach s` (terzo disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIμ_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {k : Fin n}
    (h1 : step_int s (.cache .drop_rqIμ i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inl rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))


/-! ## `drop_rqIσ` contro le regole del parent -/

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il consumo del parent `downgrade_from_M_rq1 v` su `i₂` (consuma un `rsIμ v` in `queue_cip i₂`, riga
`i₂ := I`; etichetta 1). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁`
con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale
append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto).
Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_downgrade_from_M_rq1 {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {v : Value}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent (.downgrade_from_M_rq1 v) i₂) s'') :
    DecJoin 0 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il consumo del parent `downgrade_from_S_rq1S` su `i₂` (consuma un `rsIσ` in `queue_cip i₂`, riga `i₂
:= I`; etichetta 1). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁`
con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale
append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto).
Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_downgrade_from_S_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent .downgrade_from_S_rq1S i₂) s'') :
    DecJoin 0 1 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il grant di `M` `upgrade_to_M_data_avilable_rq1` su `i₂` (consuma un `rqM`, riga `i₂ := M`, accoda
`rsM` in `queue_pci i₂`; etichetta 4). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₂) s'') :
    DecJoin 0 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
il grant di `S` `upgrade_to_S_data_avilable_rq1S` su `i₂` (consuma un `rqS`, riga `i₂ := S`, accoda
`rsS` in `queue_pci i₂`; etichetta 4). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 0 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `upgrade_to_M_invalid_all k` su `i₂` (riga `i₂ = M`, una richiesta `rqM` o `rqS` di `k`
pendente: entrambi i costruttori `upgrade_to_M_invalid_all`/`upgrade_to_M_invalid_all3`; accoda
`rqIμ` in `queue_pci i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive
`queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e
l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo
disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_upgrade_to_M_invalid_all {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {k : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `invalid_allS` su `i₂` (riga `i₂ = S`, un `rqM` pendente; accoda `rqIσ` in `queue_pci
i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo disgiunto): con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano; con `i₁ = i₂` il passo del parent riscrive `queue_pc i₁` con la
copia `queue_pci i₁` e, con le code allineate, cancellare la posizione `j` e l'eventuale append in
fondo commutano. Se le code non sono allineate si esce con `¬ Reach s` (terzo disgiunto). Il secondo
disgiunto non serve mai. -/
theorem peak_drop_rqIσ_invalid_allS {s s' s'' : MSIState n} {i₁ i₂ : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

/-- Scarto di un `rqIσ` stantio dalla cache `i₁` (in `I`, posizione `j` di `queue_pc i₁`; etichetta 0) e
l'invalidate `upgrade_to_S_invalid_2_rq1S k` su `i₂` (riga `i₂ = S`, un `rqS` di `k ≠ i₂` pendente;
accoda `rqIσ` in `queue_pci i₂`; etichetta 6). Sempre un quadrato (`DecJoin.square`, primo
disgiunto): con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano; con `i₁ = i₂` il passo del
parent riscrive `queue_pc i₁` con la copia `queue_pci i₁` e, con le code allineate, cancellare la
posizione `j` e l'eventuale append in fondo commutano. Se le code non sono allineate si esce con `¬
Reach s` (terzo disgiunto). Il secondo disgiunto non serve mai. -/
theorem peak_drop_rqIσ_upgrade_to_S_invalid_2_rq1S {s s' s'' : MSIState n} {i₁ i₂ : Fin n} {k : Fin n}
    (h1 : step_int s (.cache .drop_rqIσ i₁) s') (h2 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₂) s'') :
    DecJoin 0 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  · obtain ⟨d, hd1, hd2⟩ := drop_parent_join hs h1 (Or.inr rfl) h2
    exact Or.inl (DecJoin.square hd2 hd1 rfl rfl)
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))

end MSITrial
