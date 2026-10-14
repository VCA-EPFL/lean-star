import StarExperimental.MSI

/-! # `a`: l'insieme `A` degli stati in cui i 18 teoremi di commutazione non convergono

Dei 185 teoremi `comm_*` di `MSI.lean`, 18 hanno un caso in cui i due passi non si
ricongiungono e la dimostrazione esce con `¬ MSI.reachable s`. Per ognuno, lo stato `a` di
quel caso è descritto qui da un "vettore": ciò che impongono le guardie dei due passi
(`a → b` e `a → c`), più la condizione in più che rende il caso non convergente; tutti gli
altri campi dello stato sono liberi.

`A` è l'unione dei 18 vettori, un costruttore per teorema. Il teorema `A_unreachable` dice che
nessuno stato di `A` è raggiungibile: ogni vettore ha una vista in una delle 11 clausole di
`badView` usate dai 18 teoremi (1–7 sulla vista `(i, i)`, 10–13 sulla vista `(i, k)`).

Campi dello stato: cache `⟨state, value, queue_cp, queue_pc, extqueue⟩`, parent
`⟨value, shared_state, queue_cip, queue_pci⟩`. -/

open THEORY Relation BackwardGen MSIView

/-- **L'insieme `A`**: gli stati in cui uno dei 18 teoremi non converge. -/
inductive A {n : Nat} : MSIState n → Prop where
  -- ── Parent–parent: le guardie fissano solo il parent ──
  /-- 1. `downgrade_from_M_rq1 v` su `i₁` / `upgrade_to_M_data_avilable_rq1` su `i₂`.
  Bloccato sempre. Clausola 4. -/
  | t1 (s : MSIState n) (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value) :
      (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, s.parent.shared_state k = Bstate.I) →
      A s
  /-- 2. `downgrade_from_M_rq1 v` su `i₁` / `upgrade_to_M_data_avilable_rq2` su `i₂`.
  Bloccato sempre. Clausola 4. -/
  | t2 (s : MSIState n) (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value) :
      (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      s.parent.shared_state i₂ = Bstate.I →
      (∀ k, ¬(s.parent.shared_state k = Bstate.M)) →
      A s
  /-- 3. `downgrade_from_M_rq2` / `upgrade_to_M_data_avilable_rq1` sullo stesso indice `i`.
  Clausola 5. -/
  | t3 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) :
      (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (s.parent.queue_cip i)[j₂]? = some CPEvent.rqM →
      (∀ k, s.parent.shared_state k = Bstate.I) →
      A s
  /-- 4. `downgrade_from_M_rq2` / `upgrade_to_M_data_avilable_rq2` sullo stesso indice `i`,
  con la cache `i` non in `I`. Clausole 6, 7. -/
  | t4 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) :
      (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      s.parent.shared_state i = Bstate.I →
      (∀ k, ¬(s.parent.shared_state k = Bstate.M)) →
      ¬((s.caches i).state = Bstate.I) →
      A s
  /-- 5. `upgrade_to_M_data_avilable_rq1` su `i₁` e su `i₂`, con la cache del richiedente
  `i` (uno dei due) non in `I`. Clausole 6, 7. -/
  | t5 (s : MSIState n) (i₁ i₂ i : Fin n) (j₁ j₂ : Nat) :
      (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, s.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      ¬((s.caches i).state = Bstate.I) →
      A s
  /-- 6. `upgrade_to_M_data_avilable_rq1` su `i₁` / `upgrade_to_M_data_avilable_rq2` su `i₂`,
  con la cache del richiedente `i` (uno dei due) non in `I`. Clausole 6, 7. -/
  | t6 (s : MSIState n) (i₁ i₂ i : Fin n) (j₁ j₂ : Nat) :
      (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, s.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      ¬((s.caches i).state = Bstate.I) →
      A s
  /-- 7. `upgrade_to_M_data_avilable_rq2` due volte sullo stesso indice `i`, due `rqS` in
  posizioni diverse, con la cache `i` non in `I`. Clausole 6, 7. -/
  | t7 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) :
      j₁ ≠ j₂ →
      (s.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      s.parent.shared_state i = Bstate.I →
      (∀ k, ¬(s.parent.shared_state k = Bstate.M)) →
      ¬((s.caches i).state = Bstate.I) →
      A s
  -- ── Cache–cache, stessa cache `i`: le guardie fissano solo la cache ──
  /-- 8. `upgrade_from_I_rq` / `upgrade_from_I_rs v`, con la riga di un `k ≠ i` non a `I`.
  Clausola 12. -/
  | t8 (s : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (s.caches i).state = Bstate.I →
      ((s.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      i ≠ k →
      ¬(s.parent.shared_state k = Bstate.I) →
      A s
  /-- 9. `upgrade_from_I_rq1` / `upgrade_from_I_rsS v`, con `v = parent.value` e la riga di un
  `k ≠ i` a `M`. Clausola 13. -/
  | t9 (s : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (s.caches i).state = Bstate.I →
      ((s.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      v = s.parent.value →
      i ≠ k →
      s.parent.shared_state k = Bstate.M →
      A s
  /-- 10. `upgrade_from_I_rs v₁` / `upgrade_from_I_rs v₂`, due `rsM` in posizioni diverse.
  Clausola 1. -/
  | t10 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (s.caches i).state = Bstate.I →
      ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsM v₂) →
      j₁ ≠ j₂ →
      A s
  /-- 11. `upgrade_from_I_rs v₁` / `upgrade_from_I_rsS v₂`. Bloccato sempre. Clausola 3. -/
  | t11 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (s.caches i).state = Bstate.I →
      ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      A s
  /-- 12. `upgrade_from_I_rsS v₁` / `upgrade_from_I_rsS v₂`, due `rsS` in posizioni diverse.
  Clausola 2. -/
  | t12 (s : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (s.caches i).state = Bstate.I →
      ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsS v₁) →
      ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      j₁ ≠ j₂ →
      A s
  -- ── Esterno–interno, stessa cache `i`: le guardie fissano solo la cache ──
  /-- 13. `ld_rs` / `rq_data_not_available`: cache in `M` con una load pendente, e la riga di un
  `k ≠ i` non a `I`. Clausola 10. -/
  | t13 (s : MSIState n) (i k : Fin n) (rst : List Event) :
      (s.caches i).state = Bstate.M →
      (s.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      ¬(s.parent.shared_state k = Bstate.I) →
      A s
  /-- 14. `ld_rs` / `rq_data_not_available1`: cache in `S` con il valore del parent e una load
  pendente, e la riga di un `k ≠ i` a `M`. Clausola 11. -/
  | t14 (s : MSIState n) (i k : Fin n) (rst : List Event) :
      (s.caches i).state = Bstate.S →
      (s.caches i).extqueue.rq = Event.ld_rq :: rst →
      (s.caches i).value = s.parent.value →
      i ≠ k →
      s.parent.shared_state k = Bstate.M →
      A s
  /-- 15. `ld_rs` / `downgrade_from_M_rs`: cache in `M` con un `rqIμ` in coda e una load
  pendente, e la riga di un `k ≠ i` non a `I`. Clausola 10. -/
  | t15 (s : MSIState n) (i k : Fin n) (j : Nat) (rst : List Event) :
      (s.caches i).state = Bstate.M →
      ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (s.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      ¬(s.parent.shared_state k = Bstate.I) →
      A s
  /-- 16. `ld_rs` / `downgrade_from_M_rs1`: cache in `S` con il valore del parent, un `rqIσ` in
  coda e una load pendente, e la riga di un `k ≠ i` a `M`. Clausola 11. -/
  | t16 (s : MSIState n) (i k : Fin n) (j : Nat) (rst : List Event) :
      (s.caches i).state = Bstate.S →
      ((s.caches i).queue_pc)[j]? = some PCEvent.rqIσ →
      (s.caches i).extqueue.rq = Event.ld_rq :: rst →
      (s.caches i).value = s.parent.value →
      i ≠ k →
      s.parent.shared_state k = Bstate.M →
      A s
  /-- 17. `st_rs` / `rq_data_not_available`: cache in `M` con una store pendente, e la riga di
  un `k ≠ i` non a `I`. Clausola 10. -/
  | t17 (s : MSIState n) (i k : Fin n) (v : Value) (rst : List Event) :
      (s.caches i).state = Bstate.M →
      (s.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      ¬(s.parent.shared_state k = Bstate.I) →
      A s
  /-- 18. `st_rs` / `downgrade_from_M_rs`: cache in `M` con un `rqIμ` in coda e una store
  pendente, e la riga di un `k ≠ i` non a `I`. Clausola 10. -/
  | t18 (s : MSIState n) (i k : Fin n) (j : Nat) (v : Value) (rst : List Event) :
      (s.caches i).state = Bstate.M →
      ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (s.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      ¬(s.parent.shared_state k = Bstate.I) →
      A s

/-- Una cache non in `I` con la riga a `I` è irraggiungibile (clausola 6 se è in `M`, 7 se è
in `S`). -/
theorem not_reachable_of_notI_rowI {n} {s : MSIState n} {i : Fin n}
    (hc : ¬((s.caches i).state = Bstate.I)) (hI : s.parent.shared_state i = Bstate.I) :
    ¬ MSI.reachable s := by
  cases hst : (s.caches i).state with
  | M => exact not_reachable_of_M hst (Or.inr (Or.inr (by rw [hI]; intro h; cases h)))
  | S => exact not_reachable_of_S hst (Or.inr (Or.inr (by rw [hI]; intro h; cases h)))
  | I => exact absurd hst hc

/-- **Nessuno stato di `A` è raggiungibile.** Ogni vettore ha una vista cattiva; nei casi
cache–cache i messaggi sono letti dal lato cache, e `synced` li porta sul lato parent. -/
theorem A_unreachable {n} {s : MSIState n} (h : A s) : ¬ MSI.reachable s := by
  by_cases hsync : synced s
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | t1 i₁ i₂ j₁ j₂ v h₁ _ hall =>
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (by rw [hall i₁]; intro h; cases h)
  | t2 i₁ i₂ j₁ j₂ v h₁ _ _ hnoM =>
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (hnoM i₁)
  | t3 i j₁ j₂ h₁ _ hall =>
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ h₁) (by rw [hall i]; intro h; cases h)
  | t4 i j₁ j₂ _ _ hI _ hc => exact not_reachable_of_notI_rowI hc hI
  | t5 i₁ i₂ i j₁ j₂ _ _ hall _ hc => exact not_reachable_of_notI_rowI hc (hall i)
  | t6 i₁ i₂ i j₁ j₂ _ _ hall _ hc => exact not_reachable_of_notI_rowI hc (hall i)
  | t7 i j₁ j₂ _ _ _ hI _ hc => exact not_reachable_of_notI_rowI hc hI
  | t8 i k j v _ hj hne hk =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_rowJ hne (muMsgs_ne_zero_of_rsM hj) hk
  | t9 i k j v _ hj _ hne hk =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_rowM hne (sigMsgs_ne_zero_of_rsS hj) hk
  | t10 i j₁ j₂ v₁ v₂ _ hj₁ hj₂ hj =>
    rw [← (hsync i).2] at hj₁ hj₂
    have h2 := two_le_countP_of_ne isGrantM _ hj₁ hj₂ hj rfl rfl
    have hmu : 2 ≤ muMsgs s.parent i := by unfold muMsgs; omega
    exact not_reachable_of_two_mu hmu
  | t11 i j₁ j₂ v₁ v₂ _ hj₁ hj₂ =>
    rw [← (hsync i).2] at hj₁ hj₂
    exact not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsM hj₁) (sigMsgs_ne_zero_of_rsS hj₂)
  | t12 i j₁ j₂ v₁ v₂ _ hj₁ hj₂ hj =>
    rw [← (hsync i).2] at hj₁ hj₂
    have h2 := two_le_countP_of_ne isGrantS _ hj₁ hj₂ hj rfl rfl
    have hsig : 2 ≤ sigMsgs s.parent i := by unfold sigMsgs; omega
    exact not_reachable_of_two_sig hsig
  | t13 i k rst hM _ hne hk => exact not_reachable_of_M_rowJ hne hM hk
  | t14 i k rst hS _ _ hne hk => exact not_reachable_of_S_rowM hne hS hk
  | t15 i k j rst hM _ _ hne hk => exact not_reachable_of_M_rowJ hne hM hk
  | t16 i k j rst hS _ _ _ hne hk => exact not_reachable_of_S_rowM hne hS hk
  | t17 i k v rst hM _ hne hk => exact not_reachable_of_M_rowJ hne hM hk
  | t18 i k j v rst hM _ _ hne hk => exact not_reachable_of_M_rowJ hne hM hk

#print axioms A_unreachable
