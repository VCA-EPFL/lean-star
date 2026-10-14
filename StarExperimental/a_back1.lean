import StarExperimental.a

/-! # `a_back1`: un passo all'indietro dai 18 costruttori di `A`

Per ogni costruttore `tK` di `A` (`a.lean`), il passo all'indietro fatto **sul costruttore**:
tutte le azioni (8 regole del parent, 8 interne della cache, 5 esterne) che possono essere
l'ultimo passo `p → s` con `s` in `tK`, assumendo `synced p`. Se l'azione non crea nessuno dei
campi fissati da `tK`, il predecessore è ancora in `A`. Se ne crea uno, il predecessore è un
nuovo vettore, raccolto in `Pre_tK` (un costruttore `n1, n2, …` per vettore, con l'azione e il
campo creato nel commento).

Per ogni `K`, nel namespace `ABack.TK`:
* `Pre_tK` — i predecessori di `tK` che non sono in `A`;
* `Pre_tK_unreachable` — sono irraggiungibili;
* `back_tK_int`, `back_tK_ext` — per ogni passo interno / esterno `p → s` con `s` in `tK`:
  `A p ∨ Pre_tK p`. Lean obbliga a considerare tutte le regole, quindi nessuna azione manca.

In fondo: `A₁` = `A` più tutti i `Pre_tK` (83 vettori nuovi), `A_back_int` / `A_back_ext`
(un passo indietro da `A` cade in `A₁`) e `A₁_unreachable`. -/

open THEORY Relation BackwardGen MSIView


namespace ABack.T1

/-! # Passo indietro sul costruttore `t1` di `A`

`t1`: `rsIμ v` in `parent.queue_cip i₁`, `rqM` in `parent.queue_cip i₂`, tutte le righe a `I`.

`Pre_t1` raccoglie i vettori dei predecessori (un passo, con `synced p`) che NON sono coperti
da `A`. `back_t1_int` / `back_t1_ext` certificano che nessuna azione è stata dimenticata. -/


namespace Back_t1

theorem getElem?_of_eraseIdx {α} {l : List α} {j k : Nat} {a : α}
    (h : (l.eraseIdx j)[k]? = some a) : ∃ k', k' ≠ j ∧ l[k']? = some a := by
  by_cases hk : k < j
  · exact ⟨k, by omega, by rwa [List.getElem?_eraseIdx_of_lt hk] at h⟩
  · exact ⟨k + 1, by omega, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h⟩

theorem getElem?_append_one {α} {l : List α} {b a : α} {k : Nat}
    (h : (l ++ [b])[k]? = some a) : l[k]? = some a ∨ a = b := by
  by_cases hk : k < l.length
  · left; rwa [List.getElem?_append_left hk] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have := List.mem_of_getElem? h
    simpa using this

/-- Un passo di cache che accoda `m` a `queue_cp`: un messaggio in `queue_cip` dopo il passo
c'era già prima, oppure è `m` appena accodato dalla cache `i`. -/
theorem cip_append {n} {p : MSIState n} (hsync : synced p) {i ia : Fin n} {ja : Nat} {x m : CPEvent}
    (h : (update_Fin i ((p.caches i).queue_cp ++ [m]) p.parent.queue_cip ia)[ja]? = some x) :
    (p.parent.queue_cip ia)[ja]? = some x ∨ (ia = i ∧ x = m) := by
  by_cases hia : ia = i
  · subst hia
    rw [update_Fin_gss] at h
    rcases getElem?_append_one h with h' | h'
    · left; rw [(hsync ia).1]; exact h'
    · right; exact ⟨rfl, h'⟩
  · left; rwa [update_Fin_gso2 _ _ _ _ hia] at h

/-- Un passo di cache che non tocca `queue_cp`: con `synced`, `queue_cip` non cambia. -/
theorem cip_same {n} {p : MSIState n} (hsync : synced p) {i ia : Fin n} {ja : Nat} {x : CPEvent}
    (h : (update_Fin i ((p.caches i).queue_cp) p.parent.queue_cip ia)[ja]? = some x) :
    (p.parent.queue_cip ia)[ja]? = some x := by
  by_cases hia : ia = i
  · subst hia; rw [update_Fin_gss] at h; rw [(hsync ia).1]; exact h
  · rwa [update_Fin_gso2 _ _ _ _ hia] at h

/-- Un passo del parent che consuma la posizione `j` di `queue_cip i`: un messaggio presente dopo
il passo era presente prima, in una posizione diversa da `j` se l'indice è `i`. -/
theorem cip_erase {n} {q : Fin n → List CPEvent} {i ia : Fin n} {j ja : Nat} {x : CPEvent}
    (h : (update_Fin i ((q i).eraseIdx j) q ia)[ja]? = some x) :
    ∃ ja', (ia = i → ja' ≠ j) ∧ (q ia)[ja']? = some x := by
  by_cases hia : ia = i
  · subst hia; rw [update_Fin_gss] at h
    obtain ⟨k', hk', h'⟩ := getElem?_of_eraseIdx h
    exact ⟨k', fun _ => hk', h'⟩
  · rw [update_Fin_gso2 _ _ _ _ hia] at h; exact ⟨ja, fun h' => absurd h' hia, h⟩

end Back_t1

open Back_t1

/-- I predecessori (un passo) di `t1` che non sono coperti da `A`. -/
inductive Pre_t1 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v'` on `i` creating row `i = I` (and `parent.value`):
  la riga di `i` non era a `I`, un `rsIμ v'` in `queue_cip i` in posizione `j`; il `rsIμ v` di `t1`
  è un altro messaggio (posizione diversa se `i₁ = i`). -/
  | n1 (p : MSIState n) (i i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v' v : Value) :
      (p.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v') →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (i₁ = i → j₁ ≠ j) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      ¬(p.parent.shared_state i = Bstate.I) →
      (∀ k, k ≠ i → p.parent.shared_state k = Bstate.I) →
      Pre_t1 p
  /-- from `downgrade_from_M_rq2` on `i` creating row `i = I`:
  la riga di `i` non era a `I`, un `rsIσ` in `queue_cip i`. -/
  | n2 (p : MSIState n) (i i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      ¬(p.parent.shared_state i = Bstate.I) →
      (∀ k, k ≠ i → p.parent.shared_state k = Bstate.I) →
      Pre_t1 p
  /-- from `rq_data_not_available` on `i₁` creating `rsIμ v` in `queue_cip i₁`
  (`v` è il valore della cache `i₁`): la cache `i₁` era in `M`. -/
  | n3 (p : MSIState n) (i₁ i₂ : Fin n) (j₂ : Nat) :
      (p.caches i₁).state = Bstate.M →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t1 p
  /-- from `upgrade_from_I_rq` on `i₂` creating `rqM` in `queue_cip i₂`:
  la cache `i₂` era in `I`, nessuna richiesta pendente è necessaria. -/
  | n4 (p : MSIState n) (i₁ i₂ : Fin n) (j₁ : Nat) (v : Value) :
      (p.caches i₂).state = Bstate.I →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t1 p
  /-- from `downgrade_from_M_rs` on `i₁` creating `rsIμ v` in `queue_cip i₁`
  (`v` è il valore della cache `i₁`): la cache `i₁` era in `M` con un `rqIμ` in `queue_pc`. -/
  | n5 (p : MSIState n) (i₁ i₂ : Fin n) (j j₂ : Nat) :
      (p.caches i₁).state = Bstate.M →
      ((p.caches i₁).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t1 p

/-- Controllo di sanità: ogni predecessore di uno stato irraggiungibile è irraggiungibile. -/
theorem Pre_t1_unreachable {n} {p : MSIState n} (h : Pre_t1 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i i₁ i₂ j j₁ j₂ v' v hj h₁ hne _ _ hall =>
    by_cases hi : i₁ = i
    · subst hi
      have h2 := two_le_countP_of_ne isReleaseM _ h₁ hj (hne rfl) rfl rfl
      have hmu : 2 ≤ muMsgs p.parent i₁ := by unfold muMsgs; omega
      exact not_reachable_of_two_mu hmu
    · exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁)
        (by rw [hall i₁ hi]; intro h; cases h)
  | n2 i i₁ i₂ j j₁ j₂ v hj h₁ _ _ hall =>
    by_cases hi : i₁ = i
    · subst hi
      exact not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsIμ h₁) (sigMsgs_ne_zero_of_rsIσ hj)
    · exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁)
        (by rw [hall i₁ hi]; intro h; cases h)
  | n3 i₁ i₂ j₂ hM _ hall =>
    exact not_reachable_of_notI_rowI (by rw [hM]; intro h; cases h) (hall i₁)
  | n4 i₁ i₂ j₁ v _ h₁ hall =>
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (by rw [hall i₁]; intro h; cases h)
  | n5 i₁ i₂ j j₂ hM _ _ hall =>
    exact not_reachable_of_notI_rowI (by rw [hM]; intro h; cases h) (hall i₁)

/-- **Passo indietro interno su `t1`**: se `s` soddisfa le ipotesi di `t1` e `p → s` è un passo
interno con `synced p`, allora `p ∈ A` oppure `p` è uno dei vettori nuovi di `Pre_t1`. -/
theorem back_t1_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s)
    (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v))
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I) : A p ∨ Pre_t1 p := by
  cases hstep with
  | cache cache' i ce hc =>
    cases hc with
    | rq_data_not_available hM =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨hi, _⟩
      · exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
      · subst hi; exact Or.inr (Pre_t1.n3 p _ i₂ j₂ hM h₂' hall)
    | rq_data_not_available1 hS =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
    | upgrade_from_I_rq hI =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₂ with h₂' | ⟨hi, _⟩
      · exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
      · subst hi; exact Or.inr (Pre_t1.n4 p i₁ _ j₁ v hI h₁' hall)
    | upgrade_from_I_rq1 hI =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
    | upgrade_from_I_rs v' j hj hI =>
      dsimp only at h₁ h₂ hall
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hall)
    | upgrade_from_I_rsS v' j hj hI =>
      dsimp only at h₁ h₂ hall
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hall)
    | downgrade_from_M_rs j hj hM =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨hi, _⟩
      · exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
      · subst hi; exact Or.inr (Pre_t1.n5 p _ i₂ j j₂ hM hj h₂' hall)
    | downgrade_from_M_rs1 j hj hS =>
      dsimp only at h₁ h₂ hall
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁' h₂' hall)
  | parent_upd_queue parent' pe i hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j hj =>
      dsimp only at h₁ h₂ hall
      obtain ⟨j₁', hne₁, h₁'⟩ := cip_erase h₁
      obtain ⟨j₂', _, h₂'⟩ := cip_erase h₂
      have hrest : ∀ k, k ≠ i → p.parent.shared_state k = Bstate.I := fun k hk => by
        have := hall k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hrow : p.parent.shared_state i = Bstate.I
      · refine Or.inl (A.t1 p i₁ i₂ j₁' j₂' v h₁' h₂' (fun k => ?_))
        by_cases hk : k = i
        · subst hk; exact hrow
        · exact hrest k hk
      · exact Or.inr (Pre_t1.n1 p i i₁ i₂ j j₁' j₂' v' v hj h₁' hne₁ h₂' hrow hrest)
    | downgrade_from_M_rq2 _ j hj =>
      dsimp only at h₁ h₂ hall
      obtain ⟨j₁', _, h₁'⟩ := cip_erase h₁
      obtain ⟨j₂', _, h₂'⟩ := cip_erase h₂
      have hrest : ∀ k, k ≠ i → p.parent.shared_state k = Bstate.I := fun k hk => by
        have := hall k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hrow : p.parent.shared_state i = Bstate.I
      · refine Or.inl (A.t1 p i₁ i₂ j₁' j₂' v h₁' h₂' (fun k => ?_))
        by_cases hk : k = i
        · subst hk; exact hrow
        · exact hrest k hk
      · exact Or.inr (Pre_t1.n2 p i i₁ i₂ j j₁' j₂' v hj h₁' h₂' hrow hrest)
    | upgrade_to_M_data_avilable_rq1 =>
      -- impossibile come ultimo passo: lascia la riga `i` a `M`
      dsimp only at hall
      have := hall i; rw [update_Fin_gss] at this; cases this
    | upgrade_to_M_data_avilable_rq2 =>
      -- impossibile come ultimo passo: lascia la riga `i` a `S`
      dsimp only at hall
      have := hall i; rw [update_Fin_gss] at this; cases this
    | upgrade_to_M_invalid_all =>
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁ h₂ hall)
    | upgrade_to_M_invalid_all1 =>
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁ h₂ hall)
    | upgrade_to_M_invalid_all2 =>
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁ h₂ hall)
    | upgrade_to_M_invalid_all3 =>
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v h₁ h₂ hall)
  | parent_no_queue parent' pe i hp => cases hp

/-- **Passo indietro esterno su `t1`**: i passi esterni toccano solo `extqueue` e il valore della
cache, nessun campo fissato da `t1`: il predecessore è in `A` per `t1` stesso. -/
theorem back_t1_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s)
    (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v))
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I) : A p ∨ Pre_t1 p := by
  cases hstep with
  | cache ev cache' i hc =>
    cases hc <;> dsimp only at h₁ h₂ hall <;>
      exact Or.inl (A.t1 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hall)


end ABack.T1


namespace ABack.T2

/-! # Passo indietro sul costruttore `t2` di `A`

`t2`: `rsIμ v` in `parent.queue_cip i₁`, `rqS` in `parent.queue_cip i₂`, la riga di `i₂` a `I`,
nessuna riga a `M`.

`Pre_t2` raccoglie i vettori dei predecessori (un passo, con `synced p`) che NON sono coperti
da `A`. `back_t2_int` / `back_t2_ext` certificano che nessuna azione è stata dimenticata. -/


namespace Back_t2

theorem getElem?_of_eraseIdx {α} {l : List α} {j k : Nat} {a : α}
    (h : (l.eraseIdx j)[k]? = some a) : ∃ k', k' ≠ j ∧ l[k']? = some a := by
  by_cases hk : k < j
  · exact ⟨k, by omega, by rwa [List.getElem?_eraseIdx_of_lt hk] at h⟩
  · exact ⟨k + 1, by omega, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h⟩

theorem getElem?_append_one {α} {l : List α} {b a : α} {k : Nat}
    (h : (l ++ [b])[k]? = some a) : l[k]? = some a ∨ a = b := by
  by_cases hk : k < l.length
  · left; rwa [List.getElem?_append_left hk] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have := List.mem_of_getElem? h
    simpa using this

/-- Un passo di cache che accoda `m` a `queue_cp`: un messaggio in `queue_cip` dopo il passo
c'era già prima, oppure è `m` appena accodato dalla cache `i`. -/
theorem cip_append {n} {p : MSIState n} (hsync : synced p) {i ia : Fin n} {ja : Nat} {x m : CPEvent}
    (h : (update_Fin i ((p.caches i).queue_cp ++ [m]) p.parent.queue_cip ia)[ja]? = some x) :
    (p.parent.queue_cip ia)[ja]? = some x ∨ (ia = i ∧ x = m) := by
  by_cases hia : ia = i
  · subst hia
    rw [update_Fin_gss] at h
    rcases getElem?_append_one h with h' | h'
    · left; rw [(hsync ia).1]; exact h'
    · right; exact ⟨rfl, h'⟩
  · left; rwa [update_Fin_gso2 _ _ _ _ hia] at h

/-- Un passo di cache che non tocca `queue_cp`: con `synced`, `queue_cip` non cambia. -/
theorem cip_same {n} {p : MSIState n} (hsync : synced p) {i ia : Fin n} {ja : Nat} {x : CPEvent}
    (h : (update_Fin i ((p.caches i).queue_cp) p.parent.queue_cip ia)[ja]? = some x) :
    (p.parent.queue_cip ia)[ja]? = some x := by
  by_cases hia : ia = i
  · subst hia; rw [update_Fin_gss] at h; rw [(hsync ia).1]; exact h
  · rwa [update_Fin_gso2 _ _ _ _ hia] at h

/-- Un passo del parent che consuma la posizione `j` di `queue_cip i`: un messaggio presente dopo
il passo era presente prima, in una posizione diversa da `j` se l'indice è `i`. -/
theorem cip_erase {n} {q : Fin n → List CPEvent} {i ia : Fin n} {j ja : Nat} {x : CPEvent}
    (h : (update_Fin i ((q i).eraseIdx j) q ia)[ja]? = some x) :
    ∃ ja', (ia = i → ja' ≠ j) ∧ (q ia)[ja']? = some x := by
  by_cases hia : ia = i
  · subst hia; rw [update_Fin_gss] at h
    obtain ⟨k', hk', h'⟩ := getElem?_of_eraseIdx h
    exact ⟨k', fun _ => hk', h'⟩
  · rw [update_Fin_gso2 _ _ _ _ hia] at h; exact ⟨ja, fun h' => absurd h' hia, h⟩

end Back_t2

open Back_t2

/-- I predecessori (un passo) di `t2` che non sono coperti da `A`. -/
inductive Pre_t2 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v'` on `i₂` creating row `i₂ = I` (and `parent.value`):
  la riga di `i₂` non era a `I`, un `rsIμ v'` in `queue_cip i₂` in posizione `j`; il `rsIμ v` di
  `t2` è un altro messaggio (posizione diversa se `i₁ = i₂`). -/
  | n1 (p : MSIState n) (i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v' v : Value) :
      (p.parent.queue_cip i₂)[j]? = some (CPEvent.rsIμ v') →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (i₁ = i₂ → j₁ ≠ j) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      ¬(p.parent.shared_state i₂ = Bstate.I) →
      (∀ k, k ≠ i₂ → ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `downgrade_from_M_rq1 v'` on `i` (≠ `i₂`) creating row `i ≠ M` (and `parent.value`):
  la riga di `i` era a `M`, un `rsIμ v'` in `queue_cip i` in posizione `j`. -/
  | n2 (p : MSIState n) (i i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v' v : Value) :
      (p.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v') →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (i₁ = i → j₁ ≠ j) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.M →
      p.parent.shared_state i₂ = Bstate.I →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `downgrade_from_M_rq2` on `i₂` creating row `i₂ = I`:
  la riga di `i₂` non era a `I`, un `rsIσ` in `queue_cip i₂`. -/
  | n3 (p : MSIState n) (i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i₂)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      ¬(p.parent.shared_state i₂ = Bstate.I) →
      (∀ k, k ≠ i₂ → ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `downgrade_from_M_rq2` on `i` (≠ `i₂`) creating row `i ≠ M`:
  la riga di `i` era a `M`, un `rsIσ` in `queue_cip i`. -/
  | n4 (p : MSIState n) (i i₁ i₂ : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.M →
      p.parent.shared_state i₂ = Bstate.I →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `rq_data_not_available` on `i₁` creating `rsIμ v` in `queue_cip i₁`
  (`v` è il valore della cache `i₁`): la cache `i₁` era in `M`. -/
  | n5 (p : MSIState n) (i₁ i₂ : Fin n) (j₂ : Nat) :
      (p.caches i₁).state = Bstate.M →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i₂ = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `upgrade_from_I_rq1` on `i₂` creating `rqS` in `queue_cip i₂`:
  la cache `i₂` era in `I`, nessuna richiesta pendente è necessaria. -/
  | n6 (p : MSIState n) (i₁ i₂ : Fin n) (j₁ : Nat) (v : Value) :
      (p.caches i₂).state = Bstate.I →
      (p.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v) →
      p.parent.shared_state i₂ = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p
  /-- from `downgrade_from_M_rs` on `i₁` creating `rsIμ v` in `queue_cip i₁`
  (`v` è il valore della cache `i₁`): la cache `i₁` era in `M` con un `rqIμ` in `queue_pc`. -/
  | n7 (p : MSIState n) (i₁ i₂ : Fin n) (j j₂ : Nat) :
      (p.caches i₁).state = Bstate.M →
      ((p.caches i₁).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i₂ = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t2 p

/-- Controllo di sanità: ogni predecessore di uno stato irraggiungibile è irraggiungibile. -/
theorem Pre_t2_unreachable {n} {p : MSIState n} (h : Pre_t2 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i₁ i₂ j j₁ j₂ v' v hj h₁ hne _ _ hnoM =>
    by_cases hi : i₁ = i₂
    · subst hi
      have h2 := two_le_countP_of_ne isReleaseM _ h₁ hj (hne rfl) rfl rfl
      have hmu : 2 ≤ muMsgs p.parent i₁ := by unfold muMsgs; omega
      exact not_reachable_of_two_mu hmu
    · exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (hnoM i₁ hi)
  | n2 i i₁ i₂ j j₁ j₂ v' v hj h₁ hne _ _ _ hnoM =>
    by_cases hi : i₁ = i
    · subst hi
      have h2 := two_le_countP_of_ne isReleaseM _ h₁ hj (hne rfl) rfl rfl
      have hmu : 2 ≤ muMsgs p.parent i₁ := by unfold muMsgs; omega
      exact not_reachable_of_two_mu hmu
    · exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (hnoM i₁ hi)
  | n3 i₁ i₂ j j₁ j₂ v hj h₁ _ _ hnoM =>
    by_cases hi : i₁ = i₂
    · subst hi
      exact not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsIμ h₁) (sigMsgs_ne_zero_of_rsIσ hj)
    · exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (hnoM i₁ hi)
  | n4 i i₁ i₂ j j₁ j₂ v hj _ _ hM _ _ =>
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ hj) (by rw [hM]; intro h; cases h)
  | n5 i₁ i₂ j₂ hM _ _ hnoM =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i₁)))
  | n6 i₁ i₂ j₁ v _ h₁ _ hnoM =>
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ h₁) (hnoM i₁)
  | n7 i₁ i₂ j j₂ hM _ _ _ hnoM =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i₁)))

/-- **Passo indietro interno su `t2`**: se `s` soddisfa le ipotesi di `t2` e `p → s` è un passo
interno con `synced p`, allora `p ∈ A` oppure `p` è uno dei vettori nuovi di `Pre_t2`. -/
theorem back_t2_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s)
    (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v))
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i₂ = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M)) : A p ∨ Pre_t2 p := by
  cases hstep with
  | cache cache' i ce hc =>
    cases hc with
    | rq_data_not_available hM =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨hi, _⟩
      · exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
      · subst hi; exact Or.inr (Pre_t2.n5 p _ i₂ j₂ hM h₂' hI hnoM)
    | rq_data_not_available1 hS =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
    | upgrade_from_I_rq hIc =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
    | upgrade_from_I_rq1 hIc =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₂ with h₂' | ⟨hi, _⟩
      · exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
      · subst hi; exact Or.inr (Pre_t2.n6 p i₁ _ j₁ v hIc h₁' hI hnoM)
    | upgrade_from_I_rs v' j hj hIc =>
      dsimp only at h₁ h₂ hI hnoM
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hI hnoM)
    | upgrade_from_I_rsS v' j hj hIc =>
      dsimp only at h₁ h₂ hI hnoM
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hI hnoM)
    | downgrade_from_M_rs j hj hM =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨hi, _⟩
      · exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
      · subst hi; exact Or.inr (Pre_t2.n7 p _ i₂ j j₂ hM hj h₂' hI hnoM)
    | downgrade_from_M_rs1 j hj hS =>
      dsimp only at h₁ h₂ hI hnoM
      rcases cip_append hsync h₂ with h₂' | ⟨_, hx⟩
      swap
      · cases hx
      rcases cip_append hsync h₁ with h₁' | ⟨_, hx⟩
      swap
      · cases hx
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁' h₂' hI hnoM)
  | parent_upd_queue parent' pe i hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j hj =>
      dsimp only at h₁ h₂ hI hnoM
      obtain ⟨j₁', hne₁, h₁'⟩ := cip_erase h₁
      obtain ⟨j₂', _, h₂'⟩ := cip_erase h₂
      have hrest : ∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M) := fun k hk => by
        have := hnoM k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hi : i₂ = i
      · subst hi
        by_cases hrow : p.parent.shared_state i₂ = Bstate.I
        · refine Or.inl (A.t2 p i₁ i₂ j₁' j₂' v h₁' h₂' hrow (fun k => ?_))
          by_cases hk : k = i₂
          · subst hk; rw [hrow]; intro h; cases h
          · exact hrest k hk
        · exact Or.inr (Pre_t2.n1 p i₁ i₂ j j₁' j₂' v' v hj h₁' hne₁ h₂' hrow hrest)
      · have hI' : p.parent.shared_state i₂ = Bstate.I := by
          rwa [update_Fin_gso2 _ _ _ _ hi] at hI
        by_cases hrow : p.parent.shared_state i = Bstate.M
        · exact Or.inr (Pre_t2.n2 p i i₁ i₂ j j₁' j₂' v' v hj h₁' hne₁ h₂' hrow hI' hrest)
        · refine Or.inl (A.t2 p i₁ i₂ j₁' j₂' v h₁' h₂' hI' (fun k => ?_))
          by_cases hk : k = i
          · subst hk; exact hrow
          · exact hrest k hk
    | downgrade_from_M_rq2 _ j hj =>
      dsimp only at h₁ h₂ hI hnoM
      obtain ⟨j₁', _, h₁'⟩ := cip_erase h₁
      obtain ⟨j₂', _, h₂'⟩ := cip_erase h₂
      have hrest : ∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M) := fun k hk => by
        have := hnoM k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hi : i₂ = i
      · subst hi
        by_cases hrow : p.parent.shared_state i₂ = Bstate.I
        · refine Or.inl (A.t2 p i₁ i₂ j₁' j₂' v h₁' h₂' hrow (fun k => ?_))
          by_cases hk : k = i₂
          · subst hk; rw [hrow]; intro h; cases h
          · exact hrest k hk
        · exact Or.inr (Pre_t2.n3 p i₁ i₂ j j₁' j₂' v hj h₁' h₂' hrow hrest)
      · have hI' : p.parent.shared_state i₂ = Bstate.I := by
          rwa [update_Fin_gso2 _ _ _ _ hi] at hI
        by_cases hrow : p.parent.shared_state i = Bstate.M
        · exact Or.inr (Pre_t2.n4 p i i₁ i₂ j j₁' j₂' v hj h₁' h₂' hrow hI' hrest)
        · refine Or.inl (A.t2 p i₁ i₂ j₁' j₂' v h₁' h₂' hI' (fun k => ?_))
          by_cases hk : k = i
          · subst hk; exact hrow
          · exact hrest k hk
    | upgrade_to_M_data_avilable_rq1 =>
      -- impossibile come ultimo passo: lascia la riga `i` a `M`
      dsimp only at hnoM
      have := hnoM i; rw [update_Fin_gss] at this; exact absurd rfl this
    | upgrade_to_M_data_avilable_rq2 _ j hj hIi hnoMp =>
      dsimp only at h₁ h₂ hI hnoM
      by_cases hi : i₂ = i
      · -- impossibile come ultimo passo su `i₂`: lascia la riga `i₂` a `S`
        subst hi; rw [update_Fin_gss] at hI; cases hI
      · -- su `i ≠ i₂` non crea nessun campo fissato: il predecessore è in `A` per `t2`
        have hI' : p.parent.shared_state i₂ = Bstate.I := by
          rwa [update_Fin_gso2 _ _ _ _ hi] at hI
        obtain ⟨j₁', _, h₁'⟩ := cip_erase h₁
        obtain ⟨j₂', _, h₂'⟩ := cip_erase h₂
        exact Or.inl (A.t2 p i₁ i₂ j₁' j₂' v h₁' h₂' hI' hnoMp)
    | upgrade_to_M_invalid_all =>
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁ h₂ hI hnoM)
    | upgrade_to_M_invalid_all1 =>
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁ h₂ hI hnoM)
    | upgrade_to_M_invalid_all2 =>
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁ h₂ hI hnoM)
    | upgrade_to_M_invalid_all3 =>
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v h₁ h₂ hI hnoM)
  | parent_no_queue parent' pe i hp => cases hp

/-- **Passo indietro esterno su `t2`**: i passi esterni toccano solo `extqueue` e il valore della
cache, nessun campo fissato da `t2`: il predecessore è in `A` per `t2` stesso. -/
theorem back_t2_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s)
    (i₁ i₂ : Fin n) (j₁ j₂ : Nat) (v : Value)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some (CPEvent.rsIμ v))
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i₂ = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M)) : A p ∨ Pre_t2 p := by
  cases hstep with
  | cache ev cache' i hc =>
    cases hc <;> dsimp only at h₁ h₂ hI hnoM <;>
      exact Or.inl (A.t2 p i₁ i₂ j₁ j₂ v (cip_same hsync h₁) (cip_same hsync h₂) hI hnoM)


end ABack.T2


namespace ABack.T3

/-! # Un passo indietro sul costruttore `t3` di `A`

`t3 s i j₁ j₂`: `rsIσ` in `parent.queue_cip i` (posizione `j₁`), `rqM` in `parent.queue_cip i`
(posizione `j₂`), tutte le righe a `I`.

`Pre_t3` contiene i vettori dei predecessori NON coperti da `A`. -/

namespace BackT3

/-- Un elemento di `l ++ [a]` è già in `l`, oppure è l'ultimo (`a`). -/
theorem getElem?_append_single {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) : l[j]? = some b ∨ (j = l.length ∧ a = b) := by
  by_cases hj : j < l.length
  · left; rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    cases hd : j - l.length with
    | zero => rw [hd] at h; simp at h; exact ⟨by omega, h⟩
    | succ m => rw [hd] at h; simp at h

/-- Un elemento di `l.eraseIdx j` viene da una posizione di `l` diversa da `j`. -/
theorem getElem?_of_eraseIdx {α} {l : List α} {b : α} {j k : Nat}
    (h : (l.eraseIdx j)[k]? = some b) : ∃ k', k' ≠ j ∧ l[k']? = some b := by
  rw [List.getElem?_eraseIdx] at h
  split at h
  · exact ⟨k, by omega, h⟩
  · exact ⟨k + 1, by omega, h⟩

/-- Coda del parent dopo un `eraseIdx j` all'indice `c`: l'elemento letto all'indice `i` era già
nella coda, e se `c = i` in una posizione diversa da `j`. -/
theorem getElem?_update_erase {n} {α} {q : Fin n → List α} {c i : Fin n} {j k : Nat} {b : α}
    (h : (update_Fin c ((q c).eraseIdx j) q i)[k]? = some b) :
    ∃ k', (q i)[k']? = some b ∧ (c = i → k' ≠ j) := by
  by_cases hci : c = i
  · subst hci
    rw [update_Fin_gss] at h
    obtain ⟨k', hk', h'⟩ := getElem?_of_eraseIdx h
    exact ⟨k', h', fun _ => hk'⟩
  · rw [update_Fin_gso _ _ _ _ hci] at h
    exact ⟨k, h, fun hc => absurd hc hci⟩

end BackT3

open BackT3

/-- Predecessori di `t3` non coperti da `A`. -/
inductive Pre_t3 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_from_I_rq` on `i` creating the `rqM` in `parent.queue_cip i` -/
  | n1 (p : MSIState n) (i : Fin n) (j₁ : Nat) :
      (p.caches i).state = Bstate.I →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t3 p
  /-- from `downgrade_from_M_rq1 v` on `c` (any `c`, also `c = i`) creating the row `c = I` -/
  | n2 (p : MSIState n) (c i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip c)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqM →
      (∀ k, k ≠ c → p.parent.shared_state k = Bstate.I) →
      Pre_t3 p
  /-- from `downgrade_from_M_rq2` on `c ≠ i` creating the row `c = I` -/
  | n3 (p : MSIState n) (c i : Fin n) (j j₁ j₂ : Nat) :
      c ≠ i →
      (p.parent.queue_cip c)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqM →
      (∀ k, k ≠ c → p.parent.shared_state k = Bstate.I) →
      Pre_t3 p
  /-- from `downgrade_from_M_rq2` on `i` itself creating the row `i = I`: a second `rsIσ` in
  `parent.queue_cip i`, at a position `j ≠ j₁` -/
  | n4 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) :
      j ≠ j₁ →
      (p.parent.queue_cip i)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqM →
      (∀ k, k ≠ i → p.parent.shared_state k = Bstate.I) →
      Pre_t3 p

/-- Controllo di sanità: nessun predecessore di `t3` è raggiungibile. -/
theorem Pre_t3_unreachable {n} {p : MSIState n} (h : Pre_t3 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j₁ _ h₁ hall =>
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ h₁) (by rw [hall i]; intro h; cases h)
  | n2 c i j j₁ j₂ v hj h₁ _ hrows =>
    by_cases hci : c = i
    · subst hci
      exact not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsIμ hj) (sigMsgs_ne_zero_of_rsIσ h₁)
    · exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ h₁)
        (by rw [hrows i (Ne.symm hci)]; intro h; cases h)
  | n3 c i j j₁ j₂ hci _ h₁ _ hrows =>
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ h₁)
      (by rw [hrows i (Ne.symm hci)]; intro h; cases h)
  | n4 i j j₁ j₂ hne hj h₁ _ _ =>
    have h2 := two_le_countP_of_ne isReleaseS _ hj h₁ hne rfl rfl
    have hsig : 2 ≤ sigMsgs p.parent i := by unfold sigMsgs; omega
    exact not_reachable_of_two_sig hsig


/-- **Passo indietro interno su `t3`**: se `s` soddisfa le ipotesi di `t3` e `p → s` è un passo
interno da uno stato allineato, allora `p ∈ A` oppure `p ∈ Pre_t3`. -/
theorem back_t3_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s) (i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I) : A p ∨ Pre_t3 p := by
  cases hstep with
  | cache cache' c ce hc =>
    dsimp only at h₁ h₂ hall
    by_cases hci : c = i
    · subst hci
      rw [update_Fin_gss] at h₁ h₂
      have hq := (hsync c).1
      cases hc with
      | rq_data_not_available hM =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₁ with h₁' | ⟨_, h⟩
        · rcases getElem?_append_single h₂ with h₂' | ⟨_, h⟩
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · cases h
        · cases h
      | rq_data_not_available1 hS =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₂ with h₂' | ⟨_, h⟩
        · rcases getElem?_append_single h₁ with h₁' | _
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · exact Or.inl (A.t5 p c c c j₂ j₂ h₂' h₂' hall (Or.inl rfl)
              (by rw [hS]; intro h; cases h))
        · cases h
      | upgrade_from_I_rq hI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₁ with h₁' | ⟨_, h⟩
        · rcases getElem?_append_single h₂ with h₂' | _
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · exact Or.inr (Pre_t3.n1 p c j₁ hI h₁' hall)
        · cases h
      | upgrade_from_I_rq1 hI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₁ with h₁' | ⟨_, h⟩
        · rcases getElem?_append_single h₂ with h₂' | ⟨_, h⟩
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · cases h
        · cases h
      | upgrade_from_I_rs v j hj hI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        exact Or.inl (A.t3 p c j₁ j₂ h₁ h₂ hall)
      | upgrade_from_I_rsS v j hj hI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        exact Or.inl (A.t3 p c j₁ j₂ h₁ h₂ hall)
      | downgrade_from_M_rs j hj hM =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₁ with h₁' | ⟨_, h⟩
        · rcases getElem?_append_single h₂ with h₂' | ⟨_, h⟩
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · cases h
        · cases h
      | downgrade_from_M_rs1 j hj hS =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        rcases getElem?_append_single h₂ with h₂' | ⟨_, h⟩
        · rcases getElem?_append_single h₁ with h₁' | _
          · exact Or.inl (A.t3 p c j₁ j₂ h₁' h₂' hall)
          · exact Or.inl (A.t5 p c c c j₂ j₂ h₂' h₂' hall (Or.inl rfl)
              (by rw [hS]; intro h; cases h))
        · cases h
    · rw [update_Fin_gso _ _ _ _ hci] at h₁ h₂
      exact Or.inl (A.t3 p i j₁ j₂ h₁ h₂ hall)
  | parent_upd_queue parent' pe c hp =>
    dsimp only at h₁ h₂ hall
    cases hp with
    | downgrade_from_M_rq1 v _ j hj =>
      dsimp only at h₁ h₂ hall
      obtain ⟨j₁', h₁', _⟩ := getElem?_update_erase h₁
      obtain ⟨j₂', h₂', _⟩ := getElem?_update_erase h₂
      exact Or.inr (Pre_t3.n2 p c i j j₁' j₂' v hj h₁' h₂'
        (fun k hk => by have := hall k; rwa [update_Fin_gso2 _ _ _ _ hk] at this))
    | downgrade_from_M_rq2 _ j hj =>
      dsimp only at h₁ h₂ hall
      obtain ⟨j₁', h₁', hne⟩ := getElem?_update_erase h₁
      obtain ⟨j₂', h₂', _⟩ := getElem?_update_erase h₂
      have hrows : ∀ k, k ≠ c → p.parent.shared_state k = Bstate.I :=
        fun k hk => by have := hall k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hci : c = i
      · subst hci
        exact Or.inr (Pre_t3.n4 p c j j₁' j₂' (Ne.symm (hne rfl)) hj h₁' h₂' hrows)
      · exact Or.inr (Pre_t3.n3 p c i j j₁' j₂' hci hj h₁' h₂' hrows)
    | upgrade_to_M_data_avilable_rq1 _ j hj hI =>
      have := hall c
      dsimp only at this
      rw [update_Fin_gss] at this
      cases this
    | upgrade_to_M_data_avilable_rq2 _ j hj hI hnoM =>
      have := hall c
      dsimp only at this
      rw [update_Fin_gss] at this
      cases this
    | upgrade_to_M_invalid_all r _ j hj hrow =>
      have := hall c
      dsimp only at this
      rw [hrow] at this
      cases this
    | upgrade_to_M_invalid_all1 r _ j hj hrow =>
      have := hall c
      dsimp only at this
      rw [hrow] at this
      cases this
    | upgrade_to_M_invalid_all2 r _ j hj hne hrow =>
      have := hall c
      dsimp only at this
      rw [hrow] at this
      cases this
    | upgrade_to_M_invalid_all3 r _ j hj hrow =>
      have := hall c
      dsimp only at this
      rw [hrow] at this
      cases this
  | parent_no_queue parent' pe c hp => cases hp

/-- **Passo indietro esterno su `t3`**: i passi esterni non toccano i campi fissati. -/
theorem back_t3_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s) (i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I) : A p ∨ Pre_t3 p := by
  cases hstep with
  | cache ev cache' c hc =>
    dsimp only at h₁ h₂ hall
    have hq : update_Fin c cache'.queue_cp p.parent.queue_cip i = p.parent.queue_cip i := by
      by_cases hci : c = i
      · subst hci
        rw [update_Fin_gss, (hsync c).1]
        cases hc <;> rfl
      · rw [update_Fin_gso _ _ _ _ hci]
    rw [hq] at h₁ h₂
    exact Or.inl (A.t3 p i j₁ j₂ h₁ h₂ hall)


end ABack.T3


namespace ABack.T4

/-! # Un passo indietro sul costruttore `t4` di `A`

`t4 s i j₁ j₂`: `rsIσ` in `parent.queue_cip i` (posizione `j₁`), `rqS` in `parent.queue_cip i`
(posizione `j₂`), riga `i` a `I`, nessuna riga a `M`, cache `i` non in `I`.

`Pre_t4` contiene i vettori dei predecessori NON coperti da `A`. -/

namespace BackT4

/-- Un elemento di `l ++ [a]` è già in `l`, oppure è l'ultimo (`a`). -/
theorem getElem?_append_single {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) : l[j]? = some b ∨ (j = l.length ∧ a = b) := by
  by_cases hj : j < l.length
  · left; rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    cases hd : j - l.length with
    | zero => rw [hd] at h; simp at h; exact ⟨by omega, h⟩
    | succ m => rw [hd] at h; simp at h

/-- Un elemento di `l.eraseIdx j` viene da una posizione di `l` diversa da `j`. -/
theorem getElem?_of_eraseIdx {α} {l : List α} {b : α} {j k : Nat}
    (h : (l.eraseIdx j)[k]? = some b) : ∃ k', k' ≠ j ∧ l[k']? = some b := by
  rw [List.getElem?_eraseIdx] at h
  split at h
  · exact ⟨k, by omega, h⟩
  · exact ⟨k + 1, by omega, h⟩

/-- Coda del parent dopo un `eraseIdx j` all'indice `c`: l'elemento letto all'indice `i` era già
nella coda, e se `c = i` in una posizione diversa da `j`. -/
theorem getElem?_update_erase {n} {α} {q : Fin n → List α} {c i : Fin n} {j k : Nat} {b : α}
    (h : (update_Fin c ((q c).eraseIdx j) q i)[k]? = some b) :
    ∃ k', (q i)[k']? = some b ∧ (c = i → k' ≠ j) := by
  by_cases hci : c = i
  · subst hci
    rw [update_Fin_gss] at h
    obtain ⟨k', hk', h'⟩ := getElem?_of_eraseIdx h
    exact ⟨k', h', fun _ => hk'⟩
  · rw [update_Fin_gso _ _ _ _ hci] at h
    exact ⟨k, h, fun hc => absurd hc hci⟩

end BackT4

open BackT4

/-- Predecessori di `t4` non coperti da `A`. -/
inductive Pre_t4 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_from_I_rs v` on `i` creating the cache state `i ≠ I` (`:= M`) -/
  | n1 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t4 p
  /-- from `upgrade_from_I_rsS v` on `i` creating the cache state `i ≠ I` (`:= S`) -/
  | n2 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t4 p
  /-- from `downgrade_from_M_rq1 v` on `i` itself creating the row `i = I` -/
  | n3 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t4 p
  /-- from `downgrade_from_M_rq1 v` on `c ≠ i` creating the row `c ≠ M` (`:= I`) -/
  | n4 (p : MSIState n) (c i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      c ≠ i →
      (p.parent.queue_cip c)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, k ≠ c → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t4 p
  /-- from `downgrade_from_M_rq2` on `i` itself creating the row `i = I`: a second `rsIσ` in
  `parent.queue_cip i`, at a position `j ≠ j₁` -/
  | n5 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) :
      j ≠ j₁ →
      (p.parent.queue_cip i)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t4 p
  /-- from `downgrade_from_M_rq2` on `c ≠ i` creating the row `c ≠ M` (`:= I`) -/
  | n6 (p : MSIState n) (c i : Fin n) (j j₁ j₂ : Nat) :
      c ≠ i →
      (p.parent.queue_cip c)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, k ≠ c → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t4 p

/-- Controllo di sanità: nessun predecessore di `t4` è raggiungibile. -/
theorem Pre_t4_unreachable {n} {p : MSIState n} (h : Pre_t4 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j j₁ j₂ v _ hj _ _ hI _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hI]; intro h; cases h)
  | n2 i j j₁ j₂ v _ _ h₁ _ hI _ =>
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ h₁) (by rw [hI]; intro h; cases h)
  | n3 i j j₁ j₂ v hj h₁ _ _ _ =>
    exact not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsIμ hj) (sigMsgs_ne_zero_of_rsIσ h₁)
  | n4 c i j j₁ j₂ v _ _ _ _ hI _ hc => exact not_reachable_of_notI_rowI hc hI
  | n5 i j j₁ j₂ hne hj h₁ _ _ _ =>
    have h2 := two_le_countP_of_ne isReleaseS _ hj h₁ hne rfl rfl
    have hsig : 2 ≤ sigMsgs p.parent i := by unfold sigMsgs; omega
    exact not_reachable_of_two_sig hsig
  | n6 c i j j₁ j₂ _ _ _ _ hI _ hc => exact not_reachable_of_notI_rowI hc hI

/-- **Passo indietro interno su `t4`**: se `s` soddisfa le ipotesi di `t4` e `p → s` è un passo
interno da uno stato allineato, allora `p ∈ A` oppure `p ∈ Pre_t4`. -/
theorem back_t4_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s) (i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M))
    (hst : ¬((s.caches i).state = Bstate.I)) : A p ∨ Pre_t4 p := by
  cases hstep with
  | cache cache' c ce hc =>
    dsimp only at h₁ h₂ hI hnoM hst
    by_cases hci : c = i
    · subst hci
      rw [update_Fin_gss] at h₁ h₂ hst
      have hq := (hsync c).1
      cases hc with
      | rq_data_not_available hM => exact absurd rfl hst
      | rq_data_not_available1 hS => exact absurd rfl hst
      | upgrade_from_I_rq hcI => exact absurd hcI hst
      | upgrade_from_I_rq1 hcI => exact absurd hcI hst
      | upgrade_from_I_rs v j hj hcI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        exact Or.inr (Pre_t4.n1 p c j j₁ j₂ v hcI hj h₁ h₂ hI hnoM)
      | upgrade_from_I_rsS v j hj hcI =>
        dsimp only at h₁ h₂
        rw [← hq] at h₁ h₂
        exact Or.inr (Pre_t4.n2 p c j j₁ j₂ v hcI hj h₁ h₂ hI hnoM)
      | downgrade_from_M_rs j hj hM => exact absurd rfl hst
      | downgrade_from_M_rs1 j hj hS => exact absurd rfl hst
    · rw [update_Fin_gso _ _ _ _ hci] at h₁ h₂ hst
      exact Or.inl (A.t4 p i j₁ j₂ h₁ h₂ hI hnoM hst)
  | parent_upd_queue parent' pe c hp =>
    dsimp only at h₁ h₂ hI hnoM hst
    -- un passo del parent non cambia lo stato delle cache
    have hst' : ¬((p.caches i).state = Bstate.I) := by
      by_cases hci : c = i
      · subst hci; rw [update_Fin_gss] at hst; exact hst
      · rw [update_Fin_gso _ _ _ _ hci] at hst; exact hst
    cases hp with
    | downgrade_from_M_rq1 v _ j hj =>
      dsimp only at h₁ h₂ hI hnoM
      obtain ⟨j₁', h₁', _⟩ := getElem?_update_erase h₁
      obtain ⟨j₂', h₂', _⟩ := getElem?_update_erase h₂
      have hrows : ∀ k, k ≠ c → ¬(p.parent.shared_state k = Bstate.M) :=
        fun k hk => by have := hnoM k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hci : c = i
      · subst hci
        exact Or.inr (Pre_t4.n3 p c j j₁' j₂' v hj h₁' h₂' hrows hst')
      · rw [update_Fin_gso _ _ _ _ hci] at hI
        exact Or.inr (Pre_t4.n4 p c i j j₁' j₂' v hci hj h₁' h₂' hI hrows hst')
    | downgrade_from_M_rq2 _ j hj =>
      dsimp only at h₁ h₂ hI hnoM
      obtain ⟨j₁', h₁', hne⟩ := getElem?_update_erase h₁
      obtain ⟨j₂', h₂', _⟩ := getElem?_update_erase h₂
      have hrows : ∀ k, k ≠ c → ¬(p.parent.shared_state k = Bstate.M) :=
        fun k hk => by have := hnoM k; rwa [update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hci : c = i
      · subst hci
        exact Or.inr (Pre_t4.n5 p c j j₁' j₂' (Ne.symm (hne rfl)) hj h₁' h₂' hrows hst')
      · rw [update_Fin_gso _ _ _ _ hci] at hI
        exact Or.inr (Pre_t4.n6 p c i j j₁' j₂' hci hj h₁' h₂' hI hrows hst')
    | upgrade_to_M_data_avilable_rq1 _ j hj hallI =>
      have := hnoM c
      dsimp only at this
      rw [update_Fin_gss] at this
      exact absurd rfl this
    | upgrade_to_M_data_avilable_rq2 _ j hj hcI hpnoM =>
      dsimp only at h₁ h₂ hI hnoM
      by_cases hci : c = i
      · subst hci
        rw [update_Fin_gss] at hI
        cases hI
      · rw [update_Fin_gso _ _ _ _ hci] at h₁ h₂ hI
        exact Or.inl (A.t4 p i j₁ j₂ h₁ h₂ hI hpnoM hst')
    | upgrade_to_M_invalid_all r _ j hj hrow =>
      exact absurd hrow (hnoM c)
    | upgrade_to_M_invalid_all1 r _ j hj hrow =>
      dsimp only at h₁ h₂ hI hnoM
      exact Or.inl (A.t4 p i j₁ j₂ h₁ h₂ hI hnoM hst')
    | upgrade_to_M_invalid_all2 r _ j hj hne hrow =>
      dsimp only at h₁ h₂ hI hnoM
      exact Or.inl (A.t4 p i j₁ j₂ h₁ h₂ hI hnoM hst')
    | upgrade_to_M_invalid_all3 r _ j hj hrow =>
      exact absurd hrow (hnoM c)
  | parent_no_queue parent' pe c hp => cases hp

/-- **Passo indietro esterno su `t4`**: i passi esterni non toccano i campi fissati. -/
theorem back_t4_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s) (i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rsIσ)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M))
    (hst : ¬((s.caches i).state = Bstate.I)) : A p ∨ Pre_t4 p := by
  cases hstep with
  | cache ev cache' c hc =>
    dsimp only at h₁ h₂ hI hnoM hst
    have hq : update_Fin c cache'.queue_cp p.parent.queue_cip i = p.parent.queue_cip i := by
      by_cases hci : c = i
      · subst hci
        rw [update_Fin_gss, (hsync c).1]
        cases hc <;> rfl
      · rw [update_Fin_gso _ _ _ _ hci]
    have hs : (update_Fin c cache' p.caches i).state = (p.caches i).state := by
      by_cases hci : c = i
      · subst hci
        rw [update_Fin_gss]
        cases hc <;> rfl
      · rw [update_Fin_gso _ _ _ _ hci]
    rw [hq] at h₁ h₂
    rw [hs] at hst
    exact Or.inl (A.t4 p i j₁ j₂ h₁ h₂ hI hnoM hst)


end ABack.T4


namespace ABack.T5

/-! # Passo indietro sul costruttore `t5` di `A`

`t5`: `rqM` in `parent.queue_cip i₁` (posizione `j₁`), `rqM` in `parent.queue_cip i₂`
(posizione `j₂`), tutte le righe a `I`, e la cache `i` (uno dei due richiedenti) non in `I`.

`Pre_t5` raccoglie i vettori dei predecessori NON coperti da `A`; `back_t5_int` / `back_t5_ext`
certificano che ogni predecessore `synced` di uno stato di `t5` è in `A` oppure in `Pre_t5`. -/


/-- I predecessori di `t5` che non sono coperti da `A`. -/
inductive Pre_t5 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v` on `q` creating `shared_state q = I` (riga `q` non a `I`
  prima del passo; se era già a `I` il predecessore è in `A` per `t1`). -/
  | n1 (p : MSIState n) (q i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, k ≠ q → p.parent.shared_state k = Bstate.I) →
      ¬(p.parent.shared_state q = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t5 p
  /-- from `downgrade_from_M_rq2` on `q` creating `shared_state q = I` (riga `q` non a `I`
  prima del passo; se era già a `I` il predecessore è in `A` per `t5`). -/
  | n2 (p : MSIState n) (q i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) :
      (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, k ≠ q → p.parent.shared_state k = Bstate.I) →
      ¬(p.parent.shared_state q = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t5 p
  /-- from `upgrade_from_I_rs v` on `i` creating `(caches i).state = M` (≠ `I`). -/
  | n3 (p : MSIState n) (i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      Pre_t5 p
  /-- from `upgrade_from_I_rsS v` on `i` creating `(caches i).state = S` (≠ `I`). -/
  | n4 (p : MSIState n) (i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      Pre_t5 p

/-- **Nessun predecessore nuovo di `t5` è raggiungibile.** -/
theorem Pre_t5_unreachable {n} {p : MSIState n} (h : Pre_t5 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 q i₁ i₂ i j j₁ j₂ v hmsg _ _ hrows _ _ hc =>
    by_cases hq : i = q
    · subst hq
      cases hst : (p.caches i).state with
      | M => exact not_reachable_of_M hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
      | S => exact not_reachable_of_S hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
      | I => exact absurd hst hc
    · exact not_reachable_of_notI_rowI hc (hrows i hq)
  | n2 q i₁ i₂ i j j₁ j₂ hmsg _ _ hrows _ _ hc =>
    by_cases hq : i = q
    · subst hq
      cases hst : (p.caches i).state with
      | M => exact not_reachable_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
      | S => exact not_reachable_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
      | I => exact absurd hst hc
    · exact not_reachable_of_notI_rowI hc (hrows i hq)
  | n3 i₁ i₂ i j j₁ j₂ v _ hj _ _ hall _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hall i]; intro h; cases h)
  | n4 i₁ i₂ i j j₁ j₂ v _ hj _ _ hall _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj) (by rw [hall i]; intro h; cases h)

/-! ## Lemmi di trasporto all'indietro (un passo) -/

namespace BackT5

theorem getElem?_of_append_singleton {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [b])[j]? = some a) (hne : a ≠ b) : l[j]? = some a := by
  by_cases hj : j < l.length
  · rwa [List.getElem?_append_left hj] at h
  · exfalso
    rw [List.getElem?_append_right (by omega)] at h
    cases hk : j - l.length with
    | zero => rw [hk] at h; simp at h; exact hne h.symm
    | succ m => rw [hk] at h; simp at h

theorem getElem?_of_eraseIdx {α} {l : List α} {a : α} {j k : Nat}
    (h : (l.eraseIdx j)[k]? = some a) : ∃ k' : Nat, l[k']? = some a := by
  by_cases hk : k < j
  · exact ⟨k, by rwa [List.getElem?_eraseIdx_of_lt hk] at h⟩
  · exact ⟨k + 1, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h⟩

/-- Un messaggio nella coda `queue_cip k` dopo che un passo del parent ha tolto una posizione
dalla coda di `q` era già nella coda di `k` prima del passo. -/
theorem cip_erase_back {n} {f : Fin n → List CPEvent} {q k : Fin n} {j j' : Nat} {a : CPEvent}
    (h : (update_Fin q ((f q).eraseIdx j) f k)[j']? = some a) : ∃ j'' : Nat, (f k)[j'']? = some a := by
  by_cases hk : q = k
  · subst hk; rw [update_Fin_gss] at h; exact getElem?_of_eraseIdx h
  · rw [update_Fin_gso _ _ _ _ hk] at h; exact ⟨_, h⟩

/-- Un passo esterno non tocca stati delle cache, righe, e (con `synced`) code `queue_cip`. -/
theorem ext_back {n} {p s : MSIState n} {e} (hsync : synced p) (h : msi_step_external p e s) :
    (∀ k, (s.caches k).state = (p.caches k).state)
      ∧ s.parent.shared_state = p.parent.shared_state
      ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) := by
  cases h with
  | cache e cache' q hc =>
    refine ⟨?_, rfl, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; rw [(hsync k).1]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Un passo di cache non tocca le righe del parent. -/
theorem cache_rows_back {n} {p s : MSIState n} {ce q}
    (h : msi_step_internal p (.cache ce q) s) : s.parent.shared_state = p.parent.shared_state := by
  cases h; rfl

/-- Chi crea "cache `i` non in `I`": solo la presa di un grant (`rsM` o `rsS`) da parte di `i`,
che non tocca le code `queue_cip`. -/
theorem cache_state_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (i : Fin n) (hc : ¬ (s.caches i).state = Bstate.I) :
    ¬ (p.caches i).state = Bstate.I ∨
    ((p.caches i).state = Bstate.I ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) ∧
      ((∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v))
        ∨ (∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v)))) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : i = q
    · subst hk
      simp only [update_Fin_gss] at hc
      have hcip : ∀ k, cache'.queue_cp = (p.caches i).queue_cp →
          (update_Fin i cache'.queue_cp p.parent.queue_cip) k = p.parent.queue_cip k := by
        intro k hq
        by_cases hk : k = i
        · subst hk; rw [update_Fin_gss, hq, (hsync k).1]
        · rw [update_Fin_gso2 _ _ _ _ hk]
      cases hstep with
      | rq_data_not_available hM => exact absurd rfl hc
      | rq_data_not_available1 hS => exact absurd rfl hc
      | upgrade_from_I_rq hI => exact absurd hI hc
      | upgrade_from_I_rq1 hI => exact absurd hI hc
      | upgrade_from_I_rs v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inl ⟨j, v, hj⟩⟩
      | upgrade_from_I_rsS v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inr ⟨j, v, hj⟩⟩
      | downgrade_from_M_rs j hj hM => exact absurd rfl hc
      | downgrade_from_M_rs1 j hj hS => exact absurd rfl hc
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hc

/-- Chi crea una richiesta (`rqM` o `rqS`) in `queue_cip k`: solo la cache `k` stessa, che è in
`I` prima e dopo il passo. -/
theorem cip_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (k : Fin n) (j : Nat) (a : CPEvent)
    (ha : a = CPEvent.rqM ∨ a = CPEvent.rqS)
    (hm : (s.parent.queue_cip k)[j]? = some a) :
    (p.parent.queue_cip k)[j]? = some a
      ∨ ((p.caches k).state = Bstate.I ∧ (s.caches k).state = Bstate.I) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : k = q
    · subst hk
      simp only [update_Fin_gss] at hm ⊢
      rw [(hsync k).1]
      cases hstep with
      | rq_data_not_available hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | rq_data_not_available1 hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | upgrade_from_I_rq hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rq1 hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rs v j hj hI => exact Or.inl hm
      | upgrade_from_I_rsS v j hj hI => exact Or.inl hm
      | downgrade_from_M_rs j hj hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | downgrade_from_M_rs1 j hj hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hm

/-- Inversione di un passo del parent: non tocca gli stati delle cache, ed è di una di cinque
forme (rilascio `M`, rilascio `S`, una riga a `M` dopo il passo, grant di `S`, invalidate di una
riga a `S`). -/
theorem parent_back {n} {p s : MSIState n} {pe} (h : msi_step_internal p (.parent pe) s) :
    (∀ k, (s.caches k).state = (p.caches k).state) ∧
    ((∃ (q : Fin n) (j : Nat) (v : Value), (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, s.parent.shared_state q = Bstate.M)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rqS ∧
        p.parent.shared_state q = Bstate.I ∧ (∀ k, ¬ p.parent.shared_state k = Bstate.M) ∧
        s.parent.shared_state = update_Fin q Bstate.S p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, p.parent.shared_state q = Bstate.S ∧ s.parent.shared_state = p.parent.shared_state ∧
        s.parent.queue_cip = p.parent.queue_cip)) := by
  cases h with
  | parent_no_queue parent' e i hp => cases hp
  | parent_upd_queue parent' e q hp =>
    refine ⟨?_, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · cases hp
      · exact Or.inl ⟨_, _, _, ‹_›, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨q, by simp only [update_Fin_gss]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, ‹_›, ‹_›, ‹_›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))

end BackT5

open BackT5

/-- **Passo indietro interno su `t5`**: ogni predecessore `synced` di uno stato di `t5` è in `A`
oppure in `Pre_t5`. -/
theorem back_t5_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s)
    (i₁ i₂ i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hi : i = i₁ ∨ i = i₂)
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t5 p := by
  cases e with
  | intro => cases hstep
  | cache ce q =>
    have hrows := cache_rows_back hstep
    rw [hrows] at hall
    rcases cache_state_back hsync hstep i hc with hc' | ⟨hI, hq, hrs | hrs⟩
    · -- la cache `i` non era in `I`: basta il suo `rqM`, che non può essere appena stato creato
      rcases hi with rfl | rfl
      · rcases cip_back hsync hstep _ _ _ (Or.inl rfl) h₁ with h | ⟨_, h⟩
        · exact Or.inl (A.t5 p i i i j₁ j₁ h h hall (Or.inl rfl) hc')
        · exact absurd h hc
      · rcases cip_back hsync hstep _ _ _ (Or.inl rfl) h₂ with h | ⟨_, h⟩
        · exact Or.inl (A.t5 p i i i j₂ j₂ h h hall (Or.inl rfl) hc')
        · exact absurd h hc
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t5.n3 p i₁ i₂ i j j₁ j₂ v hI hj h₁ h₂ hall hi)
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t5.n4 p i₁ i₂ i j j₁ j₂ v hI hj h₁ h₂ hall hi)
  | parent pe =>
    obtain ⟨hst, hD⟩ := parent_back hstep
    rw [hst] at hc
    rcases hD with ⟨q, j, v, hmsg, hrow, hq⟩ | ⟨q, j, hmsg, hrow, hq⟩ | ⟨q, hM⟩
        | ⟨q, j, hmsg, hI, hnoM, hrow, hq⟩ | ⟨q, hS, hrow, hq⟩
    · rw [hq] at h₁ h₂
      obtain ⟨j₁', h₁'⟩ := cip_erase_back h₁
      obtain ⟨j₂', h₂'⟩ := cip_erase_back h₂
      have hrows : ∀ k, k ≠ q → p.parent.shared_state k = Bstate.I := by
        intro k hk; have := hall k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqI : p.parent.shared_state q = Bstate.I
      · refine Or.inl (A.t1 p q i₁ j j₁' v hmsg h₁' ?_)
        intro k; by_cases hk : k = q
        · subst hk; exact hqI
        · exact hrows k hk
      · exact Or.inr (Pre_t5.n1 p q i₁ i₂ i j j₁' j₂' v hmsg h₁' h₂' hrows hqI hi hc)
    · rw [hq] at h₁ h₂
      obtain ⟨j₁', h₁'⟩ := cip_erase_back h₁
      obtain ⟨j₂', h₂'⟩ := cip_erase_back h₂
      have hrows : ∀ k, k ≠ q → p.parent.shared_state k = Bstate.I := by
        intro k hk; have := hall k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqI : p.parent.shared_state q = Bstate.I
      · refine Or.inl (A.t5 p i₁ i₂ i j₁' j₂' h₁' h₂' ?_ hi hc)
        intro k; by_cases hk : k = q
        · subst hk; exact hqI
        · exact hrows k hk
      · exact Or.inr (Pre_t5.n2 p q i₁ i₂ i j j₁' j₂' hmsg h₁' h₂' hrows hqI hi hc)
    · rw [hall q] at hM; cases hM
    · have := hall q; rw [hrow, update_Fin_gss] at this; cases this
    · have := hall q; rw [hrow, hS] at this; cases this

/-- **Passo indietro esterno su `t5`**: un passo esterno non tocca nessun campo fissato. -/
theorem back_t5_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s)
    (i₁ i₂ i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hi : i = i₁ ∨ i = i₂)
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t5 p := by
  obtain ⟨hst, hrows, hq⟩ := ext_back hsync hstep
  rw [hst] at hc; rw [hq] at h₁ h₂; rw [hrows] at hall
  exact Or.inl (A.t5 p i₁ i₂ i j₁ j₂ h₁ h₂ hall hi hc)


end ABack.T5


namespace ABack.T6

/-! # Passo indietro sul costruttore `t6` di `A`

`t6`: `rqM` in `parent.queue_cip i₁` (posizione `j₁`), `rqS` in `parent.queue_cip i₂`
(posizione `j₂`), tutte le righe a `I`, e la cache `i` (uno dei due richiedenti) non in `I`.

`Pre_t6` raccoglie i vettori dei predecessori NON coperti da `A`; `back_t6_int` / `back_t6_ext`
certificano che ogni predecessore `synced` di uno stato di `t6` è in `A` oppure in `Pre_t6`. -/


/-- I predecessori di `t6` che non sono coperti da `A`. -/
inductive Pre_t6 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v` on `q` creating `shared_state q = I`, riga `q` a `M` prima
  del passo. (Riga `q` già a `I`: predecessore in `A` per `t1`; riga `q` a `S` con `q ≠ i₂`:
  in `A` per `t2`; riga `q` a `S` con `q = i₂`: è `n6`.) -/
  | n1 (p : MSIState n) (q i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, k ≠ q → p.parent.shared_state k = Bstate.I) →
      p.parent.shared_state q = Bstate.M →
      (i = i₁ ∨ i = i₂) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t6 p
  /-- from `downgrade_from_M_rq2` on `q` creating `shared_state q = I` (riga `q` non a `I`
  prima del passo; se era già a `I` il predecessore è in `A` per `t6`). -/
  | n2 (p : MSIState n) (q i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) :
      (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, k ≠ q → p.parent.shared_state k = Bstate.I) →
      ¬(p.parent.shared_state q = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t6 p
  /-- from `upgrade_from_I_rs v` on `i` creating `(caches i).state = M` (≠ `I`). -/
  | n3 (p : MSIState n) (i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      Pre_t6 p
  /-- from `upgrade_from_I_rsS v` on `i` creating `(caches i).state = S` (≠ `I`). -/
  | n4 (p : MSIState n) (i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      (i = i₁ ∨ i = i₂) →
      Pre_t6 p
  /-- from `upgrade_from_I_rq` on `i₁` creating `rqM` in `parent.queue_cip i₁` (il richiedente
  di `M` è in `I`, quindi la cache non in `I` è `i₂`, quella del `rqS`; nel predecessore non c'è
  più nessun `rqM`). -/
  | n5 (p : MSIState n) (i₁ i₂ : Fin n) (j₂ : Nat) :
      (p.caches i₁).state = Bstate.I →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      ¬((p.caches i₂).state = Bstate.I) →
      Pre_t6 p
  /-- from `downgrade_from_M_rq1 v` on `i₂` (il richiedente di `S`) creating
  `shared_state i₂ = I`, riga `i₂` a `S` prima del passo: il `rsIμ` e il `rqS` sono nella stessa
  coda, e `t2` non si applica perché la riga del richiedente non è a `I`. -/
  | n6 (p : MSIState n) (i₁ i₂ i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i₂)[j]? = some (CPEvent.rsIμ v) →
      (p.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM →
      (p.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS →
      (∀ k, k ≠ i₂ → p.parent.shared_state k = Bstate.I) →
      p.parent.shared_state i₂ = Bstate.S →
      (i = i₁ ∨ i = i₂) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t6 p

/-- **Nessun predecessore nuovo di `t6` è raggiungibile.** -/
theorem Pre_t6_unreachable {n} {p : MSIState n} (h : Pre_t6 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 q i₁ i₂ i j j₁ j₂ v hmsg _ _ hrows _ _ hc =>
    by_cases hq : i = q
    · subst hq
      cases hst : (p.caches i).state with
      | M => exact not_reachable_of_M hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
      | S => exact not_reachable_of_S hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
      | I => exact absurd hst hc
    · exact not_reachable_of_notI_rowI hc (hrows i hq)
  | n2 q i₁ i₂ i j j₁ j₂ hmsg _ _ hrows _ _ hc =>
    by_cases hq : i = q
    · subst hq
      cases hst : (p.caches i).state with
      | M => exact not_reachable_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
      | S => exact not_reachable_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
      | I => exact absurd hst hc
    · exact not_reachable_of_notI_rowI hc (hrows i hq)
  | n3 i₁ i₂ i j j₁ j₂ v _ hj _ _ hall _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hall i]; intro h; cases h)
  | n4 i₁ i₂ i j j₁ j₂ v _ hj _ _ hall _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj) (by rw [hall i]; intro h; cases h)
  | n5 i₁ i₂ j₂ _ _ hall hc => exact not_reachable_of_notI_rowI hc (hall i₂)
  | n6 i₁ i₂ i j j₁ j₂ v hmsg _ _ _ hS _ _ =>
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ hmsg) (by rw [hS]; intro h; cases h)

/-! ## Lemmi di trasporto all'indietro (un passo) -/

namespace BackT6

theorem getElem?_of_append_singleton {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [b])[j]? = some a) (hne : a ≠ b) : l[j]? = some a := by
  by_cases hj : j < l.length
  · rwa [List.getElem?_append_left hj] at h
  · exfalso
    rw [List.getElem?_append_right (by omega)] at h
    cases hk : j - l.length with
    | zero => rw [hk] at h; simp at h; exact hne h.symm
    | succ m => rw [hk] at h; simp at h

theorem getElem?_of_eraseIdx {α} {l : List α} {a : α} {j k : Nat}
    (h : (l.eraseIdx j)[k]? = some a) : ∃ k' : Nat, l[k']? = some a := by
  by_cases hk : k < j
  · exact ⟨k, by rwa [List.getElem?_eraseIdx_of_lt hk] at h⟩
  · exact ⟨k + 1, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h⟩

/-- Un messaggio nella coda `queue_cip k` dopo che un passo del parent ha tolto una posizione
dalla coda di `q` era già nella coda di `k` prima del passo. -/
theorem cip_erase_back {n} {f : Fin n → List CPEvent} {q k : Fin n} {j j' : Nat} {a : CPEvent}
    (h : (update_Fin q ((f q).eraseIdx j) f k)[j']? = some a) : ∃ j'' : Nat, (f k)[j'']? = some a := by
  by_cases hk : q = k
  · subst hk; rw [update_Fin_gss] at h; exact getElem?_of_eraseIdx h
  · rw [update_Fin_gso _ _ _ _ hk] at h; exact ⟨_, h⟩

/-- Un passo esterno non tocca stati delle cache, righe, e (con `synced`) code `queue_cip`. -/
theorem ext_back {n} {p s : MSIState n} {e} (hsync : synced p) (h : msi_step_external p e s) :
    (∀ k, (s.caches k).state = (p.caches k).state)
      ∧ s.parent.shared_state = p.parent.shared_state
      ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) := by
  cases h with
  | cache e cache' q hc =>
    refine ⟨?_, rfl, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; rw [(hsync k).1]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Un passo di cache non tocca le righe del parent. -/
theorem cache_rows_back {n} {p s : MSIState n} {ce q}
    (h : msi_step_internal p (.cache ce q) s) : s.parent.shared_state = p.parent.shared_state := by
  cases h; rfl

/-- Chi crea "cache `i` non in `I`": solo la presa di un grant (`rsM` o `rsS`) da parte di `i`,
che non tocca le code `queue_cip`. -/
theorem cache_state_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (i : Fin n) (hc : ¬ (s.caches i).state = Bstate.I) :
    ¬ (p.caches i).state = Bstate.I ∨
    ((p.caches i).state = Bstate.I ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) ∧
      ((∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v))
        ∨ (∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v)))) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : i = q
    · subst hk
      simp only [update_Fin_gss] at hc
      have hcip : ∀ k, cache'.queue_cp = (p.caches i).queue_cp →
          (update_Fin i cache'.queue_cp p.parent.queue_cip) k = p.parent.queue_cip k := by
        intro k hq
        by_cases hk : k = i
        · subst hk; rw [update_Fin_gss, hq, (hsync k).1]
        · rw [update_Fin_gso2 _ _ _ _ hk]
      cases hstep with
      | rq_data_not_available hM => exact absurd rfl hc
      | rq_data_not_available1 hS => exact absurd rfl hc
      | upgrade_from_I_rq hI => exact absurd hI hc
      | upgrade_from_I_rq1 hI => exact absurd hI hc
      | upgrade_from_I_rs v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inl ⟨j, v, hj⟩⟩
      | upgrade_from_I_rsS v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inr ⟨j, v, hj⟩⟩
      | downgrade_from_M_rs j hj hM => exact absurd rfl hc
      | downgrade_from_M_rs1 j hj hS => exact absurd rfl hc
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hc

/-- Chi crea una richiesta (`rqM` o `rqS`) in `queue_cip k`: solo la cache `k` stessa, che è in
`I` prima e dopo il passo. -/
theorem cip_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (k : Fin n) (j : Nat) (a : CPEvent)
    (ha : a = CPEvent.rqM ∨ a = CPEvent.rqS)
    (hm : (s.parent.queue_cip k)[j]? = some a) :
    (p.parent.queue_cip k)[j]? = some a
      ∨ ((p.caches k).state = Bstate.I ∧ (s.caches k).state = Bstate.I) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : k = q
    · subst hk
      simp only [update_Fin_gss] at hm ⊢
      rw [(hsync k).1]
      cases hstep with
      | rq_data_not_available hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | rq_data_not_available1 hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | upgrade_from_I_rq hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rq1 hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rs v j hj hI => exact Or.inl hm
      | upgrade_from_I_rsS v j hj hI => exact Or.inl hm
      | downgrade_from_M_rs j hj hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | downgrade_from_M_rs1 j hj hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hm

/-- Inversione di un passo del parent: non tocca gli stati delle cache, ed è di una di cinque
forme (rilascio `M`, rilascio `S`, una riga a `M` dopo il passo, grant di `S`, invalidate di una
riga a `S`). -/
theorem parent_back {n} {p s : MSIState n} {pe} (h : msi_step_internal p (.parent pe) s) :
    (∀ k, (s.caches k).state = (p.caches k).state) ∧
    ((∃ (q : Fin n) (j : Nat) (v : Value), (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, s.parent.shared_state q = Bstate.M)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rqS ∧
        p.parent.shared_state q = Bstate.I ∧ (∀ k, ¬ p.parent.shared_state k = Bstate.M) ∧
        s.parent.shared_state = update_Fin q Bstate.S p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, p.parent.shared_state q = Bstate.S ∧ s.parent.shared_state = p.parent.shared_state ∧
        s.parent.queue_cip = p.parent.queue_cip)) := by
  cases h with
  | parent_no_queue parent' e i hp => cases hp
  | parent_upd_queue parent' e q hp =>
    refine ⟨?_, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · cases hp
      · exact Or.inl ⟨_, _, _, ‹_›, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨q, by simp only [update_Fin_gss]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, ‹_›, ‹_›, ‹_›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))

end BackT6

open BackT6

/-- **Passo indietro interno su `t6`**: ogni predecessore `synced` di uno stato di `t6` è in `A`
oppure in `Pre_t6`. -/
theorem back_t6_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s)
    (i₁ i₂ i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hi : i = i₁ ∨ i = i₂)
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t6 p := by
  cases e with
  | intro => cases hstep
  | cache ce q =>
    have hrows := cache_rows_back hstep
    rw [hrows] at hall
    rcases cache_state_back hsync hstep i hc with hc' | ⟨hI, hq, hrs | hrs⟩
    · rcases hi with rfl | rfl
      · -- la cache non in `I` è il richiedente di `M`: il suo `rqM` c'era già, è `t5`
        rcases cip_back hsync hstep _ _ _ (Or.inl rfl) h₁ with h | ⟨_, h⟩
        · exact Or.inl (A.t5 p i i i j₁ j₁ h h hall (Or.inl rfl) hc')
        · exact absurd h hc
      · -- la cache non in `I` è il richiedente di `S`: il suo `rqS` c'era già
        rcases cip_back hsync hstep _ _ _ (Or.inr rfl) h₂ with h | ⟨_, h⟩
        · rcases cip_back hsync hstep _ _ _ (Or.inl rfl) h₁ with h' | ⟨hI₁, _⟩
          · exact Or.inl (A.t6 p i₁ i i j₁ j₂ h' h hall (Or.inr rfl) hc')
          · exact Or.inr (Pre_t6.n5 p i₁ i j₂ hI₁ h hall hc')
        · exact absurd h hc
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t6.n3 p i₁ i₂ i j j₁ j₂ v hI hj h₁ h₂ hall hi)
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t6.n4 p i₁ i₂ i j j₁ j₂ v hI hj h₁ h₂ hall hi)
  | parent pe =>
    obtain ⟨hst, hD⟩ := parent_back hstep
    rw [hst] at hc
    rcases hD with ⟨q, j, v, hmsg, hrow, hq⟩ | ⟨q, j, hmsg, hrow, hq⟩ | ⟨q, hM⟩
        | ⟨q, j, hmsg, hI, hnoM, hrow, hq⟩ | ⟨q, hS, hrow, hq⟩
    · rw [hq] at h₁ h₂
      obtain ⟨j₁', h₁'⟩ := cip_erase_back h₁
      obtain ⟨j₂', h₂'⟩ := cip_erase_back h₂
      have hrows : ∀ k, k ≠ q → p.parent.shared_state k = Bstate.I := by
        intro k hk; have := hall k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqI : p.parent.shared_state q = Bstate.I
      · refine Or.inl (A.t1 p q i₁ j j₁' v hmsg h₁' ?_)
        intro k; by_cases hk : k = q
        · subst hk; exact hqI
        · exact hrows k hk
      · cases hqs : p.parent.shared_state q with
        | I => exact absurd hqs hqI
        | M => exact Or.inr (Pre_t6.n1 p q i₁ i₂ i j j₁' j₂' v hmsg h₁' h₂' hrows hqs hi hc)
        | S =>
          by_cases hq2 : i₂ = q
          · subst hq2
            exact Or.inr (Pre_t6.n6 p i₁ i₂ i j j₁' j₂' v hmsg h₁' h₂' hrows hqs hi hc)
          · -- riga `q` a `S`, `q ≠ i₂`: nessuna riga a `M` e la riga di `i₂` è a `I`, è `t2`
            refine Or.inl (A.t2 p q i₂ j j₂' v hmsg h₂' (hrows i₂ hq2) ?_)
            intro k; by_cases hk : k = q
            · subst hk; rw [hqs]; intro h; cases h
            · rw [hrows k hk]; intro h; cases h
    · rw [hq] at h₁ h₂
      obtain ⟨j₁', h₁'⟩ := cip_erase_back h₁
      obtain ⟨j₂', h₂'⟩ := cip_erase_back h₂
      have hrows : ∀ k, k ≠ q → p.parent.shared_state k = Bstate.I := by
        intro k hk; have := hall k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqI : p.parent.shared_state q = Bstate.I
      · refine Or.inl (A.t6 p i₁ i₂ i j₁' j₂' h₁' h₂' ?_ hi hc)
        intro k; by_cases hk : k = q
        · subst hk; exact hqI
        · exact hrows k hk
      · exact Or.inr (Pre_t6.n2 p q i₁ i₂ i j j₁' j₂' hmsg h₁' h₂' hrows hqI hi hc)
    · rw [hall q] at hM; cases hM
    · have := hall q; rw [hrow, update_Fin_gss] at this; cases this
    · have := hall q; rw [hrow, hS] at this; cases this

/-- **Passo indietro esterno su `t6`**: un passo esterno non tocca nessun campo fissato. -/
theorem back_t6_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s)
    (i₁ i₂ i : Fin n) (j₁ j₂ : Nat)
    (h₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (h₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hi : i = i₁ ∨ i = i₂)
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t6 p := by
  obtain ⟨hst, hrows, hq⟩ := ext_back hsync hstep
  rw [hst] at hc; rw [hq] at h₁ h₂; rw [hrows] at hall
  exact Or.inl (A.t6 p i₁ i₂ i j₁ j₂ h₁ h₂ hall hi hc)


end ABack.T6


namespace ABack.T7

/-! # Passo indietro sul costruttore `t7` di `A`

`t7`: due `rqS` in posizioni diverse `j₁ ≠ j₂` di `parent.queue_cip i`, riga `i` a `I`, nessuna
riga a `M`, e la cache `i` non in `I`.

`Pre_t7` raccoglie i vettori dei predecessori NON coperti da `A`; `back_t7_int` / `back_t7_ext`
certificano che ogni predecessore `synced` di uno stato di `t7` è in `A` oppure in `Pre_t7`. -/


/-- I predecessori di `t7` che non sono coperti da `A`. -/
inductive Pre_t7 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v` on `i` creating `shared_state i = I` (riga `i` non a `I`
  prima del passo; se era già a `I` il predecessore è in `A` per `t2`). -/
  | n1 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      ¬(p.parent.shared_state i = Bstate.I) →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t7 p
  /-- from `downgrade_from_M_rq1 v` on `q ≠ i` creating `¬ shared_state q = M` (riga `q` a `M`
  prima del passo; se non era a `M` il predecessore è in `A` per `t7`). -/
  | n2 (p : MSIState n) (q i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      q ≠ i →
      (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      p.parent.shared_state q = Bstate.M →
      (∀ k, k ≠ q → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t7 p
  /-- from `downgrade_from_M_rq2` on `i` creating `shared_state i = I` (riga `i` non a `I`
  prima del passo; se era già a `I` il predecessore è in `A` per `t7`). -/
  | n3 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) :
      (p.parent.queue_cip i)[j]? = some CPEvent.rsIσ →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      ¬(p.parent.shared_state i = Bstate.I) →
      (∀ k, k ≠ i → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t7 p
  /-- from `downgrade_from_M_rq2` on `q ≠ i` creating `¬ shared_state q = M` (riga `q` a `M`
  prima del passo; se non era a `M` il predecessore è in `A` per `t7`). -/
  | n4 (p : MSIState n) (q i : Fin n) (j j₁ j₂ : Nat) :
      q ≠ i →
      (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      p.parent.shared_state q = Bstate.M →
      (∀ k, k ≠ q → ¬(p.parent.shared_state k = Bstate.M)) →
      ¬((p.caches i).state = Bstate.I) →
      Pre_t7 p
  /-- from `upgrade_from_I_rs v` on `i` creating `(caches i).state = M` (≠ `I`). -/
  | n5 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t7 p
  /-- from `upgrade_from_I_rsS v` on `i` creating `(caches i).state = S` (≠ `I`). -/
  | n6 (p : MSIState n) (i : Fin n) (j j₁ j₂ : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      j₁ ≠ j₂ →
      (p.parent.queue_cip i)[j₁]? = some CPEvent.rqS →
      (p.parent.queue_cip i)[j₂]? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t7 p

/-- **Nessun predecessore nuovo di `t7` è raggiungibile.** -/
theorem Pre_t7_unreachable {n} {p : MSIState n} (h : Pre_t7 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j j₁ j₂ v hmsg _ _ _ _ _ hc =>
    cases hst : (p.caches i).state with
    | M => exact not_reachable_of_M hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
    | S => exact not_reachable_of_S hst (Or.inl (muMsgs_ne_zero_of_rsIμ hmsg))
    | I => exact absurd hst hc
  | n2 q i j j₁ j₂ v _ _ _ _ _ hI _ _ hc => exact not_reachable_of_notI_rowI hc hI
  | n3 i j j₁ j₂ hmsg _ _ _ _ _ hc =>
    cases hst : (p.caches i).state with
    | M => exact not_reachable_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
    | S => exact not_reachable_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hmsg)))
    | I => exact absurd hst hc
  | n4 q i j j₁ j₂ _ _ _ _ _ hI _ _ hc => exact not_reachable_of_notI_rowI hc hI
  | n5 i j j₁ j₂ v _ hj _ _ _ hI _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hI]; intro h; cases h)
  | n6 i j j₁ j₂ v _ hj _ _ _ hI _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj) (by rw [hI]; intro h; cases h)

/-! ## Lemmi di trasporto all'indietro (un passo) -/

namespace BackT7

theorem getElem?_of_append_singleton {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [b])[j]? = some a) (hne : a ≠ b) : l[j]? = some a := by
  by_cases hj : j < l.length
  · rwa [List.getElem?_append_left hj] at h
  · exfalso
    rw [List.getElem?_append_right (by omega)] at h
    cases hk : j - l.length with
    | zero => rw [hk] at h; simp at h; exact hne h.symm
    | succ m => rw [hk] at h; simp at h

theorem getElem?_of_eraseIdx {α} {l : List α} {a : α} {j k : Nat}
    (h : (l.eraseIdx j)[k]? = some a) : ∃ k' : Nat, l[k']? = some a := by
  by_cases hk : k < j
  · exact ⟨k, by rwa [List.getElem?_eraseIdx_of_lt hk] at h⟩
  · exact ⟨k + 1, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h⟩

/-- Un messaggio nella coda `queue_cip k` dopo che un passo del parent ha tolto una posizione
dalla coda di `q` era già nella coda di `k` prima del passo. -/
theorem cip_erase_back {n} {f : Fin n → List CPEvent} {q k : Fin n} {j j' : Nat} {a : CPEvent}
    (h : (update_Fin q ((f q).eraseIdx j) f k)[j']? = some a) : ∃ j'' : Nat, (f k)[j'']? = some a := by
  by_cases hk : q = k
  · subst hk; rw [update_Fin_gss] at h; exact getElem?_of_eraseIdx h
  · rw [update_Fin_gso _ _ _ _ hk] at h; exact ⟨_, h⟩

/-- Un passo esterno non tocca stati delle cache, righe, e (con `synced`) code `queue_cip`. -/
theorem ext_back {n} {p s : MSIState n} {e} (hsync : synced p) (h : msi_step_external p e s) :
    (∀ k, (s.caches k).state = (p.caches k).state)
      ∧ s.parent.shared_state = p.parent.shared_state
      ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) := by
  cases h with
  | cache e cache' q hc =>
    refine ⟨?_, rfl, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]; rw [(hsync k).1]; cases hc <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Un passo di cache non tocca le righe del parent. -/
theorem cache_rows_back {n} {p s : MSIState n} {ce q}
    (h : msi_step_internal p (.cache ce q) s) : s.parent.shared_state = p.parent.shared_state := by
  cases h; rfl

/-- Chi crea "cache `i` non in `I`": solo la presa di un grant (`rsM` o `rsS`) da parte di `i`,
che non tocca le code `queue_cip`. -/
theorem cache_state_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (i : Fin n) (hc : ¬ (s.caches i).state = Bstate.I) :
    ¬ (p.caches i).state = Bstate.I ∨
    ((p.caches i).state = Bstate.I ∧ (∀ k, s.parent.queue_cip k = p.parent.queue_cip k) ∧
      ((∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v))
        ∨ (∃ (j : Nat) (v : Value), ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v)))) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : i = q
    · subst hk
      simp only [update_Fin_gss] at hc
      have hcip : ∀ k, cache'.queue_cp = (p.caches i).queue_cp →
          (update_Fin i cache'.queue_cp p.parent.queue_cip) k = p.parent.queue_cip k := by
        intro k hq
        by_cases hk : k = i
        · subst hk; rw [update_Fin_gss, hq, (hsync k).1]
        · rw [update_Fin_gso2 _ _ _ _ hk]
      cases hstep with
      | rq_data_not_available hM => exact absurd rfl hc
      | rq_data_not_available1 hS => exact absurd rfl hc
      | upgrade_from_I_rq hI => exact absurd hI hc
      | upgrade_from_I_rq1 hI => exact absurd hI hc
      | upgrade_from_I_rs v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inl ⟨j, v, hj⟩⟩
      | upgrade_from_I_rsS v j hj hI =>
        exact Or.inr ⟨hI, fun k => hcip k rfl, Or.inr ⟨j, v, hj⟩⟩
      | downgrade_from_M_rs j hj hM => exact absurd rfl hc
      | downgrade_from_M_rs1 j hj hS => exact absurd rfl hc
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hc

/-- Chi crea una richiesta (`rqM` o `rqS`) in `queue_cip k`: solo la cache `k` stessa, che è in
`I` prima e dopo il passo. -/
theorem cip_back {n} {p s : MSIState n} {ce q} (hsync : synced p)
    (h : msi_step_internal p (.cache ce q) s) (k : Fin n) (j : Nat) (a : CPEvent)
    (ha : a = CPEvent.rqM ∨ a = CPEvent.rqS)
    (hm : (s.parent.queue_cip k)[j]? = some a) :
    (p.parent.queue_cip k)[j]? = some a
      ∨ ((p.caches k).state = Bstate.I ∧ (s.caches k).state = Bstate.I) := by
  cases h with
  | cache cache' q e hstep =>
    by_cases hk : k = q
    · subst hk
      simp only [update_Fin_gss] at hm ⊢
      rw [(hsync k).1]
      cases hstep with
      | rq_data_not_available hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | rq_data_not_available1 hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | upgrade_from_I_rq hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rq1 hI => exact Or.inr ⟨hI, hI⟩
      | upgrade_from_I_rs v j hj hI => exact Or.inl hm
      | upgrade_from_I_rsS v j hj hI => exact Or.inl hm
      | downgrade_from_M_rs j hj hM =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
      | downgrade_from_M_rs1 j hj hS =>
        exact Or.inl (getElem?_of_append_singleton hm (by rcases ha with rfl | rfl <;> intro h <;> cases h))
    · left
      simpa only [update_Fin_gso2 _ _ _ _ hk] using hm

/-- Inversione di un passo del parent: non tocca gli stati delle cache, ed è di una di cinque
forme (rilascio `M`, rilascio `S`, una riga a `M` dopo il passo, grant di `S`, invalidate di una
riga a `S`). -/
theorem parent_back {n} {p s : MSIState n} {pe} (h : msi_step_internal p (.parent pe) s) :
    (∀ k, (s.caches k).state = (p.caches k).state) ∧
    ((∃ (q : Fin n) (j : Nat) (v : Value), (p.parent.queue_cip q)[j]? = some (CPEvent.rsIμ v) ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rsIσ ∧
        s.parent.shared_state = update_Fin q Bstate.I p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, s.parent.shared_state q = Bstate.M)
    ∨ (∃ (q : Fin n) (j : Nat), (p.parent.queue_cip q)[j]? = some CPEvent.rqS ∧
        p.parent.shared_state q = Bstate.I ∧ (∀ k, ¬ p.parent.shared_state k = Bstate.M) ∧
        s.parent.shared_state = update_Fin q Bstate.S p.parent.shared_state ∧
        s.parent.queue_cip = update_Fin q ((p.parent.queue_cip q).eraseIdx j) p.parent.queue_cip)
    ∨ (∃ q, p.parent.shared_state q = Bstate.S ∧ s.parent.shared_state = p.parent.shared_state ∧
        s.parent.queue_cip = p.parent.queue_cip)) := by
  cases h with
  | parent_no_queue parent' e i hp => cases hp
  | parent_upd_queue parent' e q hp =>
    refine ⟨?_, ?_⟩
    · intro k
      by_cases hk : k = q
      · subst hk; simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · cases hp
      · exact Or.inl ⟨_, _, _, ‹_›, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨q, by simp only [update_Fin_gss]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, ‹_›, ‹_›, ‹_›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ‹p.parent.shared_state q = Bstate.S›, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨q, ‹p.parent.shared_state q = Bstate.M›⟩))

/-- Due posizioni diverse dopo `eraseIdx` vengono da due posizioni diverse prima. -/
theorem two_getElem?_of_eraseIdx {α} {l : List α} {a b : α} {j k₁ k₂ : Nat} (hne : k₁ ≠ k₂)
    (h₁ : (l.eraseIdx j)[k₁]? = some a) (h₂ : (l.eraseIdx j)[k₂]? = some b) :
    ∃ k₁' k₂' : Nat, k₁' ≠ k₂' ∧ l[k₁']? = some a ∧ l[k₂']? = some b := by
  by_cases hk₁ : k₁ < j <;> by_cases hk₂ : k₂ < j
  · exact ⟨k₁, k₂, hne, by rwa [List.getElem?_eraseIdx_of_lt hk₁] at h₁,
      by rwa [List.getElem?_eraseIdx_of_lt hk₂] at h₂⟩
  · exact ⟨k₁, k₂ + 1, by omega, by rwa [List.getElem?_eraseIdx_of_lt hk₁] at h₁,
      by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h₂⟩
  · exact ⟨k₁ + 1, k₂, by omega, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h₁,
      by rwa [List.getElem?_eraseIdx_of_lt hk₂] at h₂⟩
  · exact ⟨k₁ + 1, k₂ + 1, by omega, by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h₁,
      by rwa [List.getElem?_eraseIdx_of_ge (by omega)] at h₂⟩

end BackT7


open BackT7

/-- **Passo indietro interno su `t7`**: ogni predecessore `synced` di uno stato di `t7` è in `A`
oppure in `Pre_t7`. -/
theorem back_t7_int {n} {p s : MSIState n} {e : MSIInternalEvent n}
    (hsync : synced p) (hstep : msi_step_internal p e s)
    (i : Fin n) (j₁ j₂ : Nat)
    (hne : j₁ ≠ j₂)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rqS)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M))
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t7 p := by
  cases e with
  | intro => cases hstep
  | cache ce q =>
    have hrows := cache_rows_back hstep
    rw [hrows] at hI hnoM
    rcases cache_state_back hsync hstep i hc with hc' | ⟨hIc, hq, hrs | hrs⟩
    · -- la cache `i` non era in `I`: i suoi due `rqS` non possono essere appena stati creati
      rcases cip_back hsync hstep _ _ _ (Or.inr rfl) h₁ with h₁' | ⟨_, h⟩
      · rcases cip_back hsync hstep _ _ _ (Or.inr rfl) h₂ with h₂' | ⟨_, h⟩
        · exact Or.inl (A.t7 p i j₁ j₂ hne h₁' h₂' hI hnoM hc')
        · exact absurd h hc
      · exact absurd h hc
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t7.n5 p i j j₁ j₂ v hIc hj hne h₁ h₂ hI hnoM)
    · rw [hq] at h₁ h₂
      obtain ⟨j, v, hj⟩ := hrs
      exact Or.inr (Pre_t7.n6 p i j j₁ j₂ v hIc hj hne h₁ h₂ hI hnoM)
  | parent pe =>
    obtain ⟨hst, hD⟩ := parent_back hstep
    rw [hst] at hc
    rcases hD with ⟨q, j, v, hmsg, hrow, hq⟩ | ⟨q, j, hmsg, hrow, hq⟩ | ⟨q, hM⟩
        | ⟨q, j, hmsg, hqI, hpnoM, hrow, hq⟩ | ⟨q, hS, hrow, hq⟩
    · -- `downgrade_from_M_rq1 v` su `q`
      rw [hq] at h₁ h₂
      have hrows : ∀ k, k ≠ q → ¬ p.parent.shared_state k = Bstate.M := by
        intro k hk; have := hnoM k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqi : q = i
      · subst hqi
        rw [update_Fin_gss] at h₁ h₂
        obtain ⟨j₁', j₂', hne', h₁', h₂'⟩ := two_getElem?_of_eraseIdx hne h₁ h₂
        by_cases hqI : p.parent.shared_state q = Bstate.I
        · refine Or.inl (A.t2 p q q j j₁' v hmsg h₁' hqI ?_)
          intro k; by_cases hk : k = q
          · subst hk; rw [hqI]; intro h; cases h
          · exact hrows k hk
        · exact Or.inr (Pre_t7.n1 p q j j₁' j₂' v hmsg hne' h₁' h₂' hqI hrows hc)
      · rw [update_Fin_gso _ _ _ _ hqi] at h₁ h₂
        rw [hrow, update_Fin_gso _ _ _ _ hqi] at hI
        by_cases hqM : p.parent.shared_state q = Bstate.M
        · exact Or.inr (Pre_t7.n2 p q i j j₁ j₂ v hqi hmsg hne h₁ h₂ hI hqM hrows hc)
        · refine Or.inl (A.t7 p i j₁ j₂ hne h₁ h₂ hI ?_ hc)
          intro k; by_cases hk : k = q
          · subst hk; exact hqM
          · exact hrows k hk
    · -- `downgrade_from_M_rq2` su `q`
      rw [hq] at h₁ h₂
      have hrows : ∀ k, k ≠ q → ¬ p.parent.shared_state k = Bstate.M := by
        intro k hk; have := hnoM k; rwa [hrow, update_Fin_gso2 _ _ _ _ hk] at this
      by_cases hqi : q = i
      · subst hqi
        rw [update_Fin_gss] at h₁ h₂
        obtain ⟨j₁', j₂', hne', h₁', h₂'⟩ := two_getElem?_of_eraseIdx hne h₁ h₂
        by_cases hqI : p.parent.shared_state q = Bstate.I
        · refine Or.inl (A.t7 p q j₁' j₂' hne' h₁' h₂' hqI ?_ hc)
          intro k; by_cases hk : k = q
          · subst hk; rw [hqI]; intro h; cases h
          · exact hrows k hk
        · exact Or.inr (Pre_t7.n3 p q j j₁' j₂' hmsg hne' h₁' h₂' hqI hrows hc)
      · rw [update_Fin_gso _ _ _ _ hqi] at h₁ h₂
        rw [hrow, update_Fin_gso _ _ _ _ hqi] at hI
        by_cases hqM : p.parent.shared_state q = Bstate.M
        · exact Or.inr (Pre_t7.n4 p q i j j₁ j₂ hqi hmsg hne h₁ h₂ hI hqM hrows hc)
        · refine Or.inl (A.t7 p i j₁ j₂ hne h₁ h₂ hI ?_ hc)
          intro k; by_cases hk : k = q
          · subst hk; exact hqM
          · exact hrows k hk
    · -- una riga a `M` dopo il passo (grant di `M`, invalidate di una riga `M`): impossibile
      exact absurd hM (hnoM q)
    · -- grant di `S` a `q`: `q ≠ i`, e il predecessore è ancora in `t7`
      by_cases hqi : q = i
      · subst hqi; rw [hrow, update_Fin_gss] at hI; cases hI
      · rw [hq, update_Fin_gso _ _ _ _ hqi] at h₁ h₂
        rw [hrow, update_Fin_gso _ _ _ _ hqi] at hI
        exact Or.inl (A.t7 p i j₁ j₂ hne h₁ h₂ hI hpnoM hc)
    · -- invalidate di una riga `S`: non tocca i campi
      rw [hq] at h₁ h₂; rw [hrow] at hI hnoM
      exact Or.inl (A.t7 p i j₁ j₂ hne h₁ h₂ hI hnoM hc)

/-- **Passo indietro esterno su `t7`**: un passo esterno non tocca nessun campo fissato. -/
theorem back_t7_ext {n} {p s : MSIState n} {e : MSIExternalEvent n}
    (hsync : synced p) (hstep : msi_step_external p e s)
    (i : Fin n) (j₁ j₂ : Nat)
    (hne : j₁ ≠ j₂)
    (h₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rqS)
    (h₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS)
    (hI : s.parent.shared_state i = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M))
    (hc : ¬((s.caches i).state = Bstate.I)) :
    A p ∨ Pre_t7 p := by
  obtain ⟨hst, hrows, hq⟩ := ext_back hsync hstep
  rw [hst] at hc; rw [hq] at h₁ h₂; rw [hrows] at hI hnoM
  exact Or.inl (A.t7 p i j₁ j₂ hne h₁ h₂ hI hnoM hc)


end ABack.T7


namespace ABack.T8

/-! # Passo indietro sul costruttore `t8` di `A`

`t8 s i k j v`: `(s.caches i).state = I`, `rsM v` in `(s.caches i).queue_pc` alla posizione `j`,
`i ≠ k`, riga `k` non a `I`.

`Pre_t8`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti da
`A`. -/


inductive Pre_t8 {n : Nat} : MSIState n → Prop where
  /-- from `rq_data_not_available` on `i` (and `downgrade_from_M_rs` on `i`, sub-case with an
  `rqIμ` in `queue_pc` and the position of `rsM v` shifted) creating `(caches i).state = I` -/
  | n1 (p : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t8 p
  /-- from `rq_data_not_available1` on `i` (and `downgrade_from_M_rs1` on `i`, sub-case with an
  `rqIσ` in `queue_pc` and the position of `rsM v` shifted) creating `(caches i).state = I` -/
  | n2 (p : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t8 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k ≠ I` (row `k := M`) -/
  | n3 (p : MSIState n) (i k : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t8 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `k` creating `shared_state k ≠ I` (row `k := S`) -/
  | n4 (p : MSIState n) (i k : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqS →
      p.parent.shared_state k = Bstate.I →
      (∀ k', ¬(p.parent.shared_state k' = Bstate.M)) →
      Pre_t8 p

/-- Nessun predecessore nuovo di `t8` è raggiungibile. -/
theorem Pre_t8_unreachable {n} {p : MSIState n} (h : Pre_t8 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j v hM _ hne hk => exact not_reachable_of_M_rowJ hne hM hk
  | n2 i k j v hS hj _ _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_S hS (Or.inl (muMsgs_ne_zero_of_rsM hj))
  | n3 i k j j' v _ hj _ _ hall =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hall i]; intro h; cases h)
  | n4 i k j j' v _ hj _ _ _ hnoM =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (hnoM i)

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rw [List.getElem?_append] at h
  split at h
  · exact h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact absurd rfl hne
    · cases h

set_option hygiene false in
/-- Caso di un invalidate del parent (accoda `rqIμ`/`rqIσ` a `q`): non crea campi di `t8`. -/
local macro "inv_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     rw [(hsync q).2] at h2'
     exact Or.inl (.t8 _ q k j v h1 h2' h3 h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
     exact Or.inl (.t8 _ i k j v h1 h2 h3 h4)))

theorem back_t8_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j]? = some (PCEvent.rsM v))
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t8 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | rq_data_not_available hM => exact Or.inr (.n1 _ c k j v hM h2 h3 h4)
      | rq_data_not_available1 hS => exact Or.inr (.n2 _ c k j v hS h2 h3 h4)
      | upgrade_from_I_rq hI => exact Or.inl (.t8 _ c k j v hI h2 h3 h4)
      | upgrade_from_I_rq1 hI => exact Or.inl (.t8 _ c k j v hI h2 h3 h4)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM =>
        simp only [List.getElem?_eraseIdx] at h2
        split at h2
        · exact Or.inr (.n1 _ c k j v hM h2 h3 h4)
        · exact Or.inr (.n1 _ c k (j + 1) v hM h2 h3 h4)
      | downgrade_from_M_rs1 j' hj' hS =>
        simp only [List.getElem?_eraseIdx] at h2
        split at h2
        · exact Or.inr (.n2 _ c k j v hS h2 h3 h4)
        · exact Or.inr (.n2 _ c k (j + 1) v hS h2 h3 h4)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t8 _ i k j v h1 h2 h3 h4)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti i campi fissati non sono creati
      have hqk : ¬ q = k := by
        intro h; subst h; exact h4 (by simp [update_Fin_gss])
      have h4' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h4
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2
        rw [(hsync q).2] at h2
        exact Or.inl (.t8 _ q k j v h1 h2 h3 h4')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inl (.t8 _ i k j v h1 h2 h3 h4')
    | downgrade_from_M_rq2 _ j' hj' =>
      have hqk : ¬ q = k := by
        intro h; subst h; exact h4 (by simp [update_Fin_gss])
      have h4' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h4
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2
        rw [(hsync q).2] at h2
        exact Or.inl (.t8 _ q k j v h1 h2 h3 h4')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inl (.t8 _ i k j v h1 h2 h3 h4')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k ≠ I` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h3 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inr (.n3 _ i q j j' v h1 h2 h3 hj' hall)
      · exact absurd (by simp [update_Fin_gso _ _ _ _ hqk, hall k]) h4
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      by_cases hqi : q = i
      · subst hqi
        have hqk : ¬ q = k := h3
        simp only [update_Fin_gss] at h1 h2
        have h4' : ¬ p.parent.shared_state k = Bstate.I := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h4
        have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
        rw [(hsync q).2] at h2'
        exact Or.inl (.t8 _ q k j v h1 h2' h3 h4')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        by_cases hqk : q = k
        · subst hqk
          exact Or.inr (.n4 _ i q j j' v h1 h2 h3 hj' hI hnoM)
        · have h4' : ¬ p.parent.shared_state k = Bstate.I := by
            simpa [update_Fin_gso _ _ _ _ hqk] using h4
          exact Or.inl (.t8 _ i k j v h1 h2 h3 h4')
    | upgrade_to_M_invalid_all r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => inv_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => inv_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: nessuna regola esterna crea un campo fissato di `t8`. -/
theorem back_t8_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j]? = some (PCEvent.rsM v))
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t8 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | ld_rq => exact Or.inl (.t8 _ c k j v h1 h2 h3 h4)
      | st_rq w => exact Or.inl (.t8 _ c k j v h1 h2 h3 h4)
      | ld_rq_data_available1 rst hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t8 _ i k j v h1 h2 h3 h4)


end ABack.T8


namespace ABack.T9

/-! # Passo indietro sul costruttore `t9` di `A`

`t9 s i k j v`: `(s.caches i).state = I`, `rsS v` in `(s.caches i).queue_pc` alla posizione `j`,
`v = s.parent.value`, `i ≠ k`, riga `k` a `M`.

`Pre_t9`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti da
`A`. -/


inductive Pre_t9 {n : Nat} : MSIState n → Prop where
  /-- from `rq_data_not_available` on `i` (and `downgrade_from_M_rs` on `i`, sub-case with an
  `rqIμ` in `queue_pc` and the position of `rsS v` shifted) creating `(caches i).state = I` -/
  | n1 (p : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      v = p.parent.value →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      Pre_t9 p
  /-- from `rq_data_not_available1` on `i` (and `downgrade_from_M_rs1` on `i`, sub-case with an
  `rqIσ` in `queue_pc` and the position of `rsS v` shifted) creating `(caches i).state = I` -/
  | n2 (p : MSIState n) (i k : Fin n) (j : Nat) (v : Value) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      v = p.parent.value →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      Pre_t9 p
  /-- from `downgrade_from_M_rq1 v` on `q ≠ k` creating `v = parent.value` (the rule writes
  `parent.value := v`; the old `parent.value` is free) -/
  | n3 (p : MSIState n) (i k q : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      q ≠ k →
      (p.parent.queue_cip q)[j']? = some (CPEvent.rsIμ v) →
      Pre_t9 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k = M` -/
  | n4 (p : MSIState n) (i k : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      v = p.parent.value →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t9 p

/-- Nessun predecessore nuovo di `t9` è raggiungibile. -/
theorem Pre_t9_unreachable {n} {p : MSIState n} (h : Pre_t9 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j v hM _ _ hne hk =>
    exact not_reachable_of_M_rowJ hne hM (by rw [hk]; intro h; cases h)
  | n2 i k j v hS _ _ hne hk => exact not_reachable_of_S_rowM hne hS hk
  | n3 i k q j j' v _ hj hne hk _ _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_rowM hne (sigMsgs_ne_zero_of_rsS hj) hk
  | n4 i k j j' v _ hj _ _ _ hall =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj) (by rw [hall i]; intro h; cases h)

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
theorem getElem?_of_append_singleton_ne' {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rw [List.getElem?_append] at h
  split at h
  · exact h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact absurd rfl hne
    · cases h

set_option hygiene false in
/-- Caso di un invalidate del parent (accoda `rqIμ`/`rqIσ` a `q`): non crea campi di `t9`. -/
local macro "inv_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2
     have h2' := getElem?_of_append_singleton_ne' h2 (by intro h; cases h)
     rw [(hsync q).2] at h2'
     exact Or.inl (.t9 _ q k j v h1 h2' h3 h4 h5)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
     exact Or.inl (.t9 _ i k j v h1 h2 h3 h4 h5)))

/-- Passo interno: il predecessore di uno stato di `t9` è in `A` oppure in `Pre_t9`. -/
theorem back_t9_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j]? = some (PCEvent.rsS v))
    (h3 : v = s.parent.value)
    (h4 : i ≠ k)
    (h5 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t9 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | rq_data_not_available hM => exact Or.inr (.n1 _ c k j v hM h2 h3 h4 h5)
      | rq_data_not_available1 hS => exact Or.inr (.n2 _ c k j v hS h2 h3 h4 h5)
      | upgrade_from_I_rq hI => exact Or.inl (.t9 _ c k j v hI h2 h3 h4 h5)
      | upgrade_from_I_rq1 hI => exact Or.inl (.t9 _ c k j v hI h2 h3 h4 h5)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM =>
        simp only [List.getElem?_eraseIdx] at h2
        split at h2
        · exact Or.inr (.n1 _ c k j v hM h2 h3 h4 h5)
        · exact Or.inr (.n1 _ c k (j + 1) v hM h2 h3 h4 h5)
      | downgrade_from_M_rs1 j' hj' hS =>
        simp only [List.getElem?_eraseIdx] at h2
        split at h2
        · exact Or.inr (.n2 _ c k j v hS h2 h3 h4 h5)
        · exact Or.inr (.n2 _ c k (j + 1) v hS h2 h3 h4 h5)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t9 _ i k j v h1 h2 h3 h4 h5)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti crea `v = parent.value` (`v' = v`)
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h5
      have h5' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      have h3' : v = v' := h3
      subst h3'
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2
        rw [(hsync q).2] at h2
        exact Or.inr (.n3 _ q k q j j' v h1 h2 h4 h5' hqk hj')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inr (.n3 _ i k q j j' v h1 h2 h4 h5' hqk hj')
    | downgrade_from_M_rq2 _ j' hj' =>
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h5
      have h5' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2
        rw [(hsync q).2] at h2
        exact Or.inl (.t9 _ q k j v h1 h2 h3 h4 h5')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inl (.t9 _ i k j v h1 h2 h3 h4 h5')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k = M` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h4 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inr (.n4 _ i q j j' v h1 h2 h3 h4 hj' hall)
      · have h5' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        rw [hall k] at h5'; cases h5'
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      -- grant di `S`: impossibile come ultimo passo (riga `k := S`, oppure riga `k = M` già prima)
      by_cases hqk : q = k
      · subst hqk; simp [update_Fin_gss] at h5
      · have h5' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        exact absurd h5' (hnoM k)
    | upgrade_to_M_invalid_all r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => inv_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => inv_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: nessuna regola esterna crea un campo fissato di `t9`. -/
theorem back_t9_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j]? = some (PCEvent.rsS v))
    (h3 : v = s.parent.value)
    (h4 : i ≠ k)
    (h5 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t9 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | ld_rq => exact Or.inl (.t9 _ c k j v h1 h2 h3 h4 h5)
      | st_rq w => exact Or.inl (.t9 _ c k j v h1 h2 h3 h4 h5)
      | ld_rq_data_available1 rst hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t9 _ i k j v h1 h2 h3 h4 h5)


end ABack.T9


namespace ABack.T10

/-! # Passo indietro sul costruttore `t10` di `A`

`t10 s i j₁ j₂ v₁ v₂`: `(s.caches i).state = I`, `rsM v₁` in `(s.caches i).queue_pc` alla
posizione `j₁`, `rsM v₂` alla posizione `j₂`, `j₁ ≠ j₂`.

`Pre_t10`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. -/


inductive Pre_t10 {n : Nat} : MSIState n → Prop where
  /-- from `rq_data_not_available` on `i` (and `downgrade_from_M_rs` on `i`, sub-case with an
  `rqIμ` in `queue_pc` and the positions of the two `rsM` shifted) creating
  `(caches i).state = I` -/
  | n1 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsM v₂) →
      j₁ ≠ j₂ →
      Pre_t10 p
  /-- from `rq_data_not_available1` on `i` (and `downgrade_from_M_rs1` on `i`, sub-case with an
  `rqIσ` in `queue_pc` and the positions of the two `rsM` shifted) creating
  `(caches i).state = I` -/
  | n2 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsM v₂) →
      j₁ ≠ j₂ →
      Pre_t10 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `i` creating one of the two `rsM` in
  `(caches i).queue_pc` (the last position; its value is `p.parent.value`): the other `rsM v`
  was already there -/
  | n3 (p : MSIState n) (i : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsM v) →
      (p.parent.queue_cip i)[j']? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t10 p

/-- Nessun predecessore nuovo di `t10` è raggiungibile. -/
theorem Pre_t10_unreachable {n} {p : MSIState n} (h : Pre_t10 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j₁ j₂ v₁ v₂ hM hj₁ _ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_M hM (Or.inl (muMsgs_ne_zero_of_rsM hj₁))
  | n2 i j₁ j₂ v₁ v₂ hS hj₁ _ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_S hS (Or.inl (muMsgs_ne_zero_of_rsM hj₁))
  | n3 i j j' v _ hj _ hall =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj) (by rw [hall i]; intro h; cases h)

/-- Se `b` sta in `l ++ [a]` alla posizione `j`, o stava già in `l`, o è l'ultimo (`a = b`). -/
private theorem getElem?_append_singleton_cases {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) : l[j]? = some b ∨ (j = l.length ∧ a = b) := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact Or.inr ⟨by omega, rfl⟩
    · cases h

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
private theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rcases getElem?_append_singleton_cases h with h | ⟨_, h⟩
  · exact h
  · exact absurd h hne

/-- La posizione prima di `eraseIdx j'` dell'elemento che dopo sta in `j`. -/
private def unshift (j' j : Nat) : Nat := if j < j' then j else j + 1

private theorem getElem?_unshift {α} {l : List α} {b : α} {j j' : Nat}
    (h : (l.eraseIdx j')[j]? = some b) : l[unshift j' j]? = some b := by
  simp only [List.getElem?_eraseIdx] at h
  unfold unshift
  split
  · simpa [*] using h
  · simpa [*] using h

private theorem unshift_ne {j' j₁ j₂ : Nat} (h : j₁ ≠ j₂) : unshift j' j₁ ≠ unshift j' j₂ := by
  unfold unshift; split <;> split <;> omega

set_option hygiene false in
/-- Caso di un passo del parent su `q` che non accoda un `rsM`: non crea campi di `t10`. -/
local macro "nocreate_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     have h3' := getElem?_of_append_singleton_ne h3 (by intro h; cases h)
     rw [(hsync q).2] at h2' h3'
     exact Or.inl (.t10 _ q j₁ j₂ v₁ v₂ h1 h2' h3' h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t10 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)))

set_option hygiene false in
/-- Caso di un downgrade del parent su `q` (cancella da `queue_cip q`, riga `q := I`): non crea
campi di `t10`. -/
local macro "downgrade_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     rw [(hsync q).2] at h2 h3
     exact Or.inl (.t10 _ q j₁ j₂ v₁ v₂ h1 h2 h3 h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t10 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)))

/-- Un passo interno indietro da `t10`: il predecessore è in `A` o in `Pre_t10`. -/
theorem back_t10_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsM v₂))
    (h4 : j₁ ≠ j₂) :
    A p ∨ Pre_t10 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => exact Or.inr (.n1 _ c j₁ j₂ v₁ v₂ hM h2 h3 h4)
      | rq_data_not_available1 hS => exact Or.inr (.n2 _ c j₁ j₂ v₁ v₂ hS h2 h3 h4)
      | upgrade_from_I_rq hI => exact Or.inl (.t10 _ c j₁ j₂ v₁ v₂ hI h2 h3 h4)
      | upgrade_from_I_rq1 hI => exact Or.inl (.t10 _ c j₁ j₂ v₁ v₂ hI h2 h3 h4)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM =>
        exact Or.inr (.n1 _ c _ _ v₁ v₂ hM (getElem?_unshift h2) (getElem?_unshift h3)
          (unshift_ne h4))
      | downgrade_from_M_rs1 j' hj' hS =>
        exact Or.inr (.n2 _ c _ _ v₁ v₂ hS (getElem?_unshift h2) (getElem?_unshift h3)
          (unshift_ne h4))
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t10 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' => downgrade_case
    | downgrade_from_M_rq2 _ j' hj' => downgrade_case
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M` a `q`: accoda `rsM p.parent.value` in fondo a `queue_pci q`
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2 h3
        rcases getElem?_append_singleton_cases h2 with h2' | ⟨hl₁, _⟩
        · rcases getElem?_append_singleton_cases h3 with h3' | ⟨hl₂, _⟩
          · -- i due `rsM` c'erano già
            rw [(hsync q).2] at h2' h3'
            exact Or.inl (.t10 _ q j₁ j₂ v₁ v₂ h1 h2' h3' h4)
          · -- `rsM v₂` è quello appena accodato
            rw [(hsync q).2] at h2'
            exact Or.inr (.n3 _ q j₁ j' v₁ h1 h2' hj' hall)
        · rcases getElem?_append_singleton_cases h3 with h3' | ⟨hl₂, _⟩
          · -- `rsM v₁` è quello appena accodato
            rw [(hsync q).2] at h3'
            exact Or.inr (.n3 _ q j₂ j' v₂ h1 h3' hj' hall)
          · exact absurd (hl₁.trans hl₂.symm) h4
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inl (.t10 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM => nocreate_case
    | upgrade_to_M_invalid_all r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => nocreate_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => nocreate_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: nessuna regola esterna crea un campo fissato di `t10`. -/
theorem back_t10_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsM v₂))
    (h4 : j₁ ≠ j₂) :
    A p ∨ Pre_t10 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq => exact Or.inl (.t10 _ c j₁ j₂ v₁ v₂ h1 h2 h3 h4)
      | st_rq w => exact Or.inl (.t10 _ c j₁ j₂ v₁ v₂ h1 h2 h3 h4)
      | ld_rq_data_available1 rst hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t10 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)


end ABack.T10


namespace ABack.T11

/-! # Passo indietro sul costruttore `t11` di `A`

`t11 s i j₁ j₂ v₁ v₂`: `(s.caches i).state = I`, `rsM v₁` in `(s.caches i).queue_pc` alla
posizione `j₁`, `rsS v₂` alla posizione `j₂`.

`Pre_t11`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. -/


inductive Pre_t11 {n : Nat} : MSIState n → Prop where
  /-- from `rq_data_not_available` on `i` (and `downgrade_from_M_rs` on `i`, sub-case with an
  `rqIμ` in `queue_pc` and the positions of `rsM`/`rsS` shifted) creating
  `(caches i).state = I` -/
  | n1 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      Pre_t11 p
  /-- from `rq_data_not_available1` on `i` (and `downgrade_from_M_rs1` on `i`, sub-case with an
  `rqIσ` in `queue_pc` and the positions of `rsM`/`rsS` shifted) creating
  `(caches i).state = I` -/
  | n2 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      Pre_t11 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `i` creating the `rsM` in `(caches i).queue_pc`
  (the last position; its value is `p.parent.value`): the `rsS v₂` was already there -/
  | n3 (p : MSIState n) (i : Fin n) (j₂ j' : Nat) (v₂ : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      (p.parent.queue_cip i)[j']? = some CPEvent.rqM →
      (∀ k, p.parent.shared_state k = Bstate.I) →
      Pre_t11 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `i` creating the `rsS` in `(caches i).queue_pc`
  (the last position; its value is `p.parent.value`): the `rsM v₁` was already there -/
  | n4 (p : MSIState n) (i : Fin n) (j₁ j' : Nat) (v₁ : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁) →
      (p.parent.queue_cip i)[j']? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t11 p

/-- Nessun predecessore nuovo di `t11` è raggiungibile. -/
theorem Pre_t11_unreachable {n} {p : MSIState n} (h : Pre_t11 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j₁ j₂ v₁ v₂ hM hj₁ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_M hM (Or.inl (muMsgs_ne_zero_of_rsM hj₁))
  | n2 i j₁ j₂ v₁ v₂ hS hj₁ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_S hS (Or.inl (muMsgs_ne_zero_of_rsM hj₁))
  | n3 i j₂ j' v₂ _ hj₂ _ hall =>
    rw [← (hsync i).2] at hj₂
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj₂) (by rw [hall i]; intro h; cases h)
  | n4 i j₁ j' v₁ _ hj₁ _ _ hnoM =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hj₁) (hnoM i)

/-- Se `b` sta in `l ++ [a]` alla posizione `j`, o stava già in `l`, o è l'ultimo (`a = b`). -/
private theorem getElem?_append_singleton_cases {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) : l[j]? = some b ∨ (j = l.length ∧ a = b) := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact Or.inr ⟨by omega, rfl⟩
    · cases h

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
private theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rcases getElem?_append_singleton_cases h with h | ⟨_, h⟩
  · exact h
  · exact absurd h hne

/-- La posizione prima di `eraseIdx j'` dell'elemento che dopo sta in `j`. -/
private def unshift (j' j : Nat) : Nat := if j < j' then j else j + 1

private theorem getElem?_unshift {α} {l : List α} {b : α} {j j' : Nat}
    (h : (l.eraseIdx j')[j]? = some b) : l[unshift j' j]? = some b := by
  simp only [List.getElem?_eraseIdx] at h
  unfold unshift
  split
  · simpa [*] using h
  · simpa [*] using h

set_option hygiene false in
/-- Caso di un invalidate del parent su `q` (accoda `rqIμ`/`rqIσ`): non crea campi di `t11`. -/
local macro "nocreate_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     have h3' := getElem?_of_append_singleton_ne h3 (by intro h; cases h)
     rw [(hsync q).2] at h2' h3'
     exact Or.inl (.t11 _ q j₁ j₂ v₁ v₂ h1 h2' h3')
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)))

set_option hygiene false in
/-- Caso di un downgrade del parent su `q` (cancella da `queue_cip q`, riga `q := I`): non crea
campi di `t11`. -/
local macro "downgrade_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     rw [(hsync q).2] at h2 h3
     exact Or.inl (.t11 _ q j₁ j₂ v₁ v₂ h1 h2 h3)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)))

/-- Un passo interno indietro da `t11`: il predecessore è in `A` o in `Pre_t11`. -/
theorem back_t11_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂)) :
    A p ∨ Pre_t11 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => exact Or.inr (.n1 _ c j₁ j₂ v₁ v₂ hM h2 h3)
      | rq_data_not_available1 hS => exact Or.inr (.n2 _ c j₁ j₂ v₁ v₂ hS h2 h3)
      | upgrade_from_I_rq hI => exact Or.inl (.t11 _ c j₁ j₂ v₁ v₂ hI h2 h3)
      | upgrade_from_I_rq1 hI => exact Or.inl (.t11 _ c j₁ j₂ v₁ v₂ hI h2 h3)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM =>
        exact Or.inr (.n1 _ c _ _ v₁ v₂ hM (getElem?_unshift h2) (getElem?_unshift h3))
      | downgrade_from_M_rs1 j' hj' hS =>
        exact Or.inr (.n2 _ c _ _ v₁ v₂ hS (getElem?_unshift h2) (getElem?_unshift h3))
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' => downgrade_case
    | downgrade_from_M_rq2 _ j' hj' => downgrade_case
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M` a `q`: accoda `rsM p.parent.value` in fondo a `queue_pci q`
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2 h3
        have h3' := getElem?_of_append_singleton_ne h3 (by intro h; cases h)
        rw [(hsync q).2] at h3'
        rcases getElem?_append_singleton_cases h2 with h2' | ⟨_, _⟩
        · -- l'`rsM v₁` c'era già
          rw [(hsync q).2] at h2'
          exact Or.inl (.t11 _ q j₁ j₂ v₁ v₂ h1 h2' h3')
        · -- l'`rsM v₁` è quello appena accodato
          exact Or.inr (.n3 _ q j₂ j' v₂ h1 h3' hj' hall)
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      -- grant di `S` a `q`: accoda `rsS p.parent.value` in fondo a `queue_pci q`
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2 h3
        have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
        rw [(hsync q).2] at h2'
        rcases getElem?_append_singleton_cases h3 with h3' | ⟨_, _⟩
        · -- l'`rsS v₂` c'era già
          rw [(hsync q).2] at h3'
          exact Or.inl (.t11 _ q j₁ j₂ v₁ v₂ h1 h2' h3')
        · -- l'`rsS v₂` è quello appena accodato
          exact Or.inr (.n4 _ q j₁ j' v₁ h1 h2' hj' hI hnoM)
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)
    | upgrade_to_M_invalid_all r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => nocreate_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => nocreate_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: nessuna regola esterna crea un campo fissato di `t11`. -/
theorem back_t11_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsM v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂)) :
    A p ∨ Pre_t11 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq => exact Or.inl (.t11 _ c j₁ j₂ v₁ v₂ h1 h2 h3)
      | st_rq w => exact Or.inl (.t11 _ c j₁ j₂ v₁ v₂ h1 h2 h3)
      | ld_rq_data_available1 rst hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t11 _ i j₁ j₂ v₁ v₂ h1 h2 h3)


end ABack.T11


namespace ABack.T12

/-! # Passo indietro sul costruttore `t12` di `A`

`t12 s i j₁ j₂ v₁ v₂`: `(s.caches i).state = I`, `rsS v₁` in `(s.caches i).queue_pc` alla
posizione `j₁`, `rsS v₂` alla posizione `j₂`, `j₁ ≠ j₂`.

`Pre_t12`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. -/


inductive Pre_t12 {n : Nat} : MSIState n → Prop where
  /-- from `rq_data_not_available` on `i` (and `downgrade_from_M_rs` on `i`, sub-case with an
  `rqIμ` in `queue_pc` and the positions of the two `rsS` shifted) creating
  `(caches i).state = I` -/
  | n1 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsS v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      j₁ ≠ j₂ →
      Pre_t12 p
  /-- from `rq_data_not_available1` on `i` (and `downgrade_from_M_rs1` on `i`, sub-case with an
  `rqIσ` in `queue_pc` and the positions of the two `rsS` shifted) creating
  `(caches i).state = I` -/
  | n2 (p : MSIState n) (i : Fin n) (j₁ j₂ : Nat) (v₁ v₂ : Value) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j₁]? = some (PCEvent.rsS v₁) →
      ((p.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂) →
      j₁ ≠ j₂ →
      Pre_t12 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `i` creating one of the two `rsS` in
  `(caches i).queue_pc` (the last position; its value is `p.parent.value`): the other `rsS v`
  was already there -/
  | n3 (p : MSIState n) (i : Fin n) (j j' : Nat) (v : Value) :
      (p.caches i).state = Bstate.I →
      ((p.caches i).queue_pc)[j]? = some (PCEvent.rsS v) →
      (p.parent.queue_cip i)[j']? = some CPEvent.rqS →
      p.parent.shared_state i = Bstate.I →
      (∀ k, ¬(p.parent.shared_state k = Bstate.M)) →
      Pre_t12 p

/-- Nessun predecessore nuovo di `t12` è raggiungibile. -/
theorem Pre_t12_unreachable {n} {p : MSIState n} (h : Pre_t12 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i j₁ j₂ v₁ v₂ hM hj₁ _ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_M hM (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsS hj₁)))
  | n2 i j₁ j₂ v₁ v₂ hS hj₁ _ _ =>
    rw [← (hsync i).2] at hj₁
    exact not_reachable_of_S hS (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsS hj₁)))
  | n3 i j j' v _ hj _ hI _ =>
    rw [← (hsync i).2] at hj
    exact not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hj) (by rw [hI]; intro h; cases h)

/-- Se `b` sta in `l ++ [a]` alla posizione `j`, o stava già in `l`, o è l'ultimo (`a = b`). -/
private theorem getElem?_append_singleton_cases {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) : l[j]? = some b ∨ (j = l.length ∧ a = b) := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact Or.inr ⟨by omega, rfl⟩
    · cases h

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
private theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rcases getElem?_append_singleton_cases h with h | ⟨_, h⟩
  · exact h
  · exact absurd h hne

/-- La posizione prima di `eraseIdx j'` dell'elemento che dopo sta in `j`. -/
private def unshift (j' j : Nat) : Nat := if j < j' then j else j + 1

private theorem getElem?_unshift {α} {l : List α} {b : α} {j j' : Nat}
    (h : (l.eraseIdx j')[j]? = some b) : l[unshift j' j]? = some b := by
  simp only [List.getElem?_eraseIdx] at h
  unfold unshift
  split
  · simpa [*] using h
  · simpa [*] using h

private theorem unshift_ne {j' j₁ j₂ : Nat} (h : j₁ ≠ j₂) : unshift j' j₁ ≠ unshift j' j₂ := by
  unfold unshift; split <;> split <;> omega

set_option hygiene false in
/-- Caso di un passo del parent su `q` che non accoda un `rsS`: non crea campi di `t12`. -/
local macro "nocreate_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     have h3' := getElem?_of_append_singleton_ne h3 (by intro h; cases h)
     rw [(hsync q).2] at h2' h3'
     exact Or.inl (.t12 _ q j₁ j₂ v₁ v₂ h1 h2' h3' h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t12 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)))

set_option hygiene false in
/-- Caso di un downgrade del parent su `q` (cancella da `queue_cip q`, riga `q := I`): non crea
campi di `t12`. -/
local macro "downgrade_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     rw [(hsync q).2] at h2 h3
     exact Or.inl (.t12 _ q j₁ j₂ v₁ v₂ h1 h2 h3 h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t12 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)))

/-- Un passo interno indietro da `t12`: il predecessore è in `A` o in `Pre_t12`. -/
theorem back_t12_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsS v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂))
    (h4 : j₁ ≠ j₂) :
    A p ∨ Pre_t12 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => exact Or.inr (.n1 _ c j₁ j₂ v₁ v₂ hM h2 h3 h4)
      | rq_data_not_available1 hS => exact Or.inr (.n2 _ c j₁ j₂ v₁ v₂ hS h2 h3 h4)
      | upgrade_from_I_rq hI => exact Or.inl (.t12 _ c j₁ j₂ v₁ v₂ hI h2 h3 h4)
      | upgrade_from_I_rq1 hI => exact Or.inl (.t12 _ c j₁ j₂ v₁ v₂ hI h2 h3 h4)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM =>
        exact Or.inr (.n1 _ c _ _ v₁ v₂ hM (getElem?_unshift h2) (getElem?_unshift h3)
          (unshift_ne h4))
      | downgrade_from_M_rs1 j' hj' hS =>
        exact Or.inr (.n2 _ c _ _ v₁ v₂ hS (getElem?_unshift h2) (getElem?_unshift h3)
          (unshift_ne h4))
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t12 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' => downgrade_case
    | downgrade_from_M_rq2 _ j' hj' => downgrade_case
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall => nocreate_case
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      -- grant di `S` a `q`: accoda `rsS p.parent.value` in fondo a `queue_pci q`
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h1 h2 h3
        rcases getElem?_append_singleton_cases h2 with h2' | ⟨hl₁, _⟩
        · rcases getElem?_append_singleton_cases h3 with h3' | ⟨hl₂, _⟩
          · -- i due `rsS` c'erano già
            rw [(hsync q).2] at h2' h3'
            exact Or.inl (.t12 _ q j₁ j₂ v₁ v₂ h1 h2' h3' h4)
          · -- `rsS v₂` è quello appena accodato
            rw [(hsync q).2] at h2'
            exact Or.inr (.n3 _ q j₁ j' v₁ h1 h2' hj' hI hnoM)
        · rcases getElem?_append_singleton_cases h3 with h3' | ⟨hl₂, _⟩
          · -- `rsS v₁` è quello appena accodato
            rw [(hsync q).2] at h3'
            exact Or.inr (.n3 _ q j₂ j' v₂ h1 h3' hj' hI hnoM)
          · exact absurd (hl₁.trans hl₂.symm) h4
      · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inl (.t12 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)
    | upgrade_to_M_invalid_all r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => nocreate_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => nocreate_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => nocreate_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: nessuna regola esterna crea un campo fissato di `t12`. -/
theorem back_t12_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i : Fin n} {j₁ j₂ : Nat}
    {v₁ v₂ : Value} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.I)
    (h2 : ((s.caches i).queue_pc)[j₁]? = some (PCEvent.rsS v₁))
    (h3 : ((s.caches i).queue_pc)[j₂]? = some (PCEvent.rsS v₂))
    (h4 : j₁ ≠ j₂) :
    A p ∨ Pre_t12 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq => exact Or.inl (.t12 _ c j₁ j₂ v₁ v₂ h1 h2 h3 h4)
      | st_rq w => exact Or.inl (.t12 _ c j₁ j₂ v₁ v₂ h1 h2 h3 h4)
      | ld_rq_data_available1 rst hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t12 _ i j₁ j₂ v₁ v₂ h1 h2 h3 h4)


end ABack.T12


namespace ABack.T13

/-! # Passo indietro sul costruttore `t13` di `A`

`t13 s i k rst`: `(s.caches i).state = M`, `(s.caches i).extqueue.rq = ld_rq :: rst`, `i ≠ k`,
riga `k` non a `I`.

`Pre_t13`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti da
`A` così com'è scritto in `a.lean`. -/


inductive Pre_t13 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k ≠ I` (row `k := M`) -/
  | n1 (p : MSIState n) (i k : Fin n) (j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t13 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `k` creating `shared_state k ≠ I` (row `k := S`) -/
  | n2 (p : MSIState n) (i k : Fin n) (j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqS →
      p.parent.shared_state k = Bstate.I →
      (∀ k', ¬(p.parent.shared_state k' = Bstate.M)) →
      Pre_t13 p
  /-- from external `ld_rq` on `i` (with `extqueue.rq` empty) creating the head
  `(caches i).extqueue.rq = ld_rq :: []` -/
  | n3 (p : MSIState n) (i k : Fin n) :
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = [] →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t13 p

/-- Nessun predecessore nuovo di `t13` è raggiungibile. -/
theorem Pre_t13_unreachable {n} {p : MSIState n} (h : Pre_t13 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j' rst hM _ _ _ hall =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n2 i k j' rst hM _ _ _ _ hnoM =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i)))
  | n3 i k hM _ hne hk => exact not_reachable_of_M_rowJ hne hM hk

/-- Passo interno: l'ultimo passo `p → s` con `s` in `t13`. -/
theorem back_t13_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t13 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v j hj hI => exact Or.inl (.t8 _ c k j v hI hj h3 h4)
      | upgrade_from_I_rsS v j hj hI => cases h1
      | downgrade_from_M_rs j hj hM => cases h1
      | downgrade_from_M_rs1 j hj hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t13 _ i k rst h1 h2 h3 h4)
  | parent_upd_queue parent' pe q hp =>
    -- un passo del parent non tocca né lo stato né la `extqueue` di alcuna cache
    have h1' : (p.caches i).state = Bstate.M := by
      by_cases hqi : q = i
      · subst hqi; simpa [update_Fin_gss] using h1
      · simpa [update_Fin_gso _ _ _ _ hqi] using h1
    have h2' : (p.caches i).extqueue.rq = Event.ld_rq :: rst := by
      by_cases hqi : q = i
      · subst hqi; simpa [update_Fin_gss] using h2
      · simpa [update_Fin_gso _ _ _ _ hqi] using h2
    clear h1 h2
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti la riga `k` non è toccata
      have hqk : ¬ q = k := by
        intro h; subst h; exact h4 (by simp [update_Fin_gss])
      have h4' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h4
      exact Or.inl (.t13 _ i k rst h1' h2' h3 h4')
    | downgrade_from_M_rq2 _ j' hj' =>
      have hqk : ¬ q = k := by
        intro h; subst h; exact h4 (by simp [update_Fin_gss])
      have h4' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h4
      exact Or.inl (.t13 _ i k rst h1' h2' h3 h4')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k ≠ I` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        exact Or.inr (.n1 _ i q j' rst h1' h2' h3 hj' hall)
      · exact absurd (by simp [update_Fin_gso _ _ _ _ hqk, hall k]) h4
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      by_cases hqk : q = k
      · subst hqk
        exact Or.inr (.n2 _ i q j' rst h1' h2' h3 hj' hI hnoM)
      · have h4' : ¬ p.parent.shared_state k = Bstate.I := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h4
        exact Or.inl (.t13 _ i k rst h1' h2' h3 h4')
    | upgrade_to_M_invalid_all r j' hj' hrow => exact Or.inl (.t13 _ i k rst h1' h2' h3 h4)
    | upgrade_to_M_invalid_all1 r j' hj' hrow => exact Or.inl (.t13 _ i k rst h1' h2' h3 h4)
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => exact Or.inl (.t13 _ i k rst h1' h2' h3 h4)
    | upgrade_to_M_invalid_all3 r j' hj' hrow => exact Or.inl (.t13 _ i k rst h1' h2' h3 h4)
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: l'ultimo passo `p → s` con `s` in `t13`. -/
theorem back_t13_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t13 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | ld_rq =>
        -- `rq := rq ++ [ld_rq]`: crea la testa solo se `rq` era vuota
        have h2' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.ld_rq :: rst := h2
        cases hrq : (p.caches c).extqueue.rq with
        | nil => exact Or.inr (.n3 _ c k h1 hrq h3 h4)
        | cons a l =>
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨rfl, _⟩ := h2'
          exact Or.inl (.t13 _ c k l h1 hrq h3 h4)
      | st_rq w =>
        -- `rq := rq ++ [st_rq w]`: non può creare la testa `ld_rq`
        have h2' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h2
        cases hrq : (p.caches c).extqueue.rq with
        | nil => rw [hrq] at h2'; cases h2'
        | cons a l =>
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨rfl, _⟩ := h2'
          exact Or.inl (.t13 _ c k l h1 hrq h3 h4)
      | ld_rq_data_available1 rst0 hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst0 hrq hM =>
        have h2' : rst0 = Event.ld_rq :: rst := h2
        subst h2'
        exact Or.inl (.t13 _ c k _ hM hrq h3 h4)
      | st_rq_M_state w rst0 hrq hM =>
        have h2' : rst0 = Event.ld_rq :: rst := h2
        subst h2'
        exact Or.inl (.t17 _ c k w _ hM hrq h3 h4)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t13 _ i k rst h1 h2 h3 h4)


end ABack.T13


namespace ABack.T14

/-! # Passo indietro sul costruttore `t14` di `A`

`t14 s i k rst`: `(s.caches i).state = S`, `(s.caches i).extqueue.rq = ld_rq :: rst`,
`(s.caches i).value = s.parent.value`, `i ≠ k`, riga `k` a `M`.

`Pre_t14`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. I predecessori coperti: `upgrade_from_I_rsS v` su `i` (è `t9`), `ld_rq_data_available1`
su `i` (è `t14` con `rst := ld_rq :: rst`). -/


inductive Pre_t14 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v` on `q ≠ k` creating `(caches i).value = parent.value` (the
  rule writes `parent.value := v`; the old `parent.value` is free). The sub-case
  `v = p.parent.value` is already `t14`. -/
  | n1 (p : MSIState n) (i k q : Fin n) (j' : Nat) (v : Value) (rst : List Event) :
      (p.caches i).state = Bstate.S →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      (p.caches i).value = v →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      q ≠ k →
      (p.parent.queue_cip q)[j']? = some (CPEvent.rsIμ v) →
      Pre_t14 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k = M` -/
  | n2 (p : MSIState n) (i k : Fin n) (j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.S →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      (p.caches i).value = p.parent.value →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t14 p
  /-- from external `ld_rq` on `i` (with `extqueue.rq` empty) creating the head of
  `(caches i).extqueue.rq` -/
  | n3 (p : MSIState n) (i k : Fin n) :
      (p.caches i).state = Bstate.S →
      (p.caches i).extqueue.rq = [] →
      (p.caches i).value = p.parent.value →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      Pre_t14 p

/-- Nessun predecessore nuovo di `t14` è raggiungibile. -/
theorem Pre_t14_unreachable {n} {p : MSIState n} (h : Pre_t14 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k q j' v rst hS _ _ hne hk _ _ => exact not_reachable_of_S_rowM hne hS hk
  | n2 i k j' rst hS _ _ _ _ hall =>
    exact not_reachable_of_S hS (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n3 i k hS _ _ hne hk => exact not_reachable_of_S_rowM hne hS hk

/-- Passo interno: il predecessore di uno stato di `t14` è in `A` oppure in `Pre_t14`. -/
theorem back_t14_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.S)
    (h2 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h3 : (s.caches i).value = s.parent.value)
    (h4 : i ≠ k)
    (h5 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t14 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI =>
        -- crea `state = S` e `value = v'`: il predecessore è `t9`
        exact Or.inl (.t9 _ c k j' v' hI hj' h3 h4 h5)
      | downgrade_from_M_rs j' hj' hM => cases h1
      | downgrade_from_M_rs1 j' hj' hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t14 _ i k rst h1 h2 h3 h4 h5)
  | parent_upd_queue parent' pe q hp =>
    -- un passo del parent su `q` non tocca stato, valore ed `extqueue` di nessuna cache
    have h1' : (p.caches i).state = Bstate.S := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h1
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h1
    have h2' : (p.caches i).extqueue.rq = Event.ld_rq :: rst := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h2
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h2
    have h3' : (p.caches i).value = parent'.value := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h3
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h3
    clear h1 h2 h3
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti crea `value = parent.value` (`:= v'`)
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h5
      have h5' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      exact Or.inr (.n1 _ i k q j' v' rst h1' h2' h3' h4 h5' hqk hj')
    | downgrade_from_M_rq2 _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti non tocca i campi
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h5
      have h5' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      exact Or.inl (.t14 _ i k rst h1' h2' h3' h4 h5')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k = M` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        exact Or.inr (.n2 _ i q j' rst h1' h2' h3' h4 hj' hall)
      · have h5' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        rw [hall k] at h5'; cases h5'
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      -- grant di `S`: impossibile come ultimo passo (riga `k := S`, oppure riga `k = M` già prima)
      by_cases hqk : q = k
      · subst hqk; simp [update_Fin_gss] at h5
      · have h5' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        exact absurd h5' (hnoM k)
    | upgrade_to_M_invalid_all r j' hj' hrow => exact Or.inl (.t14 _ i k rst h1' h2' h3' h4 h5)
    | upgrade_to_M_invalid_all1 r j' hj' hrow => exact Or.inl (.t14 _ i k rst h1' h2' h3' h4 h5)
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => exact Or.inl (.t14 _ i k rst h1' h2' h3' h4 h5)
    | upgrade_to_M_invalid_all3 r j' hj' hrow => exact Or.inl (.t14 _ i k rst h1' h2' h3' h4 h5)
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: il predecessore di uno stato di `t14` è in `A` oppure in `Pre_t14`. -/
theorem back_t14_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.S)
    (h2 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h3 : (s.caches i).value = s.parent.value)
    (h4 : i ≠ k)
    (h5 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t14 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq =>
        -- crea la testa solo se la coda era vuota
        cases hrq : (p.caches c).extqueue.rq with
        | nil => exact Or.inr (.n3 _ c k h1 hrq h3 h4 h5)
        | cons a l =>
          have h2' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.ld_rq :: rst := h2
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨ha, _⟩ := h2'
          subst ha
          exact Or.inl (.t14 _ c k l h1 hrq h3 h4 h5)
      | st_rq w =>
        -- con la coda vuota la testa sarebbe `st_rq w`: impossibile; altrimenti non la crea
        cases hrq : (p.caches c).extqueue.rq with
        | nil =>
          have h2' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h2
          rw [hrq] at h2'
          simp at h2'
        | cons a l =>
          have h2' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h2
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨ha, _⟩ := h2'
          subst ha
          exact Or.inl (.t14 _ c k l h1 hrq h3 h4 h5)
      | ld_rq_data_available1 rst0 hrq hS =>
        -- toglie la testa precedente: il predecessore è `t14` con `rst := ld_rq :: rst`
        exact Or.inl (.t14 _ c k rst0 hS hrq h3 h4 h5)
      | ld_rq_data_available rst0 hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst0 hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t14 _ i k rst h1 h2 h3 h4 h5)


end ABack.T14


namespace ABack.T15

/-! # Passo indietro sul costruttore `t15` di `A`

`t15 s i k j rst`: `(s.caches i).state = M`, `rqIμ` in `(s.caches i).queue_pc` alla posizione `j`,
`(s.caches i).extqueue.rq = ld_rq :: rst`, `i ≠ k`, riga `k` non a `I`.

`Pre_t15`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti da
`A` così com'è scritto in `a.lean`. -/


inductive Pre_t15 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k ≠ I` (row `k := M`) -/
  | n1 (p : MSIState n) (i k : Fin n) (j j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t15 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `k` creating `shared_state k ≠ I` (row `k := S`) -/
  | n2 (p : MSIState n) (i k : Fin n) (j j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqS →
      p.parent.shared_state k = Bstate.I →
      (∀ k', ¬(p.parent.shared_state k' = Bstate.M)) →
      Pre_t15 p
  /-- from external `ld_rq` on `i` (with `extqueue.rq` empty) creating the head
  `(caches i).extqueue.rq = ld_rq :: []` -/
  | n3 (p : MSIState n) (i k : Fin n) (j : Nat) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = [] →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t15 p

/-- Nessun predecessore nuovo di `t15` è raggiungibile. -/
theorem Pre_t15_unreachable {n} {p : MSIState n} (h : Pre_t15 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j j' rst hM _ _ _ _ hall =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n2 i k j j' rst hM _ _ _ _ _ hnoM =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i)))
  | n3 i k j hM _ _ hne hk => exact not_reachable_of_M_rowJ hne hM hk

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
private theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rw [List.getElem?_append] at h
  split at h
  · exact h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact absurd rfl hne
    · cases h

set_option hygiene false in
/-- Invalidate `rqIμ` accodato a `q`: se `q = i` e la posizione `j` è l'ultima, l'`rqIμ` è stato
creato ora e il predecessore è in `t13`; altrimenti c'era già e il predecessore è in `t15`. -/
local macro "invMu_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h2
     have h2' : (p.parent.queue_pci q ++ [PCEvent.rqIμ])[j]? = some PCEvent.rqIμ := h2
     rw [List.getElem?_append] at h2'
     split at h2'
     · rw [(hsync q).2] at h2'
       exact Or.inl (.t15 _ q k j rst h1' h2' h3' h4 h5)
     · exact Or.inl (.t13 _ q k rst h1' h3' h4 h5)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h2
     exact Or.inl (.t15 _ i k j rst h1' h2 h3' h4 h5)))

set_option hygiene false in
/-- Invalidate `rqIσ` accodato a `q`: non crea l'`rqIμ`, il predecessore è in `t15`. -/
local macro "invSig_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h2
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     rw [(hsync q).2] at h2'
     exact Or.inl (.t15 _ q k j rst h1' h2' h3' h4 h5)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h2
     exact Or.inl (.t15 _ i k j rst h1' h2 h3' h4 h5)))

/-- Passo interno: l'ultimo passo `p → s` con `s` in `t15`. -/
theorem back_t15_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n} {j : Nat}
    {rst : List Event} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ)
    (h3 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h4 : i ≠ k)
    (h5 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t15 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v j0 hj0 hI => exact Or.inl (.t8 _ c k j0 v hI hj0 h4 h5)
      | upgrade_from_I_rsS v j0 hj0 hI => cases h1
      | downgrade_from_M_rs j0 hj0 hM => cases h1
      | downgrade_from_M_rs1 j0 hj0 hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t15 _ i k j rst h1 h2 h3 h4 h5)
  | parent_upd_queue parent' pe q hp =>
    -- un passo del parent non tocca né lo stato né la `extqueue` di alcuna cache
    have h1' : (p.caches i).state = Bstate.M := by
      by_cases hqi : q = i
      · subst hqi; simpa [update_Fin_gss] using h1
      · simpa [update_Fin_gso _ _ _ _ hqi] using h1
    have h3' : (p.caches i).extqueue.rq = Event.ld_rq :: rst := by
      by_cases hqi : q = i
      · subst hqi; simpa [update_Fin_gss] using h3
      · simpa [update_Fin_gso _ _ _ _ hqi] using h3
    clear h1 h3
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti nessun campo fissato è creato
      have hqk : ¬ q = k := by
        intro h; subst h; exact h5 (by simp [update_Fin_gss])
      have h5' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h2
        rw [(hsync q).2] at h2
        exact Or.inl (.t15 _ q k j rst h1' h2 h3' h4 h5')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h2
        exact Or.inl (.t15 _ i k j rst h1' h2 h3' h4 h5')
    | downgrade_from_M_rq2 _ j' hj' =>
      have hqk : ¬ q = k := by
        intro h; subst h; exact h5 (by simp [update_Fin_gss])
      have h5' : ¬ p.parent.shared_state k = Bstate.I := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h5
      by_cases hqi : q = i
      · subst hqi
        simp only [update_Fin_gss] at h2
        rw [(hsync q).2] at h2
        exact Or.inl (.t15 _ q k j rst h1' h2 h3' h4 h5')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h2
        exact Or.inl (.t15 _ i k j rst h1' h2 h3' h4 h5')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k ≠ I` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h4 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h2
        exact Or.inr (.n1 _ i q j j' rst h1' h2 h3' h4 hj' hall)
      · exact absurd (by simp [update_Fin_gso _ _ _ _ hqk, hall k]) h5
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      by_cases hqi : q = i
      · subst hqi
        have hqk : ¬ q = k := h4
        simp only [update_Fin_gss] at h2
        have h5' : ¬ p.parent.shared_state k = Bstate.I := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
        rw [(hsync q).2] at h2'
        exact Or.inl (.t15 _ q k j rst h1' h2' h3' h4 h5')
      · simp only [update_Fin_gso _ _ _ _ hqi] at h2
        by_cases hqk : q = k
        · subst hqk
          exact Or.inr (.n2 _ i q j j' rst h1' h2 h3' h4 hj' hI hnoM)
        · have h5' : ¬ p.parent.shared_state k = Bstate.I := by
            simpa [update_Fin_gso _ _ _ _ hqk] using h5
          exact Or.inl (.t15 _ i k j rst h1' h2 h3' h4 h5')
    | upgrade_to_M_invalid_all r j' hj' hrow => invMu_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => invSig_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => invSig_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => invMu_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: l'ultimo passo `p → s` con `s` in `t15`. -/
theorem back_t15_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n} {j : Nat}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ)
    (h3 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h4 : i ≠ k)
    (h5 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t15 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq =>
        -- `rq := rq ++ [ld_rq]`: crea la testa solo se `rq` era vuota
        have h3' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.ld_rq :: rst := h3
        cases hrq : (p.caches c).extqueue.rq with
        | nil => exact Or.inr (.n3 _ c k j h1 h2 hrq h4 h5)
        | cons a l =>
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨rfl, _⟩ := h3'
          exact Or.inl (.t15 _ c k j l h1 h2 hrq h4 h5)
      | st_rq w =>
        -- `rq := rq ++ [st_rq w]`: non può creare la testa `ld_rq`
        have h3' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h3
        cases hrq : (p.caches c).extqueue.rq with
        | nil => rw [hrq] at h3'; cases h3'
        | cons a l =>
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨rfl, _⟩ := h3'
          exact Or.inl (.t15 _ c k j l h1 h2 hrq h4 h5)
      | ld_rq_data_available1 rst0 hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst0 hrq hM =>
        have h3' : rst0 = Event.ld_rq :: rst := h3
        subst h3'
        exact Or.inl (.t15 _ c k j _ hM h2 hrq h4 h5)
      | st_rq_M_state w rst0 hrq hM =>
        have h3' : rst0 = Event.ld_rq :: rst := h3
        subst h3'
        exact Or.inl (.t18 _ c k j w _ hM h2 hrq h4 h5)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t15 _ i k j rst h1 h2 h3 h4 h5)


end ABack.T15


namespace ABack.T16

/-! # Passo indietro sul costruttore `t16` di `A`

`t16 s i k j rst`: `(s.caches i).state = S`, `rqIσ` in `(s.caches i).queue_pc` alla posizione
`j`, `(s.caches i).extqueue.rq = ld_rq :: rst`, `(s.caches i).value = s.parent.value`, `i ≠ k`,
riga `k` a `M`. (Come insieme, `t16 ⊆ t14`: `t16` è `t14` più il messaggio `rqIσ`.)

`Pre_t16`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. I predecessori coperti: `upgrade_from_I_rsS v` su `i` (è `t9`), `ld_rq_data_available1`
su `i` (è `t16` con `rst := ld_rq :: rst`), `upgrade_to_M_invalid_all1` / `upgrade_to_M_invalid_all2`
su `i` che accodano proprio quel `rqIσ` (è `t14`). -/


inductive Pre_t16 {n : Nat} : MSIState n → Prop where
  /-- from `downgrade_from_M_rq1 v` on `q ≠ k` creating `(caches i).value = parent.value` (the
  rule writes `parent.value := v`; the old `parent.value` is free). The sub-case
  `v = p.parent.value` is already `t16`. -/
  | n1 (p : MSIState n) (i k q : Fin n) (j j' : Nat) (v : Value) (rst : List Event) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      (p.caches i).value = v →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      q ≠ k →
      (p.parent.queue_cip q)[j']? = some (CPEvent.rsIμ v) →
      Pre_t16 p
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k = M` -/
  | n2 (p : MSIState n) (i k : Fin n) (j j' : Nat) (rst : List Event) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ →
      (p.caches i).extqueue.rq = Event.ld_rq :: rst →
      (p.caches i).value = p.parent.value →
      i ≠ k →
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      Pre_t16 p
  /-- from external `ld_rq` on `i` (with `extqueue.rq` empty) creating the head of
  `(caches i).extqueue.rq` -/
  | n3 (p : MSIState n) (i k : Fin n) (j : Nat) :
      (p.caches i).state = Bstate.S →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ →
      (p.caches i).extqueue.rq = [] →
      (p.caches i).value = p.parent.value →
      i ≠ k →
      p.parent.shared_state k = Bstate.M →
      Pre_t16 p

/-- Nessun predecessore nuovo di `t16` è raggiungibile. -/
theorem Pre_t16_unreachable {n} {p : MSIState n} (h : Pre_t16 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k q j j' v rst hS _ _ _ hne hk _ _ => exact not_reachable_of_S_rowM hne hS hk
  | n2 i k j j' rst hS _ _ _ _ _ hall =>
    exact not_reachable_of_S hS (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n3 i k j hS _ _ _ hne hk => exact not_reachable_of_S_rowM hne hS hk

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
theorem getElem?_of_append_singleton_ne_t16 {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rw [List.getElem?_append] at h
  split at h
  · exact h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact absurd rfl hne
    · cases h

/-- Passo interno: il predecessore di uno stato di `t16` è in `A` oppure in `Pre_t16`. -/
theorem back_t16_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n} {j : Nat}
    {rst : List Event} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.S)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIσ)
    (h3 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h4 : (s.caches i).value = s.parent.value)
    (h5 : i ≠ k)
    (h6 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t16 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3 h4
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v' j' hj' hI => cases h1
      | upgrade_from_I_rsS v' j' hj' hI =>
        -- crea `state = S` e `value = v'`: il predecessore è `t9`
        exact Or.inl (.t9 _ c k j' v' hI hj' h4 h5 h6)
      | downgrade_from_M_rs j' hj' hM => cases h1
      | downgrade_from_M_rs1 j' hj' hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3 h4
      exact Or.inl (.t16 _ i k j rst h1 h2 h3 h4 h5 h6)
  | parent_upd_queue parent' pe q hp =>
    -- un passo del parent su `q` non tocca stato, valore ed `extqueue` di nessuna cache;
    -- la `queue_pc` della cache `q` diventa `parent'.queue_pci q`
    have h1' : (p.caches i).state = Bstate.S := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h1
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h1
    have h3' : (p.caches i).extqueue.rq = Event.ld_rq :: rst := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h3
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h3
    have h4' : (p.caches i).value = parent'.value := by
      by_cases hqi : q = i
      · subst hqi; simpa only [update_Fin_gss] using h4
      · simpa only [update_Fin_gso _ _ _ _ hqi] using h4
    have h2' : (q = i ∧ (parent'.queue_pci i)[j]? = some PCEvent.rqIσ)
        ∨ (¬ q = i ∧ ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ) := by
      by_cases hqi : q = i
      · subst hqi; exact Or.inl ⟨rfl, by simpa only [update_Fin_gss] using h2⟩
      · exact Or.inr ⟨hqi, by simpa only [update_Fin_gso _ _ _ _ hqi] using h2⟩
    clear h1 h2 h3 h4
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti crea `value = parent.value` (`:= v'`)
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h6
      have h6' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h6
      have h2p : ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
        rcases h2' with ⟨_, h⟩ | ⟨_, h⟩
        · rw [← (hsync i).2]; exact h
        · exact h
      exact Or.inr (.n1 _ i k q j j' v' rst h1' h2p h3' h4' h5 h6' hqk hj')
    | downgrade_from_M_rq2 _ j' hj' =>
      -- riga `q := I`: `q = k` impossibile; altrimenti non tocca i campi
      have hqk : ¬ q = k := by
        intro h; subst h; simp [update_Fin_gss] at h6
      have h6' : p.parent.shared_state k = Bstate.M := by
        simpa [update_Fin_gso _ _ _ _ hqk] using h6
      have h2p : ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
        rcases h2' with ⟨_, h⟩ | ⟨_, h⟩
        · rw [← (hsync i).2]; exact h
        · exact h
      exact Or.inl (.t16 _ i k j rst h1' h2p h3' h4' h5 h6')
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k = M` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have h2p : ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
          rcases h2' with ⟨hqi, _⟩ | ⟨_, h⟩
          · exact absurd hqi.symm h5
          · exact h
        exact Or.inr (.n2 _ i q j j' rst h1' h2p h3' h4' h5 hj' hall)
      · have h6' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h6
        rw [hall k] at h6'; cases h6'
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      -- grant di `S`: impossibile come ultimo passo (riga `k := S`, oppure riga `k = M` già prima)
      by_cases hqk : q = k
      · subst hqk; simp [update_Fin_gss] at h6
      · have h6' : p.parent.shared_state k = Bstate.M := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h6
        exact absurd h6' (hnoM k)
    | upgrade_to_M_invalid_all r j' hj' hrow =>
      -- accoda `rqIμ` a `q`: non crea il `rqIσ`
      have h2p : ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
        rcases h2' with ⟨hqi, h⟩ | ⟨_, h⟩
        · subst hqi
          simp only [update_Fin_gss] at h
          rw [← (hsync q).2]
          exact getElem?_of_append_singleton_ne_t16 h (by intro h; cases h)
        · exact h
      exact Or.inl (.t16 _ i k j rst h1' h2p h3' h4' h5 h6)
    | upgrade_to_M_invalid_all1 r j' hj' hrow =>
      -- accoda `rqIσ` a `q`: se `q = i` ed è proprio quello in posizione `j`, il predecessore
      -- è `t14`; altrimenti il `rqIσ` c'era già e il predecessore è `t16`
      rcases h2' with ⟨hqi, h⟩ | ⟨_, h⟩
      · subst hqi
        simp only [update_Fin_gss] at h
        rw [List.getElem?_append] at h
        split at h
        · rw [(hsync q).2] at h
          exact Or.inl (.t16 _ q k j rst h1' h h3' h4' h5 h6)
        · exact Or.inl (.t14 _ q k rst h1' h3' h4' h5 h6)
      · exact Or.inl (.t16 _ i k j rst h1' h h3' h4' h5 h6)
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow =>
      rcases h2' with ⟨hqi, h⟩ | ⟨_, h⟩
      · subst hqi
        simp only [update_Fin_gss] at h
        rw [List.getElem?_append] at h
        split at h
        · rw [(hsync q).2] at h
          exact Or.inl (.t16 _ q k j rst h1' h h3' h4' h5 h6)
        · exact Or.inl (.t14 _ q k rst h1' h3' h4' h5 h6)
      · exact Or.inl (.t16 _ i k j rst h1' h h3' h4' h5 h6)
    | upgrade_to_M_invalid_all3 r j' hj' hrow =>
      have h2p : ((p.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
        rcases h2' with ⟨hqi, h⟩ | ⟨_, h⟩
        · subst hqi
          simp only [update_Fin_gss] at h
          rw [← (hsync q).2]
          exact getElem?_of_append_singleton_ne_t16 h (by intro h; cases h)
        · exact h
      exact Or.inl (.t16 _ i k j rst h1' h2p h3' h4' h5 h6)
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: il predecessore di uno stato di `t16` è in `A` oppure in `Pre_t16`. -/
theorem back_t16_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n} {j : Nat}
    {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.S)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIσ)
    (h3 : (s.caches i).extqueue.rq = Event.ld_rq :: rst)
    (h4 : (s.caches i).value = s.parent.value)
    (h5 : i ≠ k)
    (h6 : s.parent.shared_state k = Bstate.M) :
    A p ∨ Pre_t16 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3 h4
      cases hc with
      | ld_rq =>
        -- crea la testa solo se la coda era vuota
        cases hrq : (p.caches c).extqueue.rq with
        | nil => exact Or.inr (.n3 _ c k j h1 h2 hrq h4 h5 h6)
        | cons a l =>
          have h3' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.ld_rq :: rst := h3
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨ha, _⟩ := h3'
          subst ha
          exact Or.inl (.t16 _ c k j l h1 h2 hrq h4 h5 h6)
      | st_rq w =>
        -- con la coda vuota la testa sarebbe `st_rq w`: impossibile; altrimenti non la crea
        cases hrq : (p.caches c).extqueue.rq with
        | nil =>
          have h3' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h3
          rw [hrq] at h3'
          simp at h3'
        | cons a l =>
          have h3' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.ld_rq :: rst := h3
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨ha, _⟩ := h3'
          subst ha
          exact Or.inl (.t16 _ c k j l h1 h2 hrq h4 h5 h6)
      | ld_rq_data_available1 rst0 hrq hS =>
        -- toglie la testa precedente: il predecessore è `t16` con `rst := ld_rq :: rst`
        exact Or.inl (.t16 _ c k j rst0 hS h2 hrq h4 h5 h6)
      | ld_rq_data_available rst0 hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
      | st_rq_M_state w rst0 hrq hM => exact absurd (hM.symm.trans h1) (by intro h; cases h)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3 h4
      exact Or.inl (.t16 _ i k j rst h1 h2 h3 h4 h5 h6)


end ABack.T16


namespace ABack.T17

/-! # Passo indietro sul costruttore `t17` di `A`

`t17 s i k v rst`: `(s.caches i).state = M`, `(s.caches i).extqueue.rq = st_rq v :: rst`,
`i ≠ k`, riga `k` non a `I`.

`Pre_t17`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. -/


inductive Pre_t17 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k ≠ I` (row `k := M`) -/
  | n1 (p : MSIState n) (i k : Fin n) (j' : Nat) (v : Value) (rst : List Event) :
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      Pre_t17 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `k` creating `shared_state k ≠ I` (row `k := S`) -/
  | n2 (p : MSIState n) (i k : Fin n) (j' : Nat) (v : Value) (rst : List Event) :
      (p.parent.queue_cip k)[j']? = some CPEvent.rqS →
      p.parent.shared_state k = Bstate.I →
      (∀ k', ¬(p.parent.shared_state k' = Bstate.M)) →
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      Pre_t17 p
  /-- from external `st_rq v` on `i` (with `extqueue.rq` empty) creating the head
  `extqueue.rq = st_rq v :: []` -/
  | n3 (p : MSIState n) (i k : Fin n) :
      (p.caches i).state = Bstate.M →
      (p.caches i).extqueue.rq = [] →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t17 p

/-- Nessun predecessore nuovo di `t17` è raggiungibile. -/
theorem Pre_t17_unreachable {n} {p : MSIState n} (h : Pre_t17 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j' v rst _ hall hM _ _ =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n2 i k j' v rst _ _ hnoM hM _ _ =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i)))
  | n3 i k hM _ hne hk => exact not_reachable_of_M_rowJ hne hM hk

set_option hygiene false in
/-- Caso di un invalidate del parent (accoda `rqIμ`/`rqIσ` a `q`): non tocca i campi di `t17`. -/
local macro "inv_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2
     exact Or.inl (.t17 _ q k v rst h1 h2 h3 h4)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
     exact Or.inl (.t17 _ i k v rst h1 h2 h3 h4)))

set_option hygiene false in
/-- Caso di un downgrade del parent (riga `q := I`): `q = k` impossibile, altrimenti non tocca
i campi di `t17`. -/
local macro "down_case" : tactic => `(tactic|
  (have hqk : ¬ q = k := by
     intro h; subst h; exact h4 (by simp [update_Fin_gss])
   have h4' : ¬ p.parent.shared_state k = Bstate.I := by
     simpa [update_Fin_gso _ _ _ _ hqk] using h4
   by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2
     exact Or.inl (.t17 _ q k v rst h1 h2 h3 h4')
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
     exact Or.inl (.t17 _ i k v rst h1 h2 h3 h4')))

/-- Passo interno: l'ultimo passo prima di uno stato di `t17` parte da `A` o da `Pre_t17`. -/
theorem back_t17_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n}
    {v : Value} {rst : List Event} (_hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : (s.caches i).extqueue.rq = Event.st_rq v :: rst)
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t17 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v' j' hj' hI =>
        -- crea `state = M`: il predecessore è in `I` con `rsM v'` in coda, coperto da `t8`
        exact Or.inl (.t8 _ c k j' v' hI hj' h3 h4)
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM => cases h1
      | downgrade_from_M_rs1 j' hj' hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t17 _ i k v rst h1 h2 h3 h4)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' => down_case
    | downgrade_from_M_rq2 _ j' hj' => down_case
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k ≠ I` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h3 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inr (.n1 _ i q j' v rst hj' hall h1 h2 h3)
      · exact absurd (by simp [update_Fin_gso _ _ _ _ hqk, hall k]) h4
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h3 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
        exact Or.inr (.n2 _ i q j' v rst hj' hI hnoM h1 h2 h3)
      · have h4' : ¬ p.parent.shared_state k = Bstate.I := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h4
        by_cases hqi : q = i
        · subst hqi
          simp only [update_Fin_gss] at h1 h2
          exact Or.inl (.t17 _ q k v rst h1 h2 h3 h4')
        · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2
          exact Or.inl (.t17 _ i k v rst h1 h2 h3 h4')
    | upgrade_to_M_invalid_all r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => inv_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => inv_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => inv_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: l'ultimo passo prima di uno stato di `t17` parte da `A` o da `Pre_t17`. -/
theorem back_t17_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n}
    {v : Value} {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : (s.caches i).extqueue.rq = Event.st_rq v :: rst)
    (h3 : i ≠ k)
    (h4 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t17 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2
      cases hc with
      | ld_rq =>
        -- accoda `ld_rq` in fondo: la testa `st_rq v` c'era già
        have h1' : (p.caches c).state = Bstate.M := h1
        have h2' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.st_rq v :: rst := h2
        cases hrq : (p.caches c).extqueue.rq with
        | nil => rw [hrq] at h2'; simp at h2'
        | cons a l =>
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨ha, _⟩ := h2'
          subst ha
          exact Or.inl (.t17 _ c k v l h1' hrq h3 h4)
      | st_rq w =>
        have h1' : (p.caches c).state = Bstate.M := h1
        have h2' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.st_rq v :: rst := h2
        cases hrq : (p.caches c).extqueue.rq with
        | nil =>
          -- crea la testa: il predecessore ha `extqueue.rq = []`
          exact Or.inr (.n3 _ c k h1' hrq h3 h4)
        | cons a l =>
          rw [hrq] at h2'
          simp only [List.cons_append, List.cons.injEq] at h2'
          obtain ⟨ha, _⟩ := h2'
          subst ha
          exact Or.inl (.t17 _ c k v l h1' hrq h3 h4)
      | ld_rq_data_available1 rst' hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst' hrq hM =>
        -- crea la testa togliendo `ld_rq`: predecessore con `ld_rq :: st_rq v :: rst`, in `t13`
        have h2' : rst' = Event.st_rq v :: rst := h2
        subst h2'
        exact Or.inl (.t13 _ c k _ hM hrq h3 h4)
      | st_rq_M_state w rst' hrq hM =>
        -- crea la testa togliendo `st_rq w`: predecessore con `st_rq w :: st_rq v :: rst`, in `t17`
        have h2' : rst' = Event.st_rq v :: rst := h2
        subst h2'
        exact Or.inl (.t17 _ c k w _ hM hrq h3 h4)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2
      exact Or.inl (.t17 _ i k v rst h1 h2 h3 h4)


end ABack.T17


namespace ABack.T18

/-! # Passo indietro sul costruttore `t18` di `A`

`t18 s i k j v rst`: `(s.caches i).state = M`, `rqIμ` in `(s.caches i).queue_pc` alla posizione
`j`, `(s.caches i).extqueue.rq = st_rq v :: rst`, `i ≠ k`, riga `k` non a `I`.

`Pre_t18`: i vettori dei predecessori (un passo indietro, con `synced p`) che NON sono coperti
da `A`. -/


inductive Pre_t18 {n : Nat} : MSIState n → Prop where
  /-- from `upgrade_to_M_data_avilable_rq1` on `k` creating `shared_state k ≠ I` (row `k := M`) -/
  | n1 (p : MSIState n) (i k : Fin n) (j j' : Nat) (v : Value) (rst : List Event) :
      (p.parent.queue_cip k)[j']? = some CPEvent.rqM →
      (∀ k', p.parent.shared_state k' = Bstate.I) →
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      Pre_t18 p
  /-- from `upgrade_to_M_data_avilable_rq2` on `k` creating `shared_state k ≠ I` (row `k := S`) -/
  | n2 (p : MSIState n) (i k : Fin n) (j j' : Nat) (v : Value) (rst : List Event) :
      (p.parent.queue_cip k)[j']? = some CPEvent.rqS →
      p.parent.shared_state k = Bstate.I →
      (∀ k', ¬(p.parent.shared_state k' = Bstate.M)) →
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = Event.st_rq v :: rst →
      i ≠ k →
      Pre_t18 p
  /-- from external `st_rq v` on `i` (with `extqueue.rq` empty) creating the head
  `extqueue.rq = st_rq v :: []` -/
  | n3 (p : MSIState n) (i k : Fin n) (j : Nat) :
      (p.caches i).state = Bstate.M →
      ((p.caches i).queue_pc)[j]? = some PCEvent.rqIμ →
      (p.caches i).extqueue.rq = [] →
      i ≠ k →
      ¬(p.parent.shared_state k = Bstate.I) →
      Pre_t18 p

/-- Nessun predecessore nuovo di `t18` è raggiungibile. -/
theorem Pre_t18_unreachable {n} {p : MSIState n} (h : Pre_t18 p) : ¬ MSI.reachable p := by
  by_cases hsync : synced p
  swap
  · exact not_reachable_of_not_synced hsync
  cases h with
  | n1 i k j j' v rst _ hall hM _ _ _ =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (by rw [hall i]; intro h; cases h)))
  | n2 i k j j' v rst _ _ hnoM hM _ _ _ =>
    exact not_reachable_of_M hM (Or.inr (Or.inr (hnoM i)))
  | n3 i k j hM _ _ hne hk => exact not_reachable_of_M_rowJ hne hM hk

/-- Se `b` sta in `l ++ [a]` alla posizione `j` e `a ≠ b`, allora `b` stava già in `l`. -/
private theorem getElem?_of_append_singleton_ne {α} {l : List α} {a b : α} {j : Nat}
    (h : (l ++ [a])[j]? = some b) (hne : a ≠ b) : l[j]? = some b := by
  rw [List.getElem?_append] at h
  split at h
  · exact h
  · rw [List.getElem?_singleton] at h
    split at h
    · cases h; exact absurd rfl hne
    · cases h

set_option hygiene false in
/-- Invalidate `rqIμ` accodato a `q` (`upgrade_to_M_invalid_all`, `…_all3`): se `q = i` può
creare l'`rqIμ` di `t18` (quando `j` è l'ultima posizione); il predecessore è comunque in `t17`. -/
local macro "invμ_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     exact Or.inl (.t17 _ q k v rst h1 h3 h4 h5)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5)))

set_option hygiene false in
/-- Invalidate `rqIσ` accodato a `q` (`upgrade_to_M_invalid_all1`, `…_all2`): non crea campi di
`t18` (l'`rqIμ` c'era già). -/
local macro "invσ_case" : tactic => `(tactic|
  (by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
     rw [(hsync q).2] at h2'
     exact Or.inl (.t18 _ q k j v rst h1 h2' h3 h4 h5)
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5)))

set_option hygiene false in
/-- Caso di un downgrade del parent (riga `q := I`): `q = k` impossibile, altrimenti non tocca
i campi di `t18`. -/
local macro "down_case" : tactic => `(tactic|
  (have hqk : ¬ q = k := by
     intro h; subst h; exact h5 (by simp [update_Fin_gss])
   have h5' : ¬ p.parent.shared_state k = Bstate.I := by
     simpa [update_Fin_gso _ _ _ _ hqk] using h5
   by_cases hqi : q = i
   · subst hqi
     simp only [update_Fin_gss] at h1 h2 h3
     rw [(hsync q).2] at h2
     exact Or.inl (.t18 _ q k j v rst h1 h2 h3 h4 h5')
   · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
     exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5')))

/-- Passo interno: l'ultimo passo prima di uno stato di `t18` parte da `A` o da `Pre_t18`. -/
theorem back_t18_int {n} {p s : MSIState n} {e : MSIInternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} {rst : List Event} (hsync : synced p) (hstep : msi_step_internal p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ)
    (h3 : (s.caches i).extqueue.rq = Event.st_rq v :: rst)
    (h4 : i ≠ k)
    (h5 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t18 p := by
  cases hstep with
  | cache cache' c ce hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | rq_data_not_available hM => cases h1
      | rq_data_not_available1 hS => cases h1
      | upgrade_from_I_rq hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rq1 hI => exact absurd (hI.symm.trans h1) (by intro h; cases h)
      | upgrade_from_I_rs v' j' hj' hI =>
        -- crea `state = M`: il predecessore è in `I` con `rsM v'` in coda, coperto da `t8`
        exact Or.inl (.t8 _ c k j' v' hI hj' h4 h5)
      | upgrade_from_I_rsS v' j' hj' hI => cases h1
      | downgrade_from_M_rs j' hj' hM => cases h1
      | downgrade_from_M_rs1 j' hj' hS => cases h1
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5)
  | parent_upd_queue parent' pe q hp =>
    cases hp with
    | downgrade_from_M_rq1 v' _ j' hj' => down_case
    | downgrade_from_M_rq2 _ j' hj' => down_case
    | upgrade_to_M_data_avilable_rq1 _ j' hj' hall =>
      -- grant di `M`: tutte le righe erano a `I`, quindi la riga `k ≠ I` è quella appena scritta
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h4 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inr (.n1 _ i q j j' v rst hj' hall h1 h2 h3 h4)
      · exact absurd (by simp [update_Fin_gso _ _ _ _ hqk, hall k]) h5
    | upgrade_to_M_data_avilable_rq2 _ j' hj' hI hnoM =>
      by_cases hqk : q = k
      · subst hqk
        have hqi : ¬ q = i := fun h => h4 h.symm
        simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
        exact Or.inr (.n2 _ i q j j' v rst hj' hI hnoM h1 h2 h3 h4)
      · have h5' : ¬ p.parent.shared_state k = Bstate.I := by
          simpa [update_Fin_gso _ _ _ _ hqk] using h5
        by_cases hqi : q = i
        · subst hqi
          simp only [update_Fin_gss] at h1 h2 h3
          have h2' := getElem?_of_append_singleton_ne h2 (by intro h; cases h)
          rw [(hsync q).2] at h2'
          exact Or.inl (.t18 _ q k j v rst h1 h2' h3 h4 h5')
        · simp only [update_Fin_gso _ _ _ _ hqi] at h1 h2 h3
          exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5')
    | upgrade_to_M_invalid_all r j' hj' hrow => invμ_case
    | upgrade_to_M_invalid_all1 r j' hj' hrow => invσ_case
    | upgrade_to_M_invalid_all2 r j' hj' hne hrow => invσ_case
    | upgrade_to_M_invalid_all3 r j' hj' hrow => invμ_case
  | parent_no_queue parent' pe q hp => cases hp

/-- Passo esterno: l'ultimo passo prima di uno stato di `t18` parte da `A` o da `Pre_t18`. -/
theorem back_t18_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} {i k : Fin n} {j : Nat}
    {v : Value} {rst : List Event} (_hsync : synced p) (hstep : msi_step_external p e s)
    (h1 : (s.caches i).state = Bstate.M)
    (h2 : ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ)
    (h3 : (s.caches i).extqueue.rq = Event.st_rq v :: rst)
    (h4 : i ≠ k)
    (h5 : ¬(s.parent.shared_state k = Bstate.I)) :
    A p ∨ Pre_t18 p := by
  cases hstep with
  | cache ev cache' c hc =>
    by_cases hci : c = i
    · subst hci
      simp only [update_Fin_gss] at h1 h2 h3
      cases hc with
      | ld_rq =>
        -- accoda `ld_rq` in fondo: la testa `st_rq v` c'era già
        have h1' : (p.caches c).state = Bstate.M := h1
        have h2' : ((p.caches c).queue_pc)[j]? = some PCEvent.rqIμ := h2
        have h3' : (p.caches c).extqueue.rq ++ [Event.ld_rq] = Event.st_rq v :: rst := h3
        cases hrq : (p.caches c).extqueue.rq with
        | nil => rw [hrq] at h3'; simp at h3'
        | cons a l =>
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨ha, _⟩ := h3'
          subst ha
          exact Or.inl (.t18 _ c k j v l h1' h2' hrq h4 h5)
      | st_rq w =>
        have h1' : (p.caches c).state = Bstate.M := h1
        have h2' : ((p.caches c).queue_pc)[j]? = some PCEvent.rqIμ := h2
        have h3' : (p.caches c).extqueue.rq ++ [Event.st_rq w] = Event.st_rq v :: rst := h3
        cases hrq : (p.caches c).extqueue.rq with
        | nil =>
          -- crea la testa: il predecessore ha `extqueue.rq = []`
          exact Or.inr (.n3 _ c k j h1' h2' hrq h4 h5)
        | cons a l =>
          rw [hrq] at h3'
          simp only [List.cons_append, List.cons.injEq] at h3'
          obtain ⟨ha, _⟩ := h3'
          subst ha
          exact Or.inl (.t18 _ c k j v l h1' h2' hrq h4 h5)
      | ld_rq_data_available1 rst' hrq hS => exact absurd (hS.symm.trans h1) (by intro h; cases h)
      | ld_rq_data_available rst' hrq hM =>
        -- crea la testa togliendo `ld_rq`: predecessore con `ld_rq :: st_rq v :: rst`, in `t15`
        have h3' : rst' = Event.st_rq v :: rst := h3
        subst h3'
        exact Or.inl (.t15 _ c k j _ hM h2 hrq h4 h5)
      | st_rq_M_state w rst' hrq hM =>
        -- crea la testa togliendo `st_rq w`: predecessore con `st_rq w :: st_rq v :: rst`, in `t18`
        have h3' : rst' = Event.st_rq v :: rst := h3
        subst h3'
        exact Or.inl (.t18 _ c k j w _ hM h2 hrq h4 h5)
    · simp only [update_Fin_gso _ _ _ _ hci] at h1 h2 h3
      exact Or.inl (.t18 _ i k j v rst h1 h2 h3 h4 h5)


end ABack.T18

namespace ABack

/-- **`A₁`**: `A` più i predecessori a un passo dei suoi 18 costruttori. -/
inductive A₁ {n : Nat} : MSIState n → Prop where
  | base (s : MSIState n) : A s → A₁ s
  | p1 (s : MSIState n) : T1.Pre_t1 s → A₁ s
  | p2 (s : MSIState n) : T2.Pre_t2 s → A₁ s
  | p3 (s : MSIState n) : T3.Pre_t3 s → A₁ s
  | p4 (s : MSIState n) : T4.Pre_t4 s → A₁ s
  | p5 (s : MSIState n) : T5.Pre_t5 s → A₁ s
  | p6 (s : MSIState n) : T6.Pre_t6 s → A₁ s
  | p7 (s : MSIState n) : T7.Pre_t7 s → A₁ s
  | p8 (s : MSIState n) : T8.Pre_t8 s → A₁ s
  | p9 (s : MSIState n) : T9.Pre_t9 s → A₁ s
  | p10 (s : MSIState n) : T10.Pre_t10 s → A₁ s
  | p11 (s : MSIState n) : T11.Pre_t11 s → A₁ s
  | p12 (s : MSIState n) : T12.Pre_t12 s → A₁ s
  | p13 (s : MSIState n) : T13.Pre_t13 s → A₁ s
  | p14 (s : MSIState n) : T14.Pre_t14 s → A₁ s
  | p15 (s : MSIState n) : T15.Pre_t15 s → A₁ s
  | p16 (s : MSIState n) : T16.Pre_t16 s → A₁ s
  | p17 (s : MSIState n) : T17.Pre_t17 s → A₁ s
  | p18 (s : MSIState n) : T18.Pre_t18 s → A₁ s

/-- **Un passo interno all'indietro da `A` cade in `A₁`.** -/
theorem A_back_int {n} {p s : MSIState n} {e : MSIInternalEvent n} (hsync : synced p)
    (hstep : msi_step_internal p e s) (hA : A s) : A₁ p := by
  cases hA with
  | t1 i₁ i₂ j₁ j₂ v h1 h2 h3 =>
    rcases T1.back_t1_int hsync hstep i₁ i₂ j₁ j₂ v h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p1 _ h
  | t2 i₁ i₂ j₁ j₂ v h1 h2 h3 h4 =>
    rcases T2.back_t2_int hsync hstep i₁ i₂ j₁ j₂ v h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p2 _ h
  | t3 i j₁ j₂ h1 h2 h3 =>
    rcases T3.back_t3_int hsync hstep i j₁ j₂ h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p3 _ h
  | t4 i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T4.back_t4_int hsync hstep i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p4 _ h
  | t5 i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T5.back_t5_int hsync hstep i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p5 _ h
  | t6 i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T6.back_t6_int hsync hstep i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p6 _ h
  | t7 i j₁ j₂ h1 h2 h3 h4 h5 h6 =>
    rcases T7.back_t7_int hsync hstep i j₁ j₂ h1 h2 h3 h4 h5 h6 with h | h
    · exact A₁.base _ h
    · exact A₁.p7 _ h
  | t8 i k j v h1 h2 h3 h4 =>
    rcases T8.back_t8_int hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p8 _ h
  | t9 i k j v h1 h2 h3 h4 h5 =>
    rcases T9.back_t9_int hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p9 _ h
  | t10 i j₁ j₂ v₁ v₂ h1 h2 h3 h4 =>
    rcases T10.back_t10_int hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p10 _ h
  | t11 i j₁ j₂ v₁ v₂ h1 h2 h3 =>
    rcases T11.back_t11_int hsync hstep h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p11 _ h
  | t12 i j₁ j₂ v₁ v₂ h1 h2 h3 h4 =>
    rcases T12.back_t12_int hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p12 _ h
  | t13 i k rst h1 h2 h3 h4 =>
    rcases T13.back_t13_int hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p13 _ h
  | t14 i k rst h1 h2 h3 h4 h5 =>
    rcases T14.back_t14_int hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p14 _ h
  | t15 i k j rst h1 h2 h3 h4 h5 =>
    rcases T15.back_t15_int hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p15 _ h
  | t16 i k j rst h1 h2 h3 h4 h5 h6 =>
    rcases T16.back_t16_int hsync hstep h1 h2 h3 h4 h5 h6 with h | h
    · exact A₁.base _ h
    · exact A₁.p16 _ h
  | t17 i k v rst h1 h2 h3 h4 =>
    rcases T17.back_t17_int hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p17 _ h
  | t18 i k j v rst h1 h2 h3 h4 h5 =>
    rcases T18.back_t18_int hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p18 _ h

/-- **Un passo esterno all'indietro da `A` cade in `A₁`.** -/
theorem A_back_ext {n} {p s : MSIState n} {e : MSIExternalEvent n} (hsync : synced p)
    (hstep : msi_step_external p e s) (hA : A s) : A₁ p := by
  cases hA with
  | t1 i₁ i₂ j₁ j₂ v h1 h2 h3 =>
    rcases T1.back_t1_ext hsync hstep i₁ i₂ j₁ j₂ v h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p1 _ h
  | t2 i₁ i₂ j₁ j₂ v h1 h2 h3 h4 =>
    rcases T2.back_t2_ext hsync hstep i₁ i₂ j₁ j₂ v h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p2 _ h
  | t3 i j₁ j₂ h1 h2 h3 =>
    rcases T3.back_t3_ext hsync hstep i j₁ j₂ h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p3 _ h
  | t4 i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T4.back_t4_ext hsync hstep i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p4 _ h
  | t5 i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T5.back_t5_ext hsync hstep i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p5 _ h
  | t6 i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 =>
    rcases T6.back_t6_ext hsync hstep i₁ i₂ i j₁ j₂ h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p6 _ h
  | t7 i j₁ j₂ h1 h2 h3 h4 h5 h6 =>
    rcases T7.back_t7_ext hsync hstep i j₁ j₂ h1 h2 h3 h4 h5 h6 with h | h
    · exact A₁.base _ h
    · exact A₁.p7 _ h
  | t8 i k j v h1 h2 h3 h4 =>
    rcases T8.back_t8_ext hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p8 _ h
  | t9 i k j v h1 h2 h3 h4 h5 =>
    rcases T9.back_t9_ext hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p9 _ h
  | t10 i j₁ j₂ v₁ v₂ h1 h2 h3 h4 =>
    rcases T10.back_t10_ext hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p10 _ h
  | t11 i j₁ j₂ v₁ v₂ h1 h2 h3 =>
    rcases T11.back_t11_ext hsync hstep h1 h2 h3 with h | h
    · exact A₁.base _ h
    · exact A₁.p11 _ h
  | t12 i j₁ j₂ v₁ v₂ h1 h2 h3 h4 =>
    rcases T12.back_t12_ext hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p12 _ h
  | t13 i k rst h1 h2 h3 h4 =>
    rcases T13.back_t13_ext hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p13 _ h
  | t14 i k rst h1 h2 h3 h4 h5 =>
    rcases T14.back_t14_ext hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p14 _ h
  | t15 i k j rst h1 h2 h3 h4 h5 =>
    rcases T15.back_t15_ext hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p15 _ h
  | t16 i k j rst h1 h2 h3 h4 h5 h6 =>
    rcases T16.back_t16_ext hsync hstep h1 h2 h3 h4 h5 h6 with h | h
    · exact A₁.base _ h
    · exact A₁.p16 _ h
  | t17 i k v rst h1 h2 h3 h4 =>
    rcases T17.back_t17_ext hsync hstep h1 h2 h3 h4 with h | h
    · exact A₁.base _ h
    · exact A₁.p17 _ h
  | t18 i k j v rst h1 h2 h3 h4 h5 =>
    rcases T18.back_t18_ext hsync hstep h1 h2 h3 h4 h5 with h | h
    · exact A₁.base _ h
    · exact A₁.p18 _ h

/-- **Nessuno stato di `A₁` è raggiungibile.** -/
theorem A₁_unreachable {n} {s : MSIState n} (h : A₁ s) : ¬ MSI.reachable s := by
  cases h with
  | base h => exact A_unreachable h
  | p1 h => exact T1.Pre_t1_unreachable h
  | p2 h => exact T2.Pre_t2_unreachable h
  | p3 h => exact T3.Pre_t3_unreachable h
  | p4 h => exact T4.Pre_t4_unreachable h
  | p5 h => exact T5.Pre_t5_unreachable h
  | p6 h => exact T6.Pre_t6_unreachable h
  | p7 h => exact T7.Pre_t7_unreachable h
  | p8 h => exact T8.Pre_t8_unreachable h
  | p9 h => exact T9.Pre_t9_unreachable h
  | p10 h => exact T10.Pre_t10_unreachable h
  | p11 h => exact T11.Pre_t11_unreachable h
  | p12 h => exact T12.Pre_t12_unreachable h
  | p13 h => exact T13.Pre_t13_unreachable h
  | p14 h => exact T14.Pre_t14_unreachable h
  | p15 h => exact T15.Pre_t15_unreachable h
  | p16 h => exact T16.Pre_t16_unreachable h
  | p17 h => exact T17.Pre_t17_unreachable h
  | p18 h => exact T18.Pre_t18_unreachable h

end ABack

#print axioms ABack.A_back_int
#print axioms ABack.A_back_ext
#print axioms ABack.A₁_unreachable
