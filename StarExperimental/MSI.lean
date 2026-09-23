import StarExperimental.MSI_def

open THEORY
open Relation

/-! # `MSI`: teoremi sul protocollo MSI

Tutte le definizioni stanno in `MSI_def.lean`; qui restano i lemmi ausiliari, la tattica
`new_backward_tatic` con il suo risultato `badView_unreachable`, i lemmi di inversione e tutti i
teoremi di commutazione (parent–parent, cache–cache, parent–cache, esterno–interno). -/

/-- Aggiornare due indici (anche uguali) con la stessa `append` commuta. -/
theorem update_Fin_append_comm {α : Type} {n} (f : Fin n → List α) (a b : Fin n) (x : List α) :
    update_Fin a (update_Fin b (f b ++ x) f a ++ x) (update_Fin b (f b ++ x) f)
      = update_Fin b (update_Fin a (f a ++ x) f b ++ x) (update_Fin a (f a ++ x) f) := by
  funext k
  by_cases hab : a = b
  · subst hab; simp [update_Fin]
  · by_cases hka : k = a
    · subst hka; simp [update_Fin, Ne.symm hab]
    · by_cases hkb : k = b
      · subst hkb; simp [update_Fin, hab]
      · simp [update_Fin, Ne.symm hka, Ne.symm hkb]

/-- Aggiornare due volte lo stesso indice: vince l'ultimo. -/
theorem update_Fin_update_Fin_same {α : Type} {n} (i : Fin n) (e e' : α) (f : Fin n → α) :
    update_Fin i e (update_Fin i e' f) = update_Fin i e f := by
  funext q
  by_cases hq : q = i
  · subst hq; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hq]

/-- Rimettere il valore che c'era non cambia nulla. -/
theorem update_Fin_self {α : Type} {n} (i : Fin n) (f : Fin n → α) :
    update_Fin i (f i) f = f := by
  funext q
  by_cases hq : q = i
  · subst hq; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hq]


/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem parent_msi_step_congr {n} {p1 p2 p2' : ParentState n} {e : ParentInternalEvent n}
    (h : parent_msi_step p1 e p2) (heq : p2 = p2') : parent_msi_step p1 e p2' := heq ▸ h

/-- Estensionalità campo per campo (puntuale sulle funzioni) di `MSIState`. -/
theorem MSIState.ext_all {n} {a b : MSIState n}
    (hc : ∀ k, a.caches k = b.caches k)
    (hv : a.parent.value = b.parent.value)
    (hs : ∀ k, a.parent.shared_state k = b.parent.shared_state k)
    (hq1 : ∀ k, a.parent.queue_cip k = b.parent.queue_cip k)
    (hq2 : ∀ k, a.parent.queue_pci k = b.parent.queue_pci k) : a = b := by
  obtain ⟨ca, pv, ps, pq1, pq2⟩ := a
  obtain ⟨cb, pv', ps', pq1', pq2'⟩ := b
  have e1 : ca = cb := funext hc
  have e2 : pv = pv' := hv
  have e3 : ps = ps' := funext hs
  have e4 : pq1 = pq1' := funext hq1
  have e5 : pq2 = pq2' := funext hq2
  subst e1 e2 e3 e4 e5
  rfl


/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem msi_step_congr {n} {s s' s'' : MSIState n} {t : MSIInternalEvent n}
    (h : msi_step_internal s t s') (heq : s' = s'') : msi_step_internal s t s'' := heq ▸ h

-- inductive msi_step_external : MSIState n → Event → MSIState n → Prop where
--   | cache : ∀ m1 e cache' i,
--       cache_msi_step (m1.caches i) e cache' →
--       msi_step_external m1 (Event.tag n i e)
--         { m1 with caches := update_Fin i cache' m1.caches,
--                   parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
--                   parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci
--         }


theorem lst_get {α} (l : List α) (a : α) : (l ++ [a])[l.length]? = some a := by simp

theorem lst_erase {α} (l : List α) (a : α) : (l ++ [a]).eraseIdx l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem lst_get2 {α} (l : List α) (a b : α) : ((l ++ [a]) ++ [b])[l.length]? = some a := by
  rw [List.append_assoc]; simp

theorem lst_erase2 {α} (l : List α) (a b : α) :
    ((l ++ [a]) ++ [b]).eraseIdx l.length = l ++ [b] := by
  rw [List.append_assoc]
  show (l ++ [a, b]).eraseIdx l.length = l ++ [b]
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]


theorem backwards_reachable_not_init {T} {l : MSI.LTS T} {s} :
  (∀ s_init, l.init s_init → l.backwards_reachable_from s s_init) ↔ l.reachable s := by
  grind [MSI.LTS.reachable, MSI.LTS.backwards_reachable_from, Relation.reflTransGen_swap]

theorem backwards_reachable_φ {T} {l : LTS T} {s} :
  l.φ s → ∃ s_init, l.flushed s_init ∧ l.backwards_reachable_from s_init s := by
  intro h; induction h <;> grind [LTS.backwards_reachable_from]

theorem φ_backwards_reachable {T} {l : LTS T} {s} :
  ∀ s_init, l.flushed s_init → l.backwards_reachable_from s_init s → l.φ s := by
  dsimp [LTS.backwards_reachable_from]; intro s_init hinit htrans
  induction htrans
  · apply LTS.φ.flushed; assumption
  · apply LTS.φ.back_step; assumption; assumption




/-- `default` è uno stato iniziale. -/
theorem msi_init_default {n} : msi_init (default : MSIState n) :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩


open BackwardGen

namespace MSIView

/-- Cancellare l'elemento in posizione `j` fa calare di uno il conteggio, se quell'elemento
soddisfa il predicato. -/
theorem countP_eraseIdx {α} (p : α → Bool) : ∀ (l : List α) (j : Nat) (a : α),
    l[j]? = some a → (l.eraseIdx j).countP p + (if p a then 1 else 0) = l.countP p := by
  intro l
  induction l with
  | nil => intro j a h; simp at h
  | cons x xs ih =>
    intro j a h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.eraseIdx_cons_zero, List.countP_cons]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hh := ih j a h
      simp only [List.eraseIdx_cons_succ, List.countP_cons]
      omega

/-- I lemmi "in avanti" che la tattica istanzia su ogni ipotesi `l[j]? = some a`. -/
theorem countP_eraseIdx_grantM {l : List PCEvent} {j : Nat} {a : PCEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isGrantM + (if isGrantM a then 1 else 0) = l.countP isGrantM :=
  countP_eraseIdx _ _ _ _ h

theorem countP_eraseIdx_grantS {l : List PCEvent} {j : Nat} {a : PCEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isGrantS + (if isGrantS a then 1 else 0) = l.countP isGrantS :=
  countP_eraseIdx _ _ _ _ h

theorem countP_eraseIdx_releaseM {l : List CPEvent} {j : Nat} {a : CPEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isReleaseM + (if isReleaseM a then 1 else 0) = l.countP isReleaseM :=
  countP_eraseIdx _ _ _ _ h

theorem countP_eraseIdx_releaseS {l : List CPEvent} {j : Nat} {a : CPEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isReleaseS + (if isReleaseS a then 1 else 0) = l.countP isReleaseS :=
  countP_eraseIdx _ _ _ _ h

end MSIView

open MSIView


/-- La tattica con i parametri di `MSI` già messi. Senza argomento usa `msiSetup`;
con un argomento, il `SymSetup` dato. -/
syntax "new_backward_tatic" (ppSpace term:max)? : tactic
syntax "new_backward_tatic?" (ppSpace term:max)? : tactic

macro_rules
  | `(tactic| new_backward_tatic) => `(tactic| new_backward_tatic (msiSetup _))
  | `(tactic| new_backward_tatic $st) =>
    `(tactic| backward_search_gen $st
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
           countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [msi_step_internal, cache_msi_step_internal, parent_msi_step])

macro_rules
  | `(tactic| new_backward_tatic?) => `(tactic| new_backward_tatic? (msiSetup _))
  | `(tactic| new_backward_tatic? $st) =>
    `(tactic| backward_search_gen? $st
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
           countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [msi_step_internal, cache_msi_step_internal, parent_msi_step])

/-- Ogni stato raggiungibile ha le due copie di ogni coda allineate. -/
theorem synced_of_reachable {n} {s : MSIState n} (h : MSI.reachable s) : synced s := by
  have key : ∀ x, ReflTransGen MSI.atrans (default : MSIState n) x → synced x := by
    intro x hx
    induction hx with
    | refl => exact fun _ => ⟨rfl, rfl⟩
    | tail _ hstep ih => obtain ⟨t, ht⟩ := hstep; exact synced_step ih ht
  exact key s (h _ msi_init_default)

set_option maxHeartbeats 0 in
/-- **Il risultato della tattica**: nessuno stato con una vista cattiva è raggiungibile da
`default` (453 viste di partenza, chiusura di 453, 2062 passi). Da qui discendono tutte le
uscite `¬ MSI.reachable s` dei teoremi di commutazione. -/
theorem badView_unreachable_from_default {n} : (msiSetup n).Unreachable := by
  new_backward_tatic

/-- `MSI.reachable s` quantifica su tutti gli stati iniziali; `default` è uno di essi. -/
theorem badView_unreachable {n} (s : MSIState n) (h : ∃ i j, badView (msiView s i j)) :
    ¬ MSI.reachable s :=
  fun hreach => badView_unreachable_from_default s h (hreach (default : MSIState n) msi_init_default)


/-! ### Lemmi di inversione per i passi del parent -/

theorem downgradeM_inv {n} {s s' : MSIState n} {v : Value} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) ∧ s' = downgradeMSt s v i j := by
  cases h; rename_i hp; cases hp; exact ⟨_, ‹_›, rfl⟩

theorem downgradeS_inv {n} {s s' : MSIState n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some CPEvent.rsIσ ∧ s' = downgradeSSt s i j := by
  cases h; rename_i hp; cases hp; exact ⟨_, ‹_›, rfl⟩

theorem grantM_inv {n} {s s' : MSIState n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some CPEvent.rqM
      ∧ (∀ k, s.parent.shared_state k = Bstate.I) ∧ s' = grantMSt s i j := by
  cases h; rename_i hp; cases hp; exact ⟨_, ‹_›, ‹_›, rfl⟩

theorem grantS_inv {n} {s s' : MSIState n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some CPEvent.rqS
      ∧ (∀ k, ¬(s.parent.shared_state k = Bstate.M)) ∧ s' = grantSSt s i j := by
  cases h; rename_i hp; cases hp; exact ⟨_, ‹_›, ‹_›, rfl⟩

/-- La guardia del grant di `S`: la riga del richiedente era a `I`. -/
theorem grantS_rowI {n} {s s' : MSIState n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) s') :
    s.parent.shared_state i = Bstate.I := by
  cases h; rename_i hp; cases hp; assumption

/-- Inversione dell'invalidate mirato `upgrade_to_M_invalid_all k` all'indice `i`: le due regole
(`rqM` o `rqS` pendente da `k`) danno lo stesso stato `invMSt s i`. -/
theorem invalidateM_inv {n} {s s' : MSIState n} {k i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) s') :
    (∃ j : Nat, (s.parent.queue_cip k)[j]? = some CPEvent.rqM ∨ (s.parent.queue_cip k)[j]? = some CPEvent.rqS)
      ∧ s.parent.shared_state i = Bstate.M ∧ s' = invMSt s i := by
  cases h; rename_i hp
  cases hp
  · exact ⟨⟨_, Or.inl ‹_›⟩, ‹_›, rfl⟩
  · exact ⟨⟨_, Or.inr ‹_›⟩, ‹_›, rfl⟩

/-- Inversione di `invalid_allS` all'indice `i`: un `rqM` pendente da qualche `k`, riga `i = S`. -/
theorem invalidateS_inv {n} {s s' : MSIState n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue .invalid_allS i)) s') :
    (∃ (k : Fin n) (j : Nat), (s.parent.queue_cip k)[j]? = some CPEvent.rqM)
      ∧ s.parent.shared_state i = Bstate.S ∧ s' = invSSt s i := by
  cases h; rename_i hp; cases hp; exact ⟨⟨_, _, ‹_›⟩, ‹_›, rfl⟩

/-- Inversione di `upgrade_to_S_invalid_2_rq1S k` all'indice `i`: un `rqS` pendente da `k ≠ i`,
riga `i = S`. -/
theorem invalidateS2_inv {n} {s s' : MSIState n} {k i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i)) s') :
    (∃ j : Nat, (s.parent.queue_cip k)[j]? = some CPEvent.rqS)
      ∧ ¬(i = k) ∧ s.parent.shared_state i = Bstate.S ∧ s' = invSSt s i := by
  cases h; rename_i hp; cases hp; exact ⟨⟨_, ‹_›⟩, ‹_›, ‹_›, rfl⟩


/-! ### Lemmi ponte verso `¬ MSI.reachable s` -/

theorem not_reachable_of_not_synced {n} {s : MSIState n} (h : ¬ synced s) : ¬ MSI.reachable s :=
  fun hr => h (synced_of_reachable hr)

/-- Il contatore saturato di un conteggio non nullo non è `zero`. -/
theorem cnt_ne_zero {e : Nat} (h : e ≠ 0) : Cnt.ofCount e ≠ .zero := by
  rw [Ne, Cnt.ofCount_eq_zero]; exact h

theorem muMsgs_ne_zero_of_rsIμ {n} {p : ParentState n} {i : Fin n} {k : Nat} {v : Value}
    (h : (p.queue_cip i)[k]? = some (CPEvent.rsIμ v)) : muMsgs p i ≠ 0 := by
  have : 0 < (p.queue_cip i).countP isReleaseM :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? h, rfl⟩
  unfold muMsgs; omega

theorem muMsgs_ne_zero_of_rsM {n} {p : ParentState n} {i : Fin n} {k : Nat} {v : Value}
    (h : (p.queue_pci i)[k]? = some (PCEvent.rsM v)) : muMsgs p i ≠ 0 := by
  have : 0 < (p.queue_pci i).countP isGrantM :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? h, rfl⟩
  unfold muMsgs; omega

theorem sigMsgs_ne_zero_of_rsIσ {n} {p : ParentState n} {i : Fin n} {k : Nat}
    (h : (p.queue_cip i)[k]? = some CPEvent.rsIσ) : sigMsgs p i ≠ 0 := by
  have : 0 < (p.queue_cip i).countP isReleaseS :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? h, rfl⟩
  unfold sigMsgs; omega

theorem sigMsgs_ne_zero_of_rsS {n} {p : ParentState n} {i : Fin n} {k : Nat} {v : Value}
    (h : (p.queue_pci i)[k]? = some (PCEvent.rsS v)) : sigMsgs p i ≠ 0 := by
  have : 0 < (p.queue_pci i).countP isGrantS :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? h, rfl⟩
  unfold sigMsgs; omega

/-- Due elementi in posizioni diverse che soddisfano `p` danno `countP p ≥ 2`. -/
theorem two_le_countP_of_ne {α} (p : α → Bool) (l : List α) {j₁ j₂ : Nat} {a b : α}
    (h₁ : l[j₁]? = some a) (h₂ : l[j₂]? = some b) (hne : j₁ ≠ j₂)
    (ha : p a = true) (hb : p b = true) : 2 ≤ l.countP p := by
  have hc := countP_eraseIdx p l j₁ a h₁
  rw [ha] at hc; simp only [if_true] at hc
  have hmem : b ∈ l.eraseIdx j₁ := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact List.mem_of_getElem? (l := l.eraseIdx j₁) (i := j₂ - 1)
        (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact h₂)
    · exact List.mem_of_getElem? (l := l.eraseIdx j₁) (i := j₂)
        (by rw [List.getElem?_eraseIdx_of_lt (by omega)]; exact h₂)
  have : 0 < (l.eraseIdx j₁).countP p := List.countP_pos_iff.mpr ⟨b, hmem, hb⟩
  omega

/-- Vista cattiva 1: due messaggi con token `M` per `i`. -/
theorem not_reachable_of_two_mu {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ muMsgs s.parent i) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inl (by show Cnt.ofCount (muMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h)⟩

/-- Vista cattiva 1: due messaggi con token `S` per `i`. -/
theorem not_reachable_of_two_sig {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ sigMsgs s.parent i) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inl (by show Cnt.ofCount (sigMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h))⟩

/-- Vista cattiva 1: un token `M` e un token `S` in volo per `i`. -/
theorem not_reachable_of_mu_sig {n} {s : MSIState n} {i : Fin n} (h₁ : muMsgs s.parent i ≠ 0) (h₂ : sigMsgs s.parent i ≠ 0) :
    ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h₁,
                                          cnt_ne_zero h₂⟩))⟩

/-- Vista cattiva 2: un token `M` per `i` con la riga `i` non a `M`. -/
theorem not_reachable_of_mu_row {n} {s : MSIState n} {i : Fin n} (h : muMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.M)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩)))⟩

/-- Vista cattiva 2: un token `S` per `i` con la riga `i` non a `S`. -/
theorem not_reachable_of_sig_row {n} {s : MSIState n} {i : Fin n} (h : sigMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.S)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩))))⟩

/-- Vista cattiva 3: la cache `i` in `M` con un token `M` in volo, un token `S` in volo, o la riga non a `M`. -/
theorem not_reachable_of_M {n} {s : MSIState n} {i : Fin n} (hM : (s.caches i).state = Bstate.M)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.M)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, by
    rcases h with h | h | h
    · exact Or.inl (cnt_ne_zero h)
    · exact Or.inr (Or.inl (cnt_ne_zero h))
    · exact Or.inr (Or.inr h)⟩)))))⟩

/-- Vista cattiva 3: la cache `i` in `S` con un token `M` in volo, un token `S` in volo, o la riga non a `S`. -/
theorem not_reachable_of_S {n} {s : MSIState n} {i : Fin n} (hS : (s.caches i).state = Bstate.S)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.S)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, by
    rcases h with h | h | h
    · exact Or.inl (cnt_ne_zero h)
    · exact Or.inr (Or.inl (cnt_ne_zero h))
    · exact Or.inr (Or.inr h)⟩))))))⟩

/-- Vista cattiva 4: la riga `i = M` e la riga di `j ≠ i` non a `I`. -/
theorem not_reachable_of_rowM_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hd : s.parent.shared_state i = Bstate.M) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hd, hd'⟩)))))))⟩

/-- Vista cattiva 4: la riga `i = S` e la riga di `j ≠ i` a `M`. -/
theorem not_reachable_of_rowS_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hd : s.parent.shared_state i = Bstate.S) (hd' : s.parent.shared_state j = Bstate.M) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hd, hd'⟩))))))))⟩

/-- Vista cattiva 5: la cache `i` in `M` e la riga di `j ≠ i` non a `I`. -/
theorem not_reachable_of_M_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hM : (s.caches i).state = Bstate.M) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hM, hd'⟩)))))))))⟩

/-- Vista cattiva 5: la cache `i` in `S` e la riga di `j ≠ i` a `M`. -/
theorem not_reachable_of_S_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hS : (s.caches i).state = Bstate.S) (hd' : s.parent.shared_state j = Bstate.M) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hS, hd'⟩))))))))))⟩

/-- Vista cattiva 5: un token `M` per `i` e la riga di `j ≠ i` non a `I`. -/
theorem not_reachable_of_mu_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : muMsgs s.parent i ≠ 0) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨decide_eq_false hne, cnt_ne_zero h, hd'⟩)))))))))))⟩

/-- Vista cattiva 5: un token `S` per `i` e la riga di `j ≠ i` a `M`. -/
theorem not_reachable_of_sig_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : sigMsgs s.parent i ≠ 0) (hd' : s.parent.shared_state j = Bstate.M) : ¬ MSI.reachable s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨decide_eq_false hne, cnt_ne_zero h, hd'⟩)))))))))))⟩


/-! # Commutazione parent–parent

Due passi del parent (`.parent (.upd_queue e i)`) applicati allo stesso stato `s`, una coppia per
ognuna delle 28 combinazioni non ordinate dei 7 eventi del parent. Enunciato di base, come per
`MI`: diamante, oppure `s' = s''` (stesso messaggio consumato), oppure `¬ MSI.reachable s` (code non
allineate, `synced_of_reachable`, o vista cattiva, `badView_unreachable_from_default`). Dove il
diamante è falso l'enunciato aggiunge il percorso di
riconvergenza: due downgrade da `M` coincidono a meno del valore del parent; l'invalidate dopo un
downgrade è assorbito a meno del messaggio stantio (`invMSt`/`invSSt`); i due grant riconvergono
in 7 + 7 passi; downgrade e grant di `S` sullo stesso indice in 4 + 4; grant di `S` e invalidate
`S` sullo stesso indice in 2 + 2. Le regole `upgrade_to_M_invalid_all` e `_all3` condividono
l'evento, quindi un solo teorema le copre. -/

/-- **Due downgrade da `M` commutano a meno del valore del parent.** Con `i₁ ≠ i₂` i due passi
toccano indici diversi: restano entrambi abilitati e gli stati finali coincidono tranne che per
`parent.value` (vince l'ultimo rilascio). Con `i₁ = i₂` e la stessa posizione è lo stesso passo
(`s' = s''`); con posizioni diverse le due cancellazioni commutano (`key`), di nuovo a meno del valore. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s'' →
  (∃ t₁ t₂,
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) t₁ ∧
    msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) t₂ ∧
    { t₁ with parent.value := t₂.parent.value } = t₂)
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
è la vista cattiva 2 (`not_reachable_of_mu_row`), sia con `i₁ = i₂` sia con `i₁ ≠ i₂`. -/
theorem comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₂
  -- un `rsIμ` in volo su `i₁` mentre la riga `i₁` è a `I`: vista cattiva 2
  exact Or.inr (Or.inr (not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ hj₁)
    (by rw [hall i₁]; intro h; cases h)))

/-- **Downgrade da `M` / grant di `S`.** Il grant di `S` richiede nessuna riga a `M`, ma il
downgrade consuma un `rsIμ` in volo su `i₁`: un token `M` per `i₁` con la riga `i₁` non a `M`
è la vista cattiva 2 (`not_reachable_of_mu_row`), sia con `i₁ = i₂` sia con `i₁ ≠ i₂`. -/
theorem comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨_, _, hnoM, _⟩ := grantS_inv h₂
  -- un `rsIμ` in volo su `i₁` mentre la riga `i₁` non è a `M`: vista cattiva 2
  exact Or.inr (Or.inr (not_reachable_of_mu_row (muMsgs_ne_zero_of_rsIμ hj₁) (hnoM i₁)))

/-- Downgrade da `M` di `i₁` e invalidate mirato `rqIμ` verso `i₂`. Con `i₁ ≠ i₂` il diamante:
l'invalidate non tocca l'`rsIμ v` e la richiesta di `k` sopravvive alla cancellazione (spostata
se `k = i₁`). Con `i₁ = i₂` la riga va a `I` e l'invalidate non scatta più da `s'`: il downgrade
da `s''` arriva esattamente a `invMSt s' i₂` (invalidate assorbito). -/
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq2_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
un `rsIσ` è in volo su `i₁`: vista cattiva 2 (`not_reachable_of_sig_row`). Con `i₁ ≠ i₂` i passi toccano
indici diversi e il grant resta abilitato da `s'` (il downgrade porta `i₁` a `I`): diamante. -/
theorem comm_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, rfl⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, hall, rfl⟩ := grantM_inv h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice: un `rsIσ` in volo su `i₁` con la riga `i₁` a `I` (vista cattiva 2)
    subst hne
    exact Or.inr (Or.inr (not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsIσ hj₁)
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
theorem comm_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (Or.inr (not_reachable_of_not_synced hsync)))
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
      exact Or.inr (Or.inr (Or.inr (not_reachable_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj₁))))))
    | S =>
      -- cache in `S` con il proprio `rsIσ` in volo: vista cattiva 3
      exact Or.inr (Or.inr (Or.inr (not_reachable_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj₁))))))
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
theorem comm_downgrade_from_M_rq2_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq2_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rq2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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

/-- La riconvergenza dei due grant `M`: da ciascuno dei due stati la cache servita prende la
linea, la rilascia, il parent registra il rilascio e poi serve l'altra richiesta allo stesso
modo (7 passi per lato). Vale per indici distinti (cammino di `MI`) e, con `i₁ = i₂`, per
posizioni distinte: la seconda richiesta scala di una posizione dopo la prima cancellazione (`key`). -/
theorem grantM_grantM_reconverge {n} {s : MSIState n} {i₁ i₂ : Fin n} {j₁ j₂ : Nat}
    (hdiff : i₁ ≠ i₂ ∨ j₁ ≠ j₂)
    (hj₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (hj₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hI₁ : (s.caches i₁).state = Bstate.I) (hI₂ : (s.caches i₂).state = Bstate.I) :
    ∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
      msi_step_internal (grantMSt s i₁ j₁) (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
      msi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rs s.parent.value) i₂) t₅ ∧
      msi_step_internal t₅ (.cache .rq_data_not_available i₂) t₆ ∧
      msi_step_internal t₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) s''' ∧
      msi_step_internal (grantMSt s i₂ j₂) (.cache (.upgrade_from_I_rs s.parent.value) i₂) u₁ ∧
      msi_step_internal u₁ (.cache .rq_data_not_available i₂) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) u₃ ∧
      msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
      msi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
      msi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
      msi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''' := by
  by_cases hne : i₁ = i₂
  · -- stesso indice, posizioni distinte: la seconda richiesta scala dopo la prima cancellazione
    subst hne
    have hj : j₁ ≠ j₂ := hdiff.resolve_left (fun h => h rfl)
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
    -- un cammino di 7 passi da `grantMSt s i₁ a`: la seconda richiesta sta in `b` dopo la cancellazione di `a`
    have path : ∀ (a b : Nat), ((s.parent.queue_cip i₁).eraseIdx a)[b]? = some CPEvent.rqM →
        ∃ t₁ t₂ t₃ t₄ t₅ t₆,
          msi_step_internal (grantMSt s i₁ a) (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
          msi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
          msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
          msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) t₄ ∧
          msi_step_internal t₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₅ ∧
          msi_step_internal t₅ (.cache .rq_data_not_available i₁) t₆ ∧
          msi_step_internal t₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁))
            (MSIState.mk
              (update_Fin i₁ { s.caches i₁ with
                  state := Bstate.I,
                  value := s.parent.value,
                  queue_cp := ((s.parent.queue_cip i₁).eraseIdx a).eraseIdx b,
                  queue_pc := s.parent.queue_pci i₁ } s.caches)
              { s.parent with
                  shared_state := update_Fin i₁ Bstate.I s.parent.shared_state,
                  queue_cip := update_Fin i₁ (((s.parent.queue_cip i₁).eraseIdx a).eraseIdx b) s.parent.queue_cip,
                  queue_pci := update_Fin i₁ (s.parent.queue_pci i₁) s.parent.queue_pci }) := by
      intro a b hb
      refine ⟨_, _, _, _, _, _,
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?p1 ?p2),
        msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?p3),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx a).length ?p4),
        msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ b ?p5 ?p6),
        msi_step_internal.cache _ _ i₁ _
          (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?p7 ?p8),
        msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?p9),
        msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
          (parent_msi_step.downgrade_from_M_rq1 _ _ i₁
            (((s.parent.queue_cip i₁).eraseIdx a).eraseIdx b).length ?p10)) ?peq⟩
      -- la cache prende `rsM`, rilascia, il parent registra; poi la seconda richiesta
      case p1 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
      case p2 => simp only [grantMSt, update_Fin_gss]; exact hI₁
      case p3 => simp only [grantMSt, update_Fin_gss]
      case p4 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
      case p5 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact hb
      case p6 =>
        intro k
        by_cases hk : k = i₁
        · subst hk; simp only [grantMSt, update_Fin_gss]
        · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
      case p7 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact lst_get _ _
      case p8 => simp only [grantMSt, update_Fin_gss]
      case p9 => simp only [grantMSt, update_Fin_gss]
      case p10 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact lst_get _ _
      -- lo stato finale esplicito, campo per campo
      case peq =>
        refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
        · intro k
          by_cases hk : k = i₁
          · subst hk; simp only [grantMSt, update_Fin_gss, lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]
        · intro k
          by_cases hk : k = i₁
          · subst hk; simp only [grantMSt, update_Fin_gss]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]
        · intro k
          by_cases hk : k = i₁
          · subst hk; simp only [grantMSt, update_Fin_gss, lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]
        · intro k
          by_cases hk : k = i₁
          · subst hk; simp only [grantMSt, update_Fin_gss, lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]
    rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
    · -- j₁ < j₂: da `s'` la seconda richiesta è scalata in `j₂ - 1`, da `s''` resta in `j₁`
      obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, p₁, p₂, p₃, p₄, p₅, p₆, p₇⟩ := path j₁ (j₂ - 1)
        (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂)
      obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := path j₂ j₁
        (by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁)
      refine ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, _,
        p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₁, q₂, q₃, q₄, q₅, q₆, msi_step_congr q₇ ?_⟩
      rw [key _ _ _ hlt]
    · -- j₂ < j₁: simmetrico, da `s''` la prima richiesta è scalata in `j₁ - 1`
      obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, p₁, p₂, p₃, p₄, p₅, p₆, p₇⟩ := path j₁ j₂
        (by rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂)
      obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := path j₂ (j₁ - 1)
        (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁)
      refine ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, _,
        p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₁, q₂, q₃, q₄, q₅, q₆, msi_step_congr q₇ ?_⟩
      rw [key _ _ _ hgt]
  · -- indici distinti: i due cammini di `MI`
    have hne' : i₂ ≠ i₁ := Ne.symm hne
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?l1 ?l2),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?l3),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?l4),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₂ j₂ ?l5 ?l6),
      msi_step_internal.cache _ _ i₂ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₂).length ?l7 ?l8),
      msi_step_internal.cache _ _ i₂ _ (cache_msi_step_internal.rq_data_not_available _ ?l9),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?l10),
      msi_step_internal.cache _ _ i₂ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₂).length ?r1 ?r2),
      msi_step_internal.cache _ _ i₂ _ (cache_msi_step_internal.rq_data_not_available _ ?r3),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?r4),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j₁ ?r5 ?r6),
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?r7 ?r8),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?r9),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?r10))
        ?eq⟩
    -- cammino sinistro
    case l1 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l2 => simp only [grantMSt, update_Fin_gss]; exact hI₁
    case l3 => simp only [grantMSt, update_Fin_gss]
    case l4 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l5 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    case l6 =>
      intro k
      by_cases hk : k = i₁
      · subst hk; simp only [grantMSt, update_Fin_gss]
      · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
    case l7 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
    case l8 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hI₂
    case l9 => simp only [grantMSt, update_Fin_gss]
    case l10 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
    -- cammino destro
    case r1 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case r2 => simp only [grantMSt, update_Fin_gss]; exact hI₂
    case r3 => simp only [grantMSt, update_Fin_gss]
    case r4 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case r5 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    case r6 =>
      intro k
      by_cases hk : k = i₂
      · subst hk; simp only [grantMSt, update_Fin_gss]
      · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
    case r7 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
    case r8 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hI₁
    case r9 => simp only [grantMSt, update_Fin_gss]
    case r10 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]

/-- Due grant `M` non commutano mai: la guardia `∀ i, shared_state i = I` è distrutta dal grant
stesso. La riconvergenza è servire le due richieste una dopo l'altra (7 passi per lato,
`grantM_grantM_reconverge`), sia con `i₁ ≠ i₂` sia con `i₁ = i₂` e posizioni distinte; stessa
posizione dà `s' = s''`. Una cache servita non in `I` (riga `I` per `hall`) è una vista cattiva. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, hall, rfl⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grantM_inv h₂
  -- le due cache devono essere in `I`: la riga è `I` (`hall`), altrimenti vista cattiva
  cases hI₁ : (s.caches i₁).state with
  | M => exact Or.inr (Or.inr (not_reachable_of_M hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | S => exact Or.inr (Or.inr (not_reachable_of_S hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | I =>
    cases hI₂ : (s.caches i₂).state with
    | M => exact Or.inr (Or.inr (not_reachable_of_M hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | S => exact Or.inr (Or.inr (not_reachable_of_S hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | I =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: stessa posizione dà lo stesso stato, altrimenti i due cammini
        subst hne
        by_cases hj : j₁ = j₂
        · subst hj; exact Or.inr (Or.inl rfl)
        · exact Or.inl (grantM_grantM_reconverge (Or.inr hj) hj₁ hj₂ hall hI₁ hI₂)
      · -- indici distinti: i due cammini
        exact Or.inl (grantM_grantM_reconverge (Or.inl hne) hj₁ hj₂ hall hI₁ hI₂)

/-- La riconvergenza del grant di `M` a `i₁` e del grant di `S` a `i₂`: da ciascuno dei due stati
la cache servita prende la linea, la rilascia, il parent registra il rilascio e poi serve l'altra
richiesta allo stesso modo. Con `i₁ = i₂` la seconda richiesta scala di posizione dopo la prima
cancellazione (`key`). I due cammini (7 passi ciascuno) finiscono nello stesso stato. -/
theorem grantM_grantS_reconverge {n} {s : MSIState n} {i₁ i₂ : Fin n} {j₁ j₂ : Nat}
    (hj₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (hj₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqS)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hI₁ : (s.caches i₁).state = Bstate.I) (hI₂ : (s.caches i₂).state = Bstate.I) :
    ∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
      msi_step_internal (grantMSt s i₁ j₁) (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
      msi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rsS s.parent.value) i₂) t₅ ∧
      msi_step_internal t₅ (.cache .ld_rq_data_not_availableS i₂) t₆ ∧
      msi_step_internal t₆ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''' ∧
      msi_step_internal (grantSSt s i₂ j₂) (.cache (.upgrade_from_I_rsS s.parent.value) i₂) u₁ ∧
      msi_step_internal u₁ (.cache .ld_rq_data_not_availableS i₂) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) u₃ ∧
      msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
      msi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
      msi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
      msi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''' := by
  by_cases hne : i₁ = i₂
  · -- stesso indice: `rqM ≠ rqS` dà `j₁ ≠ j₂`, la seconda richiesta scala dopo la prima cancellazione
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
    -- le posizioni scalate: `rqS` in `j₂'` dopo aver tolto `j₁`, `rqM` in `j₁'` dopo aver tolto `j₂`
    obtain ⟨j₂', j₁', hj₂', hj₁', hkey⟩ : ∃ j₂' j₁' : Nat,
        ((s.parent.queue_cip i₁).eraseIdx j₁)[j₂']? = some CPEvent.rqS ∧
        ((s.parent.queue_cip i₁).eraseIdx j₂)[j₁']? = some CPEvent.rqM ∧
        ((s.parent.queue_cip i₁).eraseIdx j₁).eraseIdx j₂'
          = ((s.parent.queue_cip i₁).eraseIdx j₂).eraseIdx j₁' := by
      rcases Nat.lt_or_gt_of_ne hjne with hlt | hgt
      · -- j₁ < j₂: `rqS` scala in j₂ - 1, `rqM` resta in j₁
        refine ⟨j₂ - 1, j₁, ?_, ?_, (key _ _ _ hlt).symm⟩
        · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
        · rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
      · -- j₂ < j₁: `rqS` resta in j₂, `rqM` scala in j₁ - 1
        refine ⟨j₂, j₁ - 1, ?_, ?_, key _ _ _ hgt⟩
        · rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂
        · rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?l1 ?l2),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?l3),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?l4),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₁ j₂' ?l5 ?hI1 ?l6),
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?l7 ?l8),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available1 _ ?l9),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq2 _ i₁
          (((s.parent.queue_cip i₁).eraseIdx j₁).eraseIdx j₂').length ?l10),
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₁).length ?r1 ?r2),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available1 _ ?r3),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq2 _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₂).length ?r4),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j₁' ?r5 ?r6),
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?r7 ?r8),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?r9),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁
          (((s.parent.queue_cip i₁).eraseIdx j₂).eraseIdx j₁').length ?r10))
        ?eq⟩
    -- cammino sinistro: prima `M`, poi `S`
    case l1 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l2 => simp only [grantMSt, update_Fin_gss]; exact hI₁
    case l3 => simp only [grantMSt, update_Fin_gss]
    case l4 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l5 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact hj₂'
    case hI1 => simp only [grantMSt, update_Fin_gss]
    case l6 =>
      intro k
      by_cases hk : k = i₁
      · subst hk; simp only [grantMSt, update_Fin_gss, reduceCtorEq, not_false_eq_true]
      · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk, hall k, reduceCtorEq, not_false_eq_true]
    case l7 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    case l8 => simp only [grantMSt, update_Fin_gss]
    case l9 => simp only [grantMSt, update_Fin_gss]
    case l10 => simp only [grantMSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    -- cammino destro: prima `S`, poi `M`
    case r1 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case r2 => simp only [grantSSt, update_Fin_gss]; exact hI₂
    case r3 => simp only [grantSSt, update_Fin_gss]
    case r4 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case r5 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact hj₁'
    case r6 =>
      intro k
      by_cases hk : k = i₁
      · subst hk; simp only [grantSSt, update_Fin_gss]
      · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
    case r7 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    case r8 => simp only [grantSSt, update_Fin_gss]
    case r9 => simp only [grantSSt, update_Fin_gss]
    case r10 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [grantMSt, grantSSt, update_Fin_gss, lst_erase, hkey]
        · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · exact rfl
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [grantMSt, grantSSt, update_Fin_gss]
        · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [grantMSt, grantSSt, update_Fin_gss, lst_erase, hkey]
        · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [grantMSt, grantSSt, update_Fin_gss, lst_erase]
        · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk]
  · -- indici distinti: le due richieste non si toccano
    have hne' : ¬ i₂ = i₁ := fun h => hne h.symm
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?l1 ?l2),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?l3),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?l4),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i₂ j₂ ?l5 ?hI1 ?l6),
      msi_step_internal.cache _ _ i₂ _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₂).length ?l7 ?l8),
      msi_step_internal.cache _ _ i₂ _ (cache_msi_step_internal.rq_data_not_available1 _ ?l9),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq2 _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?l10),
      msi_step_internal.cache _ _ i₂ _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i₂).length ?r1 ?r2),
      msi_step_internal.cache _ _ i₂ _ (cache_msi_step_internal.rq_data_not_available1 _ ?r3),
      msi_step_internal.parent_upd_queue _ _ _ i₂
        (parent_msi_step.downgrade_from_M_rq2 _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?r4),
      msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j₁ ?r5 ?r6),
      msi_step_internal.cache _ _ i₁ _
        (cache_msi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?r7 ?r8),
      msi_step_internal.cache _ _ i₁ _ (cache_msi_step_internal.rq_data_not_available _ ?r9),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i₁
        (parent_msi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?r10))
        ?eq⟩
    -- cammino sinistro: prima `M` a `i₁`, poi `S` a `i₂`
    case l1 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l2 => simp only [grantMSt, update_Fin_gss]; exact hI₁
    case l3 => simp only [grantMSt, update_Fin_gss]
    case l4 => simp only [grantMSt, update_Fin_gss]; exact lst_get _ _
    case l5 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
    case hI1 => simp only [grantMSt, update_Fin_gso2 _ _ _ _ hne']; exact hall i₂
    case l6 =>
      intro k
      by_cases hk : k = i₁
      · subst hk; simp only [grantMSt, update_Fin_gss, reduceCtorEq, not_false_eq_true]
      · simp only [grantMSt, update_Fin_gso2 _ _ _ _ hk, hall k, reduceCtorEq, not_false_eq_true]
    case l7 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
    case l8 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hI₂
    case l9 => simp only [grantMSt, update_Fin_gss]
    case l10 => simp only [grantMSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
    -- cammino destro: prima `S` a `i₂`, poi `M` a `i₁`
    case r1 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case r2 => simp only [grantSSt, update_Fin_gss]; exact hI₂
    case r3 => simp only [grantSSt, update_Fin_gss]
    case r4 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case r5 => simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
    case r6 =>
      intro k
      by_cases hk : k = i₂
      · subst hk; simp only [grantSSt, update_Fin_gss]
      · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
    case r7 => simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
    case r8 => simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hI₁
    case r9 => simp only [grantSSt, update_Fin_gss]
    case r10 => simp only [grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
    -- i due stati finali coincidono, campo per campo
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · exact rfl
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁
          simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · by_cases hk₂ : k = i₂
          · subst hk₂
            simp only [grantMSt, grantSSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
              update_Fin_gso2 _ _ _ _ hne', lst_erase]
          · simp only [grantMSt, grantSSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]

/-- Il grant di `M` a `i₁` e il grant di `S` a `i₂` non commutano: ciascuno distrugge la guardia
dell'altro. La riconvergenza è servire le due richieste una dopo l'altra (7 passi per lato,
`grantM_grantS_reconverge`), sia con `i₁ = i₂` (posizioni diverse, `rqM ≠ rqS`) sia con `i₁ ≠ i₂`.
Le due cache devono essere in `I` (righe tutte a `I`), altrimenti `¬ MSI.reachable s` (vista cattiva 3). -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, hall, rfl⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grantS_inv h₂
  -- la cache `i₁` deve essere in `I`: la riga `i₁` è a `I` (vista cattiva 3 altrimenti)
  cases hI₁ : (s.caches i₁).state with
  | M => exact Or.inr (Or.inr (not_reachable_of_M hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | S => exact Or.inr (Or.inr (not_reachable_of_S hI₁ (Or.inr (Or.inr (by simp [hall i₁])))))
  | I =>
    -- la cache `i₂` deve essere in `I`: la riga `i₂` è a `I` (vista cattiva 3 altrimenti)
    cases hI₂ : (s.caches i₂).state with
    | M => exact Or.inr (Or.inr (not_reachable_of_M hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | S => exact Or.inr (Or.inr (not_reachable_of_S hI₂ (Or.inr (Or.inr (by simp [hall i₂])))))
    | I => exact Or.inl (grantM_grantS_reconverge hj₁ hj₂ hall hI₁ hI₂)

/-- **Grant di `M` / invalidate mirato.** Il grant richiede tutte le righe a `I`, l'invalidate
richiede la riga `i₂` a `M`: le due guardie si contraddicono, la coppia è vuota. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, hM, _⟩ := invalidateM_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `M` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hM

/-- **Grant di `M` / invalidate `rqIσ` (`invalid_allS`).** Il grant richiede tutte le righe a
`I`, l'invalidate richiede la riga `i₂` a `S`: guardie contraddittorie, coppia vuota. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, hS, _⟩ := invalidateS_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `S` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hS

/-- **Grant di `M` / invalidate `rqIσ` mirato (`upgrade_to_S_invalid_2_rq1S k`).** Il grant
richiede tutte le righe a `I`, l'invalidate richiede la riga `i₂` a `S`: guardie
contraddittorie, coppia vuota. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨_, _, hall, _⟩ := grantM_inv h₁
  obtain ⟨_, _, hS, _⟩ := invalidateS2_inv h₂
  -- la riga `i₂` è a `I` per il grant e a `S` per l'invalidate: assurdo
  cases (hall i₂).symm.trans hS

/-- La riconvergenza di due grant `S` alla stessa cache `i` in posizioni distinte `j₁ ≠ j₂`:
da ciascuno dei due stati la cache prende la linea, la rilascia, il parent registra il rilascio
(riga di nuovo a `I`, come chiede la guardia) e poi serve l'altra richiesta, scalata di una
posizione dopo la prima cancellazione (`key`). I due cammini (7 passi) finiscono nello stesso stato. -/
theorem grantS_grantS_reconverge {n} {s : MSIState n} {i : Fin n} {j₁ j₂ : Nat}
    (hj : j₁ ≠ j₂)
    (hj₁ : (s.parent.queue_cip i)[j₁]? = some CPEvent.rqS)
    (hj₂ : (s.parent.queue_cip i)[j₂]? = some CPEvent.rqS)
    (hrow : s.parent.shared_state i = Bstate.I)
    (hnoM : ∀ k, ¬(s.parent.shared_state k = Bstate.M))
    (hcI : (s.caches i).state = Bstate.I) :
    ∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆ s''',
      msi_step_internal (grantSSt s i j₁) (.cache (.upgrade_from_I_rsS s.parent.value) i) t₁ ∧
      msi_step_internal t₁ (.cache .ld_rq_data_not_availableS i) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue .downgrade_from_S_rq1S i)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rsS s.parent.value) i) t₅ ∧
      msi_step_internal t₅ (.cache .ld_rq_data_not_availableS i) t₆ ∧
      msi_step_internal t₆ (.parent (.upd_queue .downgrade_from_S_rq1S i)) s''' ∧
      msi_step_internal (grantSSt s i j₂) (.cache (.upgrade_from_I_rsS s.parent.value) i) u₁ ∧
      msi_step_internal u₁ (.cache .ld_rq_data_not_availableS i) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue .downgrade_from_S_rq1S i)) u₃ ∧
      msi_step_internal u₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) u₄ ∧
      msi_step_internal u₄ (.cache (.upgrade_from_I_rsS s.parent.value) i) u₅ ∧
      msi_step_internal u₅ (.cache .ld_rq_data_not_availableS i) u₆ ∧
      msi_step_internal u₆ (.parent (.upd_queue .downgrade_from_S_rq1S i)) s''' := by
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
  -- un cammino di 7 passi da `grantSSt s i a`: la seconda richiesta sta in `b` dopo la cancellazione di `a`
  have path : ∀ (a b : Nat), ((s.parent.queue_cip i).eraseIdx a)[b]? = some CPEvent.rqS →
      ∃ t₁ t₂ t₃ t₄ t₅ t₆,
        msi_step_internal (grantSSt s i a) (.cache (.upgrade_from_I_rsS s.parent.value) i) t₁ ∧
        msi_step_internal t₁ (.cache .ld_rq_data_not_availableS i) t₂ ∧
        msi_step_internal t₂ (.parent (.upd_queue .downgrade_from_S_rq1S i)) t₃ ∧
        msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) t₄ ∧
        msi_step_internal t₄ (.cache (.upgrade_from_I_rsS s.parent.value) i) t₅ ∧
        msi_step_internal t₅ (.cache .ld_rq_data_not_availableS i) t₆ ∧
        msi_step_internal t₆ (.parent (.upd_queue .downgrade_from_S_rq1S i))
          (MSIState.mk
            (update_Fin i { s.caches i with
                state := Bstate.I,
                value := s.parent.value,
                queue_cp := ((s.parent.queue_cip i).eraseIdx a).eraseIdx b,
                queue_pc := s.parent.queue_pci i } s.caches)
            { s.parent with
                shared_state := update_Fin i Bstate.I s.parent.shared_state,
                queue_cip := update_Fin i (((s.parent.queue_cip i).eraseIdx a).eraseIdx b) s.parent.queue_cip,
                queue_pci := update_Fin i (s.parent.queue_pci i) s.parent.queue_pci }) := by
    intro a b hb
    refine ⟨_, _, _, _, _, _,
      msi_step_internal.cache _ _ i _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i).length ?p1 ?p2),
      msi_step_internal.cache _ _ i _ (cache_msi_step_internal.rq_data_not_available1 _ ?p3),
      msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.downgrade_from_M_rq2 _ i ((s.parent.queue_cip i).eraseIdx a).length ?p4),
      msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ i b ?p5 ?pI ?p6),
      msi_step_internal.cache _ _ i _
        (cache_msi_step_internal.upgrade_from_I_rsS _ _ (s.parent.queue_pci i).length ?p7 ?p8),
      msi_step_internal.cache _ _ i _ (cache_msi_step_internal.rq_data_not_available1 _ ?p9),
      msi_step_congr (msi_step_internal.parent_upd_queue _ _ _ i
        (parent_msi_step.downgrade_from_M_rq2 _ i
          (((s.parent.queue_cip i).eraseIdx a).eraseIdx b).length ?p10)) ?peq⟩
    -- la cache prende `rsS`, rilascia, il parent registra; poi la seconda richiesta
    case p1 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case p2 => simp only [grantSSt, update_Fin_gss]; exact hcI
    case p3 => simp only [grantSSt, update_Fin_gss]
    case p4 => simp only [grantSSt, update_Fin_gss]; exact lst_get _ _
    case p5 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact hb
    -- la guardia del secondo grant: la riga di `i` è appena tornata a `I`
    case pI => simp only [grantSSt, update_Fin_gss]
    case p6 =>
      intro k
      by_cases hk : k = i
      · subst hk; simp only [grantSSt, update_Fin_gss, reduceCtorEq, not_false_eq_true]
      · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]; exact hnoM k
    case p7 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    case p8 => simp only [grantSSt, update_Fin_gss]
    case p9 => simp only [grantSSt, update_Fin_gss]
    case p10 => simp only [grantSSt, update_Fin_gss, lst_erase]; exact lst_get _ _
    -- lo stato finale esplicito, campo per campo
    case peq =>
      refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
      · intro k
        by_cases hk : k = i
        · subst hk; simp only [grantSSt, update_Fin_gss, lst_erase]
        · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i
        · subst hk; simp only [grantSSt, update_Fin_gss]
        · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i
        · subst hk; simp only [grantSSt, update_Fin_gss, lst_erase]
        · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]
      · intro k
        by_cases hk : k = i
        · subst hk; simp only [grantSSt, update_Fin_gss, lst_erase]
        · simp only [grantSSt, update_Fin_gso2 _ _ _ _ hk]
  rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
  · -- j₁ < j₂: da `s'` la seconda richiesta è scalata in `j₂ - 1`, da `s''` resta in `j₁`
    obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, p₁, p₂, p₃, p₄, p₅, p₆, p₇⟩ := path j₁ (j₂ - 1)
      (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂)
    obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := path j₂ j₁
      (by rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁)
    refine ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, _,
      p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₁, q₂, q₃, q₄, q₅, q₆, msi_step_congr q₇ ?_⟩
    rw [key _ _ _ hlt]
  · -- j₂ < j₁: simmetrico, da `s''` la prima richiesta è scalata in `j₁ - 1`
    obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, p₁, p₂, p₃, p₄, p₅, p₆, p₇⟩ := path j₁ j₂
      (by rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂)
    obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := path j₂ (j₁ - 1)
      (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁)
    refine ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, _,
      p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₁, q₂, q₃, q₄, q₅, q₆, msi_step_congr q₇ ?_⟩
    rw [key _ _ _ hgt]

/-- Due grant di `S`: con indici distinti commutano (diamante: la guardia "riga a `I`" di ciascuno
non è toccata dall'altro); con lo stesso indice e la stessa posizione danno lo stesso stato; con lo
stesso indice e posizioni distinte il secondo grant non può più scattare (riga a `S`) e si riconverge
servendo le due richieste una dopo l'altra (`grantS_grantS_reconverge`), se la cache è in `I`. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
      | M => exact Or.inr (Or.inr (Or.inr (not_reachable_of_M hc (Or.inr (Or.inr (by simp [hI₁]))))))
      | S => exact Or.inr (Or.inr (Or.inr (not_reachable_of_S hc (Or.inr (Or.inr (by simp [hI₁]))))))
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
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  obtain ⟨_, _, hnoM, _⟩ := grantS_inv h₁
  obtain ⟨_, hM, _⟩ := invalidateM_inv h₂
  -- la riga `i₂` non è a `M` per il grant di `S` ma è a `M` per l'invalidate: assurdo
  exact absurd hM (hnoM i₂)

/-- Grant di `S` a `i₁` e `invalid_allS` a `i₂` (un `rqM` pendente da `k`, riga `i₂ = S`).
Con `i₁ ≠ i₂` diamante (se `k = i₁` l'`rqM` scorre oltre l'`rqS` cancellato dal grant).
Con `i₁ = i₂` la cache riceve `rsS` e `rqIσ` in ordine opposto sui due lati: in `I` prende
il grant e poi cede (2 + 2 passi), in `S` cede e poi prende il grant; in `M` è `not_reachable_of_M`. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (Or.inr (Or.inr (not_reachable_of_not_synced hsync))))
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
        (not_reachable_of_M hst (Or.inr (Or.inr (by rw [hS]; intro h; cases h)))))))
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
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (not_reachable_of_M hst (Or.inr (Or.inr (hnoM i₁))))))))
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
theorem comm_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_to_M_invalid_all2_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₁) i₁)) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₁) i₁)) s''' ∧
    msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k₂) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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



/-! # Commutazione cache–cache

Due passi interni della stessa cache `i` applicati allo stesso stato, una coppia per ognuna delle
36 combinazioni non ordinate degli 8 eventi interni di cache, a livello di `MSIState`. Enunciato di base:
diamante, oppure `s' = s''`, oppure `¬ MSI.reachable s`. Dove serve il parent per riconvergere l'enunciato
dà il percorso (richiesta → downgrade → grant → presa → servizio, 5 o 5 + 5 passi, come in `MI`);
le riacquisizioni di `S` riportano il valore del parent, quindi valgono se la copia era aggiornata
(`v = s.parent.value`). Senza una regola di scarto, un invalidate stantio resta in coda: gli
enunciati lo dicono con `dropSt`. La load servita (in `S` o in `M`) e la store servita in `M` sono
eventi *esterni* (`cache_msi_step`): i loro diagrammi stanno nella sezione esterno–interno. -/

/-- Due rilasci spontanei da `M` della stessa cache `i`: entrambi accodano `rsIμ value`
e portano la cache in `I`, quindi i due stati di arrivo coincidono (`s' = s''`). -/
theorem comm_rq_data_not_available_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .rq_data_not_available i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_downgrade_from_M_rs {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .rq_data_not_available i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .rq_data_not_available i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .ld_rq_data_not_availableS i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .ld_rq_data_not_availableS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_rq_data_not_available1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq_upgrade_from_I_rs {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
            exact Or.inr (Or.inr (not_reachable_of_mu_rowJ (Ne.symm hki) (muMsgs_ne_zero_of_rsM hj') hkI))

/-- Richiesta di `M` e presa del grant di `S` dalla stessa cache `i` in `I`: dopo la presa la
cache è in `S`, quindi la richiesta non è più abilitata; da `s'` invece la presa (stessa posizione
`j`, stato ancora `I`) porta esattamente a `reqMSt s'' i` (quarto disgiunto, per estensionalità). -/
theorem comm_upgrade_from_I_rq_upgrade_from_I_rsS {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rq i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (Or.inr (not_reachable_of_not_synced hsync)))
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
              (not_reachable_of_sig_rowM (Ne.symm hki) (sigMsgs_ne_zero_of_rsS hj') (Classical.not_not.mp hkM))))

/-- Coppia vuota: la richiesta `rqS` vuole la cache `i` in `I`, l'invalidate ricevuto in `M`
(`downgrade_from_M_rs`) la vuole in `M`. -/
theorem comm_upgrade_from_I_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .upgrade_from_I_rqS i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .upgrade_from_I_rqS i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
cioè `2 ≤ muMsgs`, vista cattiva `not_reachable_of_two_mu`. -/
theorem comm_upgrade_from_I_rs_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
            exact Or.inr (Or.inr (not_reachable_of_two_mu hmu))

/-- Presa del grant `rsM` e presa del grant `rsS` sulla stessa cache `i`: un token `M` e un token `S`
in volo per `i` sul lato parent (via `synced`), vista cattiva `not_reachable_of_mu_sig`. -/
theorem comm_upgrade_from_I_rs_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
          exact Or.inr (Or.inr (not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsM hj₁) (sigMsgs_ne_zero_of_rsS hj₂)))

/-- Presa del grant `rsM` (cache in `I`) e `downgrade_from_M_rs` (cache in `M`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem comm_upgrade_from_I_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rs v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
cioè `2 ≤ sigMsgs`, vista cattiva `not_reachable_of_two_sig`. -/
theorem comm_upgrade_from_I_rsS_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₁) i) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v₁) i) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
            exact Or.inr (Or.inr (not_reachable_of_two_sig hsig))

/-- Presa del grant `rsS` (cache in `I`) e `downgrade_from_M_rs` (cache in `M`) sulla stessa cache `i`:
le guardie sullo stato si contraddicono, caso vuoto. -/
theorem comm_upgrade_from_I_rsS_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_upgrade_from_I_rsS_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache (.upgrade_from_I_rsS v) i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.cache .downgrade_from_M_rs i) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i) s'' →
  (∃ s''',
    msi_step_internal s'' (.cache .downgrade_from_M_rs i) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
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
theorem comm_downgrade_from_M_rs1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
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
    ¬ MSI.reachable s := by
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



/-! # Commutazione parent–cache

Un passo del parent (`.parent (.upd_queue e i₁)`) e un passo interno di una cache (`.cache e' i₂`)
applicati allo stesso stato; 7 × 8 = 56 coppie, ordinate per evento del parent e poi per evento
della cache, ognuna con `i₁ = i₂` e `i₁ ≠ i₂`. Enunciato uniforme: diamante, oppure `s' = s''`,
oppure `¬ MSI.reachable s`. -/

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio spontaneo
della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂` la cache è in `M`
mentre il suo rilascio è già in volo: vista cattiva (`not_reachable_of_M`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
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
mentre un suo rilascio da `M` è ancora in volo: vista cattiva (`not_reachable_of_S`). Con `i₁ ≠ i₂` i due
passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
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
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
vista cattiva (`not_reachable_of_two_mu`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        refine Or.inr (Or.inr (not_reachable_of_two_mu (i := i₁) ?_))
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
indice: vista cattiva (`not_reachable_of_mu_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v₂) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsIμ hj) (sigMsgs_ne_zero_of_rsS hj')))
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
la cache è in `M` mentre il suo rilascio è già in volo: vista cattiva (`not_reachable_of_M`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
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
cache è in `S` mentre un suo rilascio con token `M` è già in volo: vista cattiva (`not_reachable_of_S`).
Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inl (muMsgs_ne_zero_of_rsIμ hj))))
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
è in `M` mentre il suo rilascio `S` è già in volo: vista cattiva (`not_reachable_of_M`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
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
è in `S` mentre il suo rilascio `S` è già in volo: vista cattiva (`not_reachable_of_S`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
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
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
indice: vista cattiva (`not_reachable_of_mu_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_mu_sig (muMsgs_ne_zero_of_rsM hj') (sigMsgs_ne_zero_of_rsIσ hj)))
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
(`not_reachable_of_two_sig`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        refine Or.inr (Or.inr (not_reachable_of_two_sig (i := i₁) ?_))
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
(`not_reachable_of_M`). Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
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
cache è in `S` mentre un suo rilascio con token `S` è già in volo: vista cattiva (`not_reachable_of_S`).
Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .downgrade_from_S_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsIσ hj)))))
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
cache è in `M` mentre la riga la dà a `I`: vista cattiva (`not_reachable_of_M`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inr (by simp [hall i₁])))))
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
cache è in `S` mentre la riga la dà a `I`: vista cattiva (`not_reachable_of_S`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inr (Or.inr (by simp [hall i₁])))))
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
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
`i₁` mentre la riga `i₁` è a `I`: vista cattiva (`not_reachable_of_mu_row`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hg) (by simp [hall i₁])))
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
`i₁` mentre la riga `i₁` è a `I`: vista cattiva (`not_reachable_of_sig_row`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_sig_row (sigMsgs_ne_zero_of_rsS hg) (by simp [hall i₁])))
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
(`not_reachable_of_M`). Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inr (by simp [hall i₁])))))
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
`i₁ = i₂` la cache è in `S` mentre la riga `i₁` è a `I`: vista cattiva (`not_reachable_of_S`). Con
`i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_S hS (Or.inr (Or.inr (by simp [hall i₁])))))
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
la cache è in `M` mentre la riga non è a `M`: vista cattiva (`not_reachable_of_M`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi: diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inr (hnoM i₁)))))
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
theorem comm_upgrade_to_M_data_avilable_rq2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hrowI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  -- la nuova guardia del grant: la riga di `i₁` era a `I`
  have hrowI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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

/-- Grant di `S` del parent su `i₁` (consuma un `rqS`, nessuna riga a `M`) e presa del grant
di `M` da parte della cache `i₂` (consuma un `rsM v` da `queue_pc`). Con `i₁ = i₂` c'è un
`rsM` in volo verso `i₁` mentre la riga `i₁` non è a `M`: vista cattiva 2 (`not_reachable_of_mu_row`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hIrow := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_mu_row (muMsgs_ne_zero_of_rsM hg) (hnoM i₁)))
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
theorem comm_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hrow := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
Con `i₁ = i₂` la cache è in `M` mentre la riga non è a `M`: vista cattiva (`not_reachable_of_M`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi: diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
        exact Or.inr (Or.inr (not_reachable_of_M hM (Or.inr (Or.inr (hnoM i₁)))))
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
theorem comm_upgrade_to_M_data_avilable_rq2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  have hI := grantS_rowI h₁
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all1_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue .invalid_allS i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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
theorem comm_upgrade_to_M_invalid_all2_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''',
    msi_step_internal s'' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₁)) s''' ∧
    msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: via d'uscita esplicita
    exact Or.inr (Or.inr (not_reachable_of_not_synced hsync))
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


/-! # Commutazione esterno–interno

Il passo *esterno* di sistema `msi_step_external`: la cache `i` riceve un evento esterno
(`cache_msi_step`, cinque regole). Le *richieste* `ld_rq` e `st_rq v` accodano in fondo a
`extqueue.rq`; i *servizi* `ld_rs` (load servita in `S` o in `M`, due regole con lo stesso evento:
consuma la testa `ld_rq` di `rq` e accoda `ld_rs value` a `rs`) e `st_rs` (store servita in `M`:
consuma la testa `st_rq v` e scrive `value := v`). Come nel
passo interno di cache, le copie delle code lato parent vengono riallineate (un passo esterno non
tocca `queue_cp`/`queue_pc`, quindi su uno stato `synced` il riallineamento è l'identità).

Un teorema per coppia di eventi, come nelle sezioni precedenti (4 × 15 = 60):
* **esterno–parent (4 × 7)**: sempre il diamante su stati `synced` (`comm_ext_parent_generic`: il
  parent non guarda `state`, `value` ed `extqueue` della cache, il passo esterno non tocca le code
  interne), con la via d'uscita `¬ MSI.reachable s` (`not_reachable_of_not_synced`);
* **richieste–cache (2 × 8)**: diamante puro (`comm_ext_cache_generic`), senza via d'uscita;
* **servizi–cache (2 × 8)**: con indici diversi il diamante (`comm_ext_cache_ne`); sulla stessa
  cache i servizi leggono lo stato e la testa di `rq`, quindi valgono gli enunciati della sezione
  cache–cache: coppie vuote (guardie incompatibili, `comm_ext_cache_of_incompatible`) e le sei
  riconvergenze "a meno di un giro di linea" (rilascio o invalidate contro il servizio, in `S` e in
  `M`), con `¬ MSI.reachable s` come uscita. -/

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem msi_step_external_congr {n} {s s' s'' : MSIState n} {t : MSIExternalEvent n}
    (h : msi_step_external s t s') (heq : s' = s'') : msi_step_external s t s'' := heq ▸ h

/-- Inversione del passo esterno. -/
theorem ext_inv {n} {s s' : MSIState n} {e : Event} {i : Fin n}
    (h : msi_step_external s (.cache e i) s') :
    ∃ c', cache_msi_step (s.caches i) e c' ∧
      s' = { s with caches := update_Fin i c' s.caches,
                    parent.queue_cip := update_Fin i c'.queue_cp s.parent.queue_cip,
                    parent.queue_pci := update_Fin i c'.queue_pc s.parent.queue_pci } := by
  cases h
  exact ⟨_, ‹_›, rfl⟩

/-- Un passo esterno non tocca lo stato di coerenza né le code interne `queue_cp`/`queue_pc`
(le richieste toccano solo `extqueue`; la store servita anche `value`). -/
theorem cache_msi_step_frame {c c' : CacheState} {e : Event} (h : cache_msi_step c e c') :
    c'.state = c.state ∧ c'.queue_cp = c.queue_cp ∧ c'.queue_pc = c.queue_pc := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- Un passo esterno non guarda `queue_cp`/`queue_pc`: si trasporta lungo il loro aggiornamento. -/
theorem cache_msi_step_queues {c c' : CacheState} {e : Event} (h : cache_msi_step c e c')
    (qcp : List CPEvent) (qpc : List PCEvent) :
    cache_msi_step { c with queue_cp := qcp, queue_pc := qpc } e
      { c' with queue_cp := qcp, queue_pc := qpc } := by
  cases h with
  | ld_rq => exact cache_msi_step.ld_rq _
  | st_rq => exact cache_msi_step.st_rq _ _
  | ld_rq_data_available1 => exact cache_msi_step.ld_rq_data_available1 _ _ ‹_› ‹_›
  | ld_rq_data_available => exact cache_msi_step.ld_rq_data_available _ _ ‹_› ‹_›
  | st_rq_M_state => exact cache_msi_step.st_rq_M_state _ _ _ ‹_› ‹_›

/-- Le due *richieste* esterne (`ld_rq`, `st_rq v`). -/
abbrev isRequest (e : Event) : Prop := e = Event.ld_rq ∨ ∃ v, e = Event.st_rq v

/-- **Commutazione al livello della singola cache** per le richieste esterne: accodano in fondo a
`rq` senza guardare lo stato, quindi si chiudono in un passo con ogni regola interna (16 casi). -/
theorem cache_comm {c c₁ c₂ : CacheState} {e : Event} {r : CacheInternalEvent} (he : isRequest e)
    (h₁ : cache_msi_step c e c₁) (h₂ : cache_msi_step_internal c r c₂) :
    ∃ c₃, cache_msi_step_internal c₁ r c₃ ∧ cache_msi_step c₂ e c₃ := by
  cases h₁ <;> cases h₂
  -- esterno `ld_rq`
  case ld_rq.rq_data_not_available =>
    exact ⟨_, .rq_data_not_available _ ‹_›, .ld_rq _⟩
  case ld_rq.rq_data_not_available1 =>
    exact ⟨_, .rq_data_not_available1 _ ‹_›, .ld_rq _⟩
  case ld_rq.upgrade_from_I_rq =>
    exact ⟨_, .upgrade_from_I_rq _ ‹_›, .ld_rq _⟩
  case ld_rq.upgrade_from_I_rq1 =>
    exact ⟨_, .upgrade_from_I_rq1 _ ‹_›, .ld_rq _⟩
  case ld_rq.upgrade_from_I_rs =>
    rename_i v j hj hI
    exact ⟨_, .upgrade_from_I_rs _ v j hj hI, .ld_rq _⟩
  case ld_rq.upgrade_from_I_rsS =>
    rename_i v j hj hI
    exact ⟨_, .upgrade_from_I_rsS _ v j hj hI, .ld_rq _⟩
  case ld_rq.downgrade_from_M_rs =>
    rename_i j hj hM
    exact ⟨_, .downgrade_from_M_rs _ j hj hM, .ld_rq _⟩
  case ld_rq.downgrade_from_M_rs1 =>
    rename_i j hj hS
    exact ⟨_, .downgrade_from_M_rs1 _ j hj hS, .ld_rq _⟩
  -- esterno `st_rq x`
  case st_rq.rq_data_not_available =>
    exact ⟨_, .rq_data_not_available _ ‹_›, .st_rq _ _⟩
  case st_rq.rq_data_not_available1 =>
    exact ⟨_, .rq_data_not_available1 _ ‹_›, .st_rq _ _⟩
  case st_rq.upgrade_from_I_rq =>
    exact ⟨_, .upgrade_from_I_rq _ ‹_›, .st_rq _ _⟩
  case st_rq.upgrade_from_I_rq1 =>
    exact ⟨_, .upgrade_from_I_rq1 _ ‹_›, .st_rq _ _⟩
  case st_rq.upgrade_from_I_rs =>
    rename_i v j hj hI
    exact ⟨_, .upgrade_from_I_rs _ v j hj hI, .st_rq _ _⟩
  case st_rq.upgrade_from_I_rsS =>
    rename_i v j hj hI
    exact ⟨_, .upgrade_from_I_rsS _ v j hj hI, .st_rq _ _⟩
  case st_rq.downgrade_from_M_rs =>
    rename_i j hj hM
    exact ⟨_, .downgrade_from_M_rs _ j hj hM, .st_rq _ _⟩
  case st_rq.downgrade_from_M_rs1 =>
    rename_i j hj hS
    exact ⟨_, .downgrade_from_M_rs1 _ j hj hS, .st_rq _ _⟩
  -- i servizi (`ld_rs`, `st_rs`) sono esclusi da `he`
  all_goals (rcases he with he | ⟨_, he⟩ <;> cases he)

/-- Aggiornare due indici distinti commuta. -/
theorem comm_ext_cache_generic_aux_update_Fin_comm {α : Type} {n} (a b : Fin n) (x y : α)
    (f : Fin n → α) (hab : ¬ a = b) :
    update_Fin a x (update_Fin b y f) = update_Fin b y (update_Fin a x f) := by
  funext k
  by_cases hka : k = a
  · subst hka; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ hab]
  · by_cases hkb : k = b
    · subst hkb; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hab)]
    · simp [update_Fin_gso2 _ _ _ _ hka, update_Fin_gso2 _ _ _ _ hkb]

/-- **Esterno / cache su indici diversi**: diamante puro, per ogni evento esterno e ogni regola. -/
theorem comm_ext_cache_ne {n} {s s' s'' : MSIState n} {e : Event} {r : CacheInternalEvent}
    {i₁ i₂ : Fin n} (hii : ¬ i₁ = i₂)
    (h₁ : msi_step_external s (.cache e i₁) s') (h₂ : msi_step_internal s (.cache r i₂) s'') :
    ∃ s''', msi_step_external s'' (.cache e i₁) s''' ∧ msi_step_internal s' (.cache r i₂) s''' := by
  obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
  cases h₂
  rename_i c₂ hc₂
  refine ⟨_, msi_step_external.cache _ e c₁ i₁ (by simp only [update_Fin_gso2 _ _ _ _ hii]; exact hc₁), ?_⟩
  refine msi_step_congr (msi_step_internal.cache _ c₂ i₂ r
    (by simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hii)]; exact hc₂)) ?_
  refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · rfl
  · intro k; rfl
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]

/-- **Richiesta esterna / cache**: diamante puro, per ogni regola di cache e ogni coppia di indici. -/
theorem comm_ext_cache_generic {n} {s s' s'' : MSIState n} {e : Event} {r : CacheInternalEvent}
    {i₁ i₂ : Fin n} (he : isRequest e)
    (h₁ : msi_step_external s (.cache e i₁) s') (h₂ : msi_step_internal s (.cache r i₂) s'') :
    ∃ s''', msi_step_external s'' (.cache e i₁) s''' ∧ msi_step_internal s' (.cache r i₂) s''' := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    obtain ⟨c₃, h₃, h₄⟩ := cache_comm he hc₁ hc₂
    refine ⟨_, msi_step_external.cache _ e c₃ i₁ (by simp only [update_Fin_gss]; exact h₄), ?_⟩
    refine msi_step_congr (msi_step_internal.cache _ c₃ i₁ r (by simp only [update_Fin_gss]; exact h₃)) ?_
    refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
    · intro k; simp only [update_Fin_update_Fin_same]
    · rfl
    · intro k; rfl
    · intro k; simp only [update_Fin_update_Fin_same]
    · intro k; simp only [update_Fin_update_Fin_same]
  · exact comm_ext_cache_ne hii h₁ h₂

/-- **Esterno / parent**: diamante su stati `synced` (le copie delle code lato parent sono
allineate, quindi il riallineamento del passo esterno è l'identità e le guardie del parent non
cambiano). -/
theorem comm_ext_parent_generic {n} {s s' s'' : MSIState n} {e : Event}
    {pe : ParentUpdQueueInternalEvent n} {i₁ i₂ : Fin n} (hs : synced s)
    (h₁ : msi_step_external s (.cache e i₁) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue pe i₂)) s'') :
    ∃ s''', msi_step_external s'' (.cache e i₁) s''' ∧
            msi_step_internal s' (.parent (.upd_queue pe i₂)) s''' := by
  obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
  obtain ⟨_, hcp, hpc⟩ := cache_msi_step_frame hc₁
  cases h₂
  rename_i parent' hp
  -- il parent di `s'` è `s.parent`: la ricopiatura delle code è l'identità su stati `synced`
  have hq1 : update_Fin i₁ c₁.queue_cp s.parent.queue_cip = s.parent.queue_cip := by
    rw [hcp, ← (hs i₁).1]; exact update_Fin_self _ _
  have hq2 : update_Fin i₁ c₁.queue_pc s.parent.queue_pci = s.parent.queue_pci := by
    rw [hpc, ← (hs i₁).2]; exact update_Fin_self _ _
  by_cases hii : i₁ = i₂
  · subst hii
    refine ⟨_, msi_step_external_congr
        (msi_step_external.cache _ e
          { c₁ with queue_cp := parent'.queue_cip i₁, queue_pc := parent'.queue_pci i₁ } i₁ ?h) ?eq,
      msi_step_internal.parent_upd_queue _ parent' pe i₁ (by simp only [hq1, hq2]; exact hp)⟩
    case h =>
      simp only [update_Fin_gss]
      exact cache_msi_step_queues hc₁ _ _
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk : k = i₁
        · subst hk; simp only [update_Fin_gss]
        · simp only [update_Fin_gso2 _ _ _ _ hk]
      · rfl
      · intro k; rfl
      · intro k; simp only [update_Fin_self]
      · intro k; simp only [update_Fin_self]
  · have hne' : ¬ i₂ = i₁ := fun h => hii h.symm
    obtain ⟨hl1, hl2, _⟩ := parent_step_local hp i₁ hii
    have hcp' : c₁.queue_cp = parent'.queue_cip i₁ := by rw [hcp, ← (hs i₁).1, hl1]
    have hpc' : c₁.queue_pc = parent'.queue_pci i₁ := by rw [hpc, ← (hs i₁).2, hl2]
    refine ⟨_, msi_step_external_congr (msi_step_external.cache _ e c₁ i₁ ?h) ?eq,
      msi_step_internal.parent_upd_queue _ parent' pe i₂ (by simp only [hq1, hq2]; exact hp)⟩
    case h =>
      simp only [update_Fin_gso2 _ _ _ _ hii]
      exact hc₁
    case eq =>
      refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
      · intro k
        by_cases hk₁ : k = i₁
        · subst hk₁; simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hii]
        · by_cases hk₂ : k = i₂
          · subst hk₂; simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
          · simp only [update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
      · rfl
      · intro k; rfl
      · intro k; simp only [hcp', update_Fin_self]
      · intro k; simp only [hpc', update_Fin_self]

/-! ## Esterno–parent (4 × 7): diamante su stati `synced`, altrimenti `¬ MSI.reachable s` -/

theorem comm_ext_ld_rq_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rq_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rq_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_ld_rs_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_downgrade_from_M_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_downgrade_from_M_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_upgrade_to_M_data_avilable_rq2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_upgrade_to_M_invalid_all {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_upgrade_to_M_invalid_all1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue .invalid_allS i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue .invalid_allS i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

theorem comm_ext_st_rs_upgrade_to_M_invalid_all2 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.parent (.upd_queue (.upgrade_to_S_invalid_2_rq1S k) i₂)) s''')
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hs : synced s
  · exact Or.inl (comm_ext_parent_generic hs h₁ h₂)
  · exact Or.inr (not_reachable_of_not_synced hs)

/-! ## Richieste esterne–cache (2 × 8): diamante puro, senza via d'uscita -/

theorem comm_ext_ld_rq_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .rq_data_not_available i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_ld_rq_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .ld_rq i₁) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .ld_rq i₁) s''' ∧
          msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inl rfl) h₁ h₂

theorem comm_ext_st_rq_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .rq_data_not_available i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

theorem comm_ext_st_rq_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.st_rq w) i₁) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.st_rq w) i₁) s''' ∧
          msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_generic (Or.inr ⟨_, rfl⟩) h₁ h₂

/-! ## Servizi esterni–cache (2 × 8): indici diversi diamante; stessa cache come in cache–cache -/

/-- **Esterno / cache con guardie incompatibili**: con indici diversi il diamante
(`comm_ext_cache_ne`); sulla stessa cache la coppia è vuota (`hinc`), quindi il diamante vale a vuoto. -/
theorem comm_ext_cache_of_incompatible {n} {s s' s'' : MSIState n} {e : Event} {r : CacheInternalEvent}
    {i₁ i₂ : Fin n}
    (hinc : ∀ {c c₁ c₂ : CacheState}, cache_msi_step c e c₁ → cache_msi_step_internal c r c₂ → False)
    (h₁ : msi_step_external s (.cache e i₁) s') (h₂ : msi_step_internal s (.cache r i₂) s'') :
    ∃ s''', msi_step_external s'' (.cache e i₁) s''' ∧ msi_step_internal s' (.cache r i₂) s''' := by
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂; rename_i c₂ hc₂
    exact (hinc hc₁ hc₂).elim
  · exact comm_ext_cache_ne hii h₁ h₂

/-- **Load esterna / rilascio spontaneo da `M`.** Indici diversi: diamante. Stessa cache: se la load
è servita in `S` la coppia è vuota (`S` contro `M`); se è servita in `M`, dopo il rilascio la load
aspetta che la linea torni: da `s''` la cache (ora in `I`) richiede `rqM`, il parent consuma l'`rsIμ`
con il valore `w`, concede `rsM w`, la cache riprende `M` e serve la load. Le cache coincidono con
`s'` (i parent no). La concessione vuole tutte le righe a `I`: una riga `k ≠ i₂` non a `I` con la
cache in `M` è la vista cattiva `not_reachable_of_M_rowJ`. -/
theorem comm_ext_ld_rs_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅,
      msi_step_internal s'' (.cache .upgrade_from_I_rq i₂) t₁ ∧
      msi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 w) i₂)) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₃ ∧
      msi_step_internal t₃ (.cache (.upgrade_from_I_rs w) i₂) t₄ ∧
      msi_step_external t₄ (.cache (.ld_rs w) i₁) t₅ ∧
      s'.caches = t₅.caches)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | ld_rq_data_available1 _ _ hS =>
      cases hc₂ with
      | rq_data_not_available hM' => exact Bstate.noConfusion (hS.symm.trans hM')
    | ld_rq_data_available rst hrq hM =>
      cases hc₂ with
      | rq_data_not_available hM' =>
        by_cases hall : ∀ k, k ≠ i₁ → s.parent.shared_state k = Bstate.I
        · -- tutte le altre righe della directory sono a `I`: il cammino esplicito da `s''`
          refine Or.inr (Or.inl ⟨_, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
            msi_step_internal.cache _ ?c2 _ _ ?p4,
            msi_step_external.cache _ _ ?c3 _ ?p5,
            ?eq⟩)
          -- 1. la cache, ora in `I`, torna a chiedere la linea (`rqM`)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- 2. il parent consuma l'`rsIμ w`: riga `i := I`, `value := w`
          case p2 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- 3. il parent consuma l'`rqM` e risponde `rsM w`: la directory è tutta a `I`
          case p3 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- 4. la cache riprende la linea in `M` con il valore `w`
          case p4 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ (s.caches i₁).queue_pc.length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- 5. la load è servita in `M`
          case p5 =>
            simp only [update_Fin_gss, lst_erase]
            refine .ld_rq_data_available _ rst ?_ ?_
            · exact hrq
            · rfl
          -- le cache coincidono: code riallineate, `extqueue` uguale
          case eq =>
            funext k
            by_cases hk : k = i₁
            · subst hk
              simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
            · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- una riga `k ≠ i` non è a `I` mentre la cache `i` è in `M`: vista cattiva
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkI⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (not_reachable_of_M_rowJ (Ne.symm hki) hM hkI))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Load esterna / rilascio spontaneo da `S` commutano "a meno di un giro di linea".** Se la load è
servita in `M` la coppia è vuota (`M` contro `S`). Servita in `S`:
Indici diversi: diamante. Stessa cache: da `s''` (rilasciato `rsIσ`) la cache richiede `S`, il parent
consuma il rilascio e riconcede `S` con il proprio valore, la cache riprende la linea e serve la
load: le cache coincidono con `s'` se la load restituiva proprio `s.parent.value` (altrimenti vale
il disgiunto `¬(w = s.parent.value)`). La concessione vuole nessuna riga a `M`: le altre righe non lo
sono, oppure `s` ha una vista cattiva (cache in `S` con una riga `k ≠ i₂` a `M`). -/
theorem comm_ext_ld_rs_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅,
      msi_step_internal s'' (.cache .upgrade_from_I_rqS i₂) t₁ ∧
      msi_step_internal t₁ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) t₃ ∧
      msi_step_internal t₃ (.cache (.upgrade_from_I_rsS w) i₂) t₄ ∧
      msi_step_external t₄ (.cache (.ld_rs w) i₁) t₅ ∧
      s'.caches = t₅.caches)
  ∨ ¬(w = s.parent.value)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | ld_rq_data_available _ _ hM =>
      cases hc₂ with
      | rq_data_not_available1 hS' => exact Bstate.noConfusion (hM.symm.trans hS')
    | ld_rq_data_available1 rst hrq hS =>
      cases hc₂ with
      | rq_data_not_available1 hS' =>
        -- il grant porta il valore del parent: se la load restituiva altro, terzo disgiunto
        by_cases hv : (s.caches i₁).value = s.parent.value
        swap
        · exact Or.inr (Or.inr (Or.inl hv))
        by_cases hall : ∀ k, k ≠ i₁ → ¬ s.parent.shared_state k = Bstate.M
        · -- nessun'altra riga a `M`: il cammino esplicito da `s''`
          refine Or.inr (Or.inl ⟨_, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
            msi_step_internal.cache _ ?c2 _ _ ?p4,
            msi_step_external.cache _ _ ?c3 _ ?p5,
            ?eq⟩)
          -- 1. la cache, ora in `I`, torna a chiedere la linea (`rqS`)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq1 _ ?_
            rfl
          -- 2. il parent consuma l'`rsIσ`: riga `i := I`
          case p2 =>
            refine .downgrade_from_M_rq2 _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- 3. il parent consuma l'`rqS` e risponde `rsS s.parent.value`: riga `i` a `I`, nessuna a `M`
          case p3 =>
            refine .upgrade_to_M_data_avilable_rq2 _ _ (s.caches i₁).queue_cp.length ?_ ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · simp only [update_Fin_gss]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
                exact fun h => Bstate.noConfusion h
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- 4. la cache riprende la linea in `S` con il valore del parent
          case p4 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rsS _ _ (s.caches i₁).queue_pc.length ?_ ?_
            · rw [hv]
              exact lst_get _ _
            · rfl
          -- 5. la load è servita in `S`
          case p5 =>
            simp only [update_Fin_gss, lst_erase]
            refine .ld_rq_data_available1 _ rst ?_ ?_
            · exact hrq
            · rfl
          -- le cache coincidono: code riallineate, `extqueue` uguale
          case eq =>
            funext k
            by_cases hk : k = i₁
            · subst hk
              simp only [update_Fin_gss, lst_erase, lst_erase2, hS]
            · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- una riga `k ≠ i` è a `M` mentre la cache `i` è in `S`: vista cattiva 5
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (Or.inr
            (not_reachable_of_S_rowM (Ne.symm hki) hS (Classical.not_not.mp hkM))))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Load esterna (in `S` o in `M`) / richiesta di `M` da `I`.** Indici diversi: diamante. Stessa cache: coppia vuota (`S` o `M` contro `I`). -/
theorem comm_ext_ld_rs_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁ <;> cases hc₂ <;> simp_all) h₁ h₂

/-- **Load esterna (in `S` o in `M`) / richiesta di `S` da `I`.** Indici diversi: diamante. Stessa cache: coppia vuota (`S` o `M` contro `I`). -/
theorem comm_ext_ld_rs_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁ <;> cases hc₂ <;> simp_all) h₁ h₂

/-- **Load esterna (in `S` o in `M`) / presa del grant di `M`.** Indici diversi: diamante. Stessa cache: coppia vuota (`S` o `M` contro `I`). -/
theorem comm_ext_ld_rs_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁ <;> cases hc₂ <;> simp_all) h₁ h₂

/-- **Load esterna (in `S` o in `M`) / presa del grant di `S`.** Indici diversi: diamante. Stessa cache: coppia vuota (`S` o `M` contro `I`). -/
theorem comm_ext_ld_rs_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁ <;> cases hc₂ <;> simp_all) h₁ h₂

/-- **Load esterna / invalidate `rqIμ` ricevuto in `M`.** Indici diversi: diamante. Stessa cache:
se la load è servita in `S` la coppia è vuota (`S` contro `M`); se è servita in `M` non commutano
direttamente: da `s'` la cache cede `w` (stessa posizione `j`), richiede, il parent registra e
concede, la cache riprende `M` con `w`; da `s''` la cache richiede, il parent registra `w` e
concede, la cache riprende `M` e serve la load. I due stati finali coincidono. Una riga `k ≠ i₂`
non a `I` è `not_reachable_of_M_rowJ`. -/
theorem comm_ext_ld_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄ u₅,
      msi_step_internal s'  (.cache .downgrade_from_M_rs i₂) t₁ ∧
      msi_step_internal t₁ (.cache .upgrade_from_I_rq i₂) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 w) i₂)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rs w) i₂) t₅ ∧
      msi_step_internal s'' (.cache .upgrade_from_I_rq i₂) u₁ ∧
      msi_step_internal u₁ (.parent (.upd_queue (.downgrade_from_M_rq1 w) i₂)) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) u₃ ∧
      msi_step_internal u₃ (.cache (.upgrade_from_I_rs w) i₂) u₄ ∧
      msi_step_external u₄ (.cache (.ld_rs w) i₁) u₅ ∧
      t₅ = u₅)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | ld_rq_data_available1 _ _ hS =>
      cases hc₂ with
      | downgrade_from_M_rs _ _ hM' => exact Bstate.noConfusion (hS.symm.trans hM')
    | ld_rq_data_available rst hrq hM =>
      cases hc₂ with
      | downgrade_from_M_rs j hj hM' =>
        by_cases hall : ∀ k, k ≠ i₁ → s.parent.shared_state k = Bstate.I
        · refine Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.cache _ ?c2 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
            msi_step_internal.cache _ ?c3 _ _ ?p5,
            msi_step_internal.cache _ ?c4 _ _ ?p6,
            msi_step_internal.parent_upd_queue _ ?q3 _ _ ?p7,
            msi_step_internal.parent_upd_queue _ ?q4 _ _ ?p8,
            msi_step_internal.cache _ ?c5 _ _ ?p9,
            msi_step_external.cache _ _ ?c6 _ ?p10,
            ?eq⟩)
          -- sinistra 1. la cache (dopo la load) cede la linea allo stesso `j` (rsIμ w)
          case p1 =>
            simp only [update_Fin_gss]
            refine .downgrade_from_M_rs _ j ?_ ?_
            · exact hj
            · exact hM
          -- sinistra 2. la cache (in `I`) richiede la linea (rqM)
          case p2 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- sinistra 3. il parent consuma l'rsIμ: riga `i := I`, value := w
          case p3 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- sinistra 4. il parent consuma l'rqM e concede la linea (rsM w)
          case p4 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- sinistra 5. la cache riprende la linea con w
          case p5 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- destra 1. la cache (già in `I`) richiede la linea (rqM)
          case p6 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- destra 2. il parent consuma l'rsIμ
          case p7 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- destra 3. il parent concede la linea
          case p8 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- destra 4. la cache riprende la linea con w
          case p9 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- destra 5. ora la load può essere servita
          case p10 =>
            simp only [update_Fin_gss, lst_erase]
            refine .ld_rq_data_available _ rst ?_ ?_
            · exact hrq
            · rfl
          -- i due stati finali coincidono, campo per campo
          case eq =>
            refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- un'altra riga della directory non è a `I` mentre la cache `i` è in `M`: vista cattiva 5
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkI⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (not_reachable_of_M_rowJ (Ne.symm hki) hM hkI))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Load esterna / invalidate `rqIσ` ricevuto in `S`.** Se la load è servita in `M` la coppia è
vuota (`M` contro `S`). Servita in `S`, indici diversi: diamante.
Stessa cache: da `s'` (load già servita) si cede la linea e la si riprende in cinque passi
(cessione, `rqS`, `downgrade` da `S`, grant di `S`, presa del grant); da `s''` (linea già ceduta)
si fanno gli stessi quattro passi e poi la load: gli stati finali coincidono. Il grant porta il
valore del parent, quindi se `w ≠ s.parent.value` si esce con quel disgiunto; se un'altra riga della
directory è a `M` si esce con `¬ MSI.reachable s` (vista cattiva 5). -/
theorem comm_ext_ld_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache (.ld_rs w) i₁) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache (.ld_rs w) i₁) s''' ∧
           msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄ u₅,
      msi_step_internal s'  (.cache .downgrade_from_S_rsS i₂) t₁ ∧
      msi_step_internal t₁ (.cache .upgrade_from_I_rqS i₂) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rsS w) i₂) t₅ ∧
      msi_step_internal s'' (.cache .upgrade_from_I_rqS i₂) u₁ ∧
      msi_step_internal u₁ (.parent (.upd_queue .downgrade_from_S_rq1S i₂)) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) u₃ ∧
      msi_step_internal u₃ (.cache (.upgrade_from_I_rsS w) i₂) u₄ ∧
      msi_step_external u₄ (.cache (.ld_rs w) i₁) u₅ ∧
      t₅ = u₅)
  ∨ ¬(w = s.parent.value)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | ld_rq_data_available _ _ hM =>
      cases hc₂ with
      | downgrade_from_M_rs1 _ _ hS' => exact Bstate.noConfusion (hM.symm.trans hS')
    | ld_rq_data_available1 rst hrq hS =>
      cases hc₂ with
      | downgrade_from_M_rs1 j hj hS' =>
        -- il grant porta il valore del parent: se la load restituiva altro, terzo disgiunto
        by_cases hv : (s.caches i₁).value = s.parent.value
        swap
        · exact Or.inr (Or.inr (Or.inl hv))
        by_cases hall : ∀ k, k ≠ i₁ → ¬ s.parent.shared_state k = Bstate.M
        · -- nessun'altra riga a `M`: i due cammini espliciti
          refine Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.cache _ ?c2 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
            msi_step_internal.cache _ ?c3 _ _ ?p5,
            msi_step_internal.cache _ ?c4 _ _ ?p6,
            msi_step_internal.parent_upd_queue _ ?q3 _ _ ?p7,
            msi_step_internal.parent_upd_queue _ ?q4 _ _ ?p8,
            msi_step_internal.cache _ ?c5 _ _ ?p9,
            msi_step_external.cache _ _ ?c6 _ ?p10,
            ?eq⟩)
          -- sinistra 1. la cache (dopo la load) cede la linea allo stesso `j` (rsIσ)
          case p1 =>
            simp only [update_Fin_gss]
            refine .downgrade_from_M_rs1 _ j ?_ ?_
            · exact hj
            · exact hS
          -- sinistra 2. la cache (in `I`) richiede la linea (rqS)
          case p2 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq1 _ ?_
            rfl
          -- sinistra 3. il parent consuma l'rsIσ: riga `i := I`
          case p3 =>
            refine .downgrade_from_M_rq2 _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- sinistra 4. il parent consuma l'rqS e concede la linea (rsS s.parent.value)
          case p4 =>
            refine .upgrade_to_M_data_avilable_rq2 _ _ (s.caches i₁).queue_cp.length ?_ ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · simp only [update_Fin_gss]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
                exact fun h => Bstate.noConfusion h
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- sinistra 5. la cache prende la linea in `S` con il valore del parent
          case p5 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rsS _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · rw [hv]
              exact lst_get _ _
            · rfl
          -- destra 1. la cache (già in `I`) richiede la linea (rqS)
          case p6 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq1 _ ?_
            rfl
          -- destra 2. il parent consuma l'rsIσ
          case p7 =>
            refine .downgrade_from_M_rq2 _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- destra 3. il parent concede la linea
          case p8 =>
            refine .upgrade_to_M_data_avilable_rq2 _ _ (s.caches i₁).queue_cp.length ?_ ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · simp only [update_Fin_gss]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
                exact fun h => Bstate.noConfusion h
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- destra 4. la cache riprende la linea in `S` con il valore del parent
          case p9 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rsS _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · rw [hv]
              exact lst_get _ _
            · rfl
          -- destra 5. ora la load può essere servita in `S`
          case p10 =>
            simp only [update_Fin_gss, lst_erase]
            refine .ld_rq_data_available1 _ rst ?_ ?_
            · exact hrq
            · rfl
          -- i due stati finali coincidono, campo per campo
          case eq =>
            refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss, lst_erase]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- una riga `k ≠ i` è a `M` mentre la cache `i` è in `S`: vista cattiva 5
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (Or.inr
            (not_reachable_of_S_rowM (Ne.symm hki) hS (Classical.not_not.mp hkM))))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Store esterna (in `M`) / rilascio spontaneo da `M`.** Indici diversi: diamante. Stessa
cache: dopo il rilascio la store aspetta che la linea torni: da `s''` la cache (ora in `I`) richiede
`rqM`, il parent consuma l'`rsIμ` col valore vecchio, concede `rsM`, la cache riprende `M` e serve
la store. Le cache coincidono con `s'` (i parent no). La concessione vuole tutte le righe a `I`: una
riga `k ≠ i₂` non a `I` con la cache in `M` è la vista cattiva `not_reachable_of_M_rowJ`. -/
theorem comm_ext_st_rs_rq_data_not_available {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅,
      msi_step_internal s'' (.cache .upgrade_from_I_rq i₂) t₁ ∧
      msi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 (s.caches i₂).value) i₂)) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₃ ∧
      msi_step_internal t₃ (.cache (.upgrade_from_I_rs (s.caches i₂).value) i₂) t₄ ∧
      msi_step_external t₄ (.cache .st_rs i₁) t₅ ∧
      s'.caches = t₅.caches)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | st_rq_M_state v rst hrq hM =>
      cases hc₂ with
      | rq_data_not_available hM' =>
        by_cases hall : ∀ k, k ≠ i₁ → s.parent.shared_state k = Bstate.I
        · -- tutte le altre righe della directory sono a `I`: il cammino esplicito da `s''`
          refine Or.inr (Or.inl ⟨_, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
            msi_step_internal.cache _ ?c2 _ _ ?p4,
            msi_step_external.cache _ _ ?c3 _ ?p5,
            ?eq⟩)
          -- 1. la cache, ora in `I`, torna a chiedere la linea (`rqM`)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- 2. il parent consuma l'`rsIμ` col valore vecchio: riga `i := I`
          case p2 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- 3. il parent consuma l'`rqM` e risponde `rsM`: la directory è tutta a `I`
          case p3 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- 4. la cache riprende la linea in `M` con il valore vecchio
          case p4 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ (s.caches i₁).queue_pc.length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- 5. la store è servita in `M`
          case p5 =>
            simp only [update_Fin_gss, lst_erase]
            refine .st_rq_M_state _ v rst ?_ ?_
            · exact hrq
            · rfl
          -- le cache coincidono: code riallineate, `value` e `extqueue` uguali
          case eq =>
            funext k
            by_cases hk : k = i₁
            · subst hk
              simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
            · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- una riga `k ≠ i` non è a `I` mentre la cache `i` è in `M`: vista cattiva
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkI⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (not_reachable_of_M_rowJ (Ne.symm hki) hM hkI))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Store esterna (in `M`) / rilascio spontaneo da `S`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `S`). -/
theorem comm_ext_st_rs_rq_data_not_available1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .ld_rq_data_not_availableS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache .ld_rq_data_not_availableS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂

/-- **Store esterna (in `M`) / richiesta di `M` da `I`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `I`). -/
theorem comm_ext_st_rs_upgrade_from_I_rq {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂

/-- **Store esterna (in `M`) / richiesta di `S` da `I`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `I`). -/
theorem comm_ext_st_rs_upgrade_from_I_rq1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .upgrade_from_I_rqS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache .upgrade_from_I_rqS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂

/-- **Store esterna (in `M`) / presa del grant di `M`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `I`). -/
theorem comm_ext_st_rs_upgrade_from_I_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rs v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rs v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂

/-- **Store esterna (in `M`) / presa del grant di `S`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `I`). -/
theorem comm_ext_st_rs_upgrade_from_I_rsS {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache (.upgrade_from_I_rsS v) i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache (.upgrade_from_I_rsS v) i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂

/-- **Store esterna (in `M`) / invalidate `rqIμ` ricevuto in `M`.** Indici diversi: diamante.
Stessa cache, non commutano direttamente: da `s'` la cache cede `v` (stessa posizione `j`),
richiede, il parent registra e concede, la cache riprende `M` con `v`; da `s''` la cache richiede,
il parent registra il valore vecchio e concede, la cache riprende `M` e serve la store. Le cache
coincidono (i parent no). Una riga `k ≠ i₂` non a `I` è `not_reachable_of_M_rowJ`. -/
theorem comm_ext_st_rs_downgrade_from_M_rs {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
           msi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨ (∃ t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄ u₅,
      msi_step_internal s'  (.cache .downgrade_from_M_rs i₂) t₁ ∧
      msi_step_internal t₁ (.cache .upgrade_from_I_rq i₂) t₂ ∧
      msi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 (s'.caches i₂).value) i₂)) t₃ ∧
      msi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
      msi_step_internal t₄ (.cache (.upgrade_from_I_rs (s'.caches i₂).value) i₂) t₅ ∧
      msi_step_internal s'' (.cache .upgrade_from_I_rq i₂) u₁ ∧
      msi_step_internal u₁ (.parent (.upd_queue (.downgrade_from_M_rq1 (s.caches i₂).value) i₂)) u₂ ∧
      msi_step_internal u₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) u₃ ∧
      msi_step_internal u₃ (.cache (.upgrade_from_I_rs (s.caches i₂).value) i₂) u₄ ∧
      msi_step_external u₄ (.cache .st_rs i₁) u₅ ∧
      t₅.caches = u₅.caches)
  ∨ ¬ MSI.reachable s := by
  intro h₁ h₂
  by_cases hii : i₁ = i₂
  · subst hii
    obtain ⟨c₁, hc₁, rfl⟩ := ext_inv h₁
    cases h₂
    rename_i c₂ hc₂
    cases hc₁ with
    | st_rq_M_state v rst hrq hM =>
      cases hc₂ with
      | downgrade_from_M_rs j hj hM' =>
        by_cases hall : ∀ k, k ≠ i₁ → s.parent.shared_state k = Bstate.I
        · refine Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, _, _,
            msi_step_internal.cache _ ?c1 _ _ ?p1,
            msi_step_internal.cache _ ?c2 _ _ ?p2,
            msi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
            msi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
            msi_step_internal.cache _ ?c3 _ _ ?p5,
            msi_step_internal.cache _ ?c4 _ _ ?p6,
            msi_step_internal.parent_upd_queue _ ?q3 _ _ ?p7,
            msi_step_internal.parent_upd_queue _ ?q4 _ _ ?p8,
            msi_step_internal.cache _ ?c5 _ _ ?p9,
            msi_step_external.cache _ _ ?c6 _ ?p10,
            ?eq⟩)
          -- sinistra 1. la cache (dopo la store) cede la linea allo stesso `j` (rsIμ v)
          case p1 =>
            simp only [update_Fin_gss]
            refine .downgrade_from_M_rs _ j ?_ ?_
            · exact hj
            · exact hM
          -- sinistra 2. la cache (in `I`) richiede la linea (rqM)
          case p2 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- sinistra 3. il parent consuma l'rsIμ: riga `i := I`, value := v
          case p3 =>
            simp only [update_Fin_gss]
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- sinistra 4. il parent consuma l'rqM e concede la linea (rsM v)
          case p4 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- sinistra 5. la cache riprende la linea con v
          case p5 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- destra 1. la cache (già in `I`) richiede la linea (rqM)
          case p6 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- destra 2. il parent consuma l'rsIμ col valore vecchio
          case p7 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i₁).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- destra 3. il parent concede la linea
          case p8 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i₁).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              by_cases hk : k = i₁
              · subst hk; simp only [update_Fin_gss]
              · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
          -- destra 4. la cache riprende la linea con il valore vecchio
          case p9 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rs _ _ ((s.caches i₁).queue_pc.eraseIdx j).length ?_ ?_
            · exact lst_get _ _
            · rfl
          -- destra 5. ora la store può essere servita
          case p10 =>
            simp only [update_Fin_gss, lst_erase]
            refine .st_rq_M_state _ v rst ?_ ?_
            · exact hrq
            · rfl
          -- le cache dei due stati finali coincidono
          case eq =>
            funext k
            by_cases hk : k = i₁
            · subst hk
              simp only [update_Fin_gss, lst_erase, lst_erase2]
            · simp only [update_Fin_gso2 _ _ _ _ hk]
        · -- un'altra riga della directory non è a `I` mentre la cache `i` è in `M`: vista cattiva 5
          obtain ⟨k, hk⟩ := not_forall.mp hall
          obtain ⟨hki, hkI⟩ := Classical.not_imp.mp hk
          exact Or.inr (Or.inr (not_reachable_of_M_rowJ (Ne.symm hki) hM hkI))
  · exact Or.inl (comm_ext_cache_ne hii h₁ h₂)

/-- **Store esterna (in `M`) / invalidate ricevuto in `S`.** Indici diversi: diamante. Stessa cache: coppia vuota (`M` contro `S`). -/
theorem comm_ext_st_rs_downgrade_from_M_rs1 {s s' s'' : MSIState n} :
  msi_step_external s (.cache .st_rs i₁) s' →
  msi_step_internal s (.cache .downgrade_from_S_rsS i₂) s'' →
  ∃ s''', msi_step_external s'' (.cache .st_rs i₁) s''' ∧
          msi_step_internal s' (.cache .downgrade_from_S_rsS i₂) s''' :=
  fun h₁ h₂ => comm_ext_cache_of_incompatible
    (fun hc₁ hc₂ => by cases hc₁; cases hc₂; simp_all) h₁ h₂


---spec and flush relation


/- Stato dello spec sequenziale. Come nel resto del file l'indirizzo è unico e gli eventi non
portano `Ident`, quindi la memoria è un solo `Value` e non c'è il contatore `fresh_ident`;
per ogni cache resta la coda esterna `extqueue`. -/
-- structure SeqState (n : Nat) where
--   memory : Value
--   extqueue : Fin n -> RsRqEvent

-- instance : Inhabited (SeqState n) where
--   default := SeqState.mk default (fun _ => default)

-- /-- Quite a basic implementation of a sequential memory behaviour, where only
-- one request can be in flight at one time.  However, the hope would be that by
-- still allowing for event queues, that it could be extended to view out-of-order
-- events. -/
-- inductive seq_step : SeqState n -> MSIExternalEvent n -> SeqState n -> Prop where
--   | ld_rq : ∀ (s1 : SeqState n) i,
--       seq_step s1 (.cache Event.ld_rq i)
--         { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.ld_rq] } s1.extqueue }
--   | st_rq : ∀ (s1 : SeqState n) v i,
--       seq_step s1 (.cache (Event.st_rq v) i)
--         { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.st_rq v] } s1.extqueue }
--   | ld_rs : ∀ (s1 : SeqState n) v rst i,
--       (s1.extqueue i).rs = Event.ld_rs v :: rst →
--       seq_step s1 (.cache (Event.ld_rs v) i)
--         { s1 with extqueue := update_Fin i { s1.extqueue i with rs := rst } s1.extqueue }

-- inductive seq_internal_step : SeqState n -> MSIInternalEvent n -> SeqState n -> Prop where
--   | read : ∀ (s1 : SeqState n) v i rst,
--       (s1.extqueue i).rq = Event.ld_rq :: rst →
--       s1.memory = v ->
--       seq_internal_step s1 (MSIInternalEvent.cache (CacheInternalEvent.ld_rs v) i)
--         { s1 with extqueue := update_Fin i { s1.extqueue i with rs := (s1.extqueue i).rs ++ [Event.ld_rs v], rq := rst } s1.extqueue }
--   | write : ∀ (s1 : SeqState n) v i rst,
--       (s1.extqueue i).rq = Event.st_rq v :: rst →
--       seq_internal_step s1 (MSIInternalEvent.cache (CacheInternalEvent.st_rs v) i)
--         { s1 with extqueue := update_Fin i { s1.extqueue i with rq := rst } s1.extqueue, memory := v }

-- @[simp]
-- def seq_init (n : Nat) : SeqState n := Inhabited.default

-- def spec_behaviour (n : Nat) := behaviour_extend (seq_init n : SeqState n) seq_step seq_internal_step


-- /-inductive IFlush (i : MIState n) : Prop where
-- | Ii :
--     (∀ c, (i.caches c).queue_cp = ⟨[], []⟩ ∧ (i.caches c).queue_pc = []) ->
--     (∀ c, (i.caches c).cache.meta.state = Bstate.I) ->
--     (∀ c, i.parent.parent.meta.shared_state c = Bstate.I) ->
--     IFlush i
-- | Mi : ∀ c',
--     (∀ c, (i.caches c).queue_cp = ⟨[], []⟩ ∧ (i.caches c).queue_pc = []) ->
--     ((i.caches c').cache.meta.state = Bstate.M) ->
--     (∀ c'',  ¬(c'' = c') -> (i.caches c'').cache.meta.state = Bstate.I) ->
--     (∀ c'', ¬(c'' = c') -> i.parent.parent.meta.shared_state c'' = Bstate.I) ->
--     (i.parent.parent.meta.shared_state c' = Bstate.M) ->
--     (i.parent.parent.meta.state =  Bstate.M) ->
--     ((i.caches c').cache.meta.tag = i.parent.parent.meta.tag) ->
--     IFlush i
-- -/


-- theorem relation_flush (i i' : MSIState n) (s : B):
--   flush i s -> trans_refl msi_step_internal i i' -> flush i' s := by admit


-- theorem relation_flush_method (i i' : A) (s s' : B) e := flush i s -> method_i i e i' -> method_s s e s' ->
--                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'



-- theorem relation_method (i i' : A) (s : B) e := flush i s -> method_i i e i' -> ∃ s', method_s s e s'
