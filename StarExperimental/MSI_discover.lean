import StarExperimental.MSI
import StarExperimental.BackwardDiscover

/-! # `MSI_discover`: le viste cattive del modello a liste *scoperte*, e la parte usata dai 41

`MSI.lean` dimostra 185 teoremi di commutazione; 41 di essi chiudono un caso con una vista
cattiva, attraverso gli 11 lemmi ponte `not_reachable_of_*`, che a loro volta poggiano su
`badView_unreachable_from_default` (la tattica `new_backward_tatic`, con `badView` dato).

Qui si rifà la catena **senza assumere `badView`**:
1. `discovered_views_list`: `discover_views` sul modello a liste (`MSIView.msiSetup`) scopre da
   solo l'insieme `U` delle viste irraggiungibili e verifica `badView ⊆ U`;
2. `bad41`: le viste che gli 11 lemmi ponte istanziano davvero — i pattern 1–7 sulla vista
   `(i, i)` e i pattern 10–13 sulla vista `(i, j)`; è la parte di `U` che i 41 teoremi usano;
3. `unreachable41`: `bad41` è irraggiungibile, ricavato da `U` scoperto e non da `badView`;
4. gli 11 lemmi ponte ridimostrati da `unreachable41` (stessi enunciati, nome con `'`): i 41
   teoremi di `MSI.lean` passerebbero invariati con questi al posto degli originali. -/

open THEORY Relation BackwardGen MSIView

set_option maxHeartbeats 0 in
/-- **`U` scoperto per il modello a liste**: irraggiungibile da `default` con i passi interni,
e contiene tutti i 13 pattern di `badView`. -/
theorem discovered_views_list {n} :
    ∃ U : List View, (msiSetup n).UnreachableSet U ∧ ∀ v, badView v → v ∈ U := by
  discover_views (msiSetup _)
    simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
          update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
          isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
          Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
    fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
         countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
    split Cnt.ofCount_cases Cnt.ofCount
    upd update_Fin
    inv [msi_step_internal, cache_msi_step_internal, parent_msi_step]

/-! ## La parte di `U` che i 41 teoremi usano -/

/-- Le viste istanziate dagli 11 lemmi ponte: sulla vista `(i, i)` (quindi `eq = true` e
`d0 = d1`) i pattern 1–7; sulla vista `(i, j)` con `i ≠ j` i pattern 10–13. I pattern 8 e 9
(riga contro riga) non sono usati da nessuno dei 41. -/
def bad41 (v : View) : Prop :=
  (v.eq = true ∧ v.d0 = v.d1 ∧
    (v.m0 = .many                                                    -- 1
     ∨ v.s0 = .many                                                  -- 2
     ∨ (v.m0 ≠ .zero ∧ v.s0 ≠ .zero)                                 -- 3
     ∨ (v.m0 ≠ .zero ∧ v.d0 ≠ .M)                                    -- 4
     ∨ (v.s0 ≠ .zero ∧ v.d0 ≠ .S)                                    -- 5
     ∨ (v.c0 = .M ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .M))       -- 6
     ∨ (v.c0 = .S ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .S))))     -- 7
  ∨ (v.eq = false ∧
    ((v.c0 = .M ∧ v.d1 ≠ .I)                                         -- 10
     ∨ (v.c0 = .S ∧ v.d1 = .M)                                       -- 11
     ∨ (v.m0 ≠ .zero ∧ v.d1 ≠ .I)                                    -- 12
     ∨ (v.s0 ≠ .zero ∧ v.d1 = .M)))                                  -- 13

instance : DecidablePred bad41 := fun v => by unfold bad41; infer_instance
instance : DecidablePred badView := fun v => by unfold badView; infer_instance

/-- `bad41 ⊆ badView`, vista per vista. -/
theorem bad41_sub_badView : ∀ v, bad41 v → badView v := by
  intro v
  obtain ⟨c0, d0, d1, m0, s0, eq⟩ := v
  cases c0 <;> cases d0 <;> cases d1 <;> cases m0 <;> cases s0 <;> cases eq <;> decide

/-- **`bad41` è irraggiungibile**, da `U` scoperto: `bad41 ⊆ badView ⊆ U`. -/
theorem unreachable41 {n} (s : MSIState n) (h : ∃ i j, bad41 (msiView s i j)) :
    ¬ MSI.reachable s := fun hreach =>
  let ⟨_, hU, hbad⟩ := discovered_views_list (n := n)
  let ⟨i, j, hb⟩ := h
  hU s ⟨i, j, hbad _ (bad41_sub_badView _ hb)⟩ (hreach (default : MSIState n) msi_init_default)

/-! ## Gli 11 lemmi ponte, ricavati da `U` scoperto

Stessi enunciati di `MSI.lean`, nome con `'`. La vista `(i, i)` ha `eq = decide (i = i) = true`
e `d0 = d1` per riflessività; la vista `(i, j)` con `i ≠ j` ha `eq = false`. -/

theorem not_reachable_of_M' {n} {s : MSIState n} {i : Fin n} (hM : (s.caches i).state = Bstate.M)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.M)) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, by
      rcases h with h | h | h
      · exact Or.inl (cnt_ne_zero h)
      · exact Or.inr (Or.inl (cnt_ne_zero h))
      · exact Or.inr (Or.inr h)⟩)))))⟩⟩

theorem not_reachable_of_S' {n} {s : MSIState n} {i : Fin n} (hS : (s.caches i).state = Bstate.S)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.S)) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hS, by
      rcases h with h | h | h
      · exact Or.inl (cnt_ne_zero h)
      · exact Or.inr (Or.inl (cnt_ne_zero h))
      · exact Or.inr (Or.inr h)⟩)))))⟩⟩

theorem not_reachable_of_mu_row' {n} {s : MSIState n} {i : Fin n} (h : muMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.M)) : ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩)))⟩⟩

theorem not_reachable_of_sig_row' {n} {s : MSIState n} {i : Fin n} (h : sigMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.S)) : ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩))))⟩⟩

theorem not_reachable_of_two_mu' {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ muMsgs s.parent i) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inl (by show Cnt.ofCount (muMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h)⟩⟩

theorem not_reachable_of_two_sig' {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ sigMsgs s.parent i) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inl (by show Cnt.ofCount (sigMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h))⟩⟩

theorem not_reachable_of_mu_sig' {n} {s : MSIState n} {i : Fin n} (h₁ : muMsgs s.parent i ≠ 0)
    (h₂ : sigMsgs s.parent i ≠ 0) : ¬ MSI.reachable s :=
  unreachable41 s ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl,
    Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h₁, cnt_ne_zero h₂⟩))⟩⟩

theorem not_reachable_of_M_rowJ' {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hM : (s.caches i).state = Bstate.M) (hd' : ¬(s.parent.shared_state j = Bstate.I)) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, j, Or.inr ⟨decide_eq_false hne, Or.inl ⟨hM, hd'⟩⟩⟩

theorem not_reachable_of_S_rowM' {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hS : (s.caches i).state = Bstate.S) (hd' : s.parent.shared_state j = Bstate.M) :
    ¬ MSI.reachable s :=
  unreachable41 s ⟨i, j, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inl ⟨hS, hd'⟩)⟩⟩

theorem not_reachable_of_mu_rowJ' {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : muMsgs s.parent i ≠ 0) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ MSI.reachable s :=
  unreachable41 s ⟨i, j, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd'⟩))⟩⟩

theorem not_reachable_of_sig_rowM' {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : sigMsgs s.parent i ≠ 0) (hd' : s.parent.shared_state j = Bstate.M) : ¬ MSI.reachable s :=
  unreachable41 s ⟨i, j, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inr ⟨cnt_ne_zero h, hd'⟩))⟩⟩

/-! ## I numeri -/

/-- Tutte le 486 viste. -/
def allViews : List View := Id.run do
  let bs := [Bstate.M, Bstate.S, Bstate.I]
  let cs := [Cnt.zero, Cnt.one, Cnt.many]
  let mut out : List View := []
  for c0 in bs do
    for d0 in bs do
      for d1 in bs do
        for m0 in cs do
          for s0 in cs do
            for eq in [true, false] do
              out := out ++ [⟨c0, d0, d1, m0, s0, eq⟩]
  return out

/-- Le viste di `bad41`, cioè la parte di `U` usata dai 41 teoremi. -/
def views41 : List View := allViews.filter (fun v => decide (bad41 v))

#eval allViews.length                                        -- 486
#eval (allViews.filter (fun v => decide (badView v))).length -- 453
#eval views41.length                                         -- 215
#eval (views41.filter (·.eq)).length                         -- 74: pattern 1–7 sulla vista (i, i)
#eval (views41.filter (! ·.eq)).length                       -- 141: pattern 10–13 sulla vista (i, j)

#print axioms discovered_views_list
#print axioms unreachable41
#print axioms not_reachable_of_M_rowJ'
