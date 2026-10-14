import StarExperimental.MSI_trial_views

/-!
# `MSI_trial`: lemmi ponte verso `¬ Reach s`

Gli stessi lemmi ponte di `MSI.lean` (`not_reachable_of_*`), con la conclusione `¬ Reach s` di
`MSI_trial` (raggiungibilità di ARS, passi interni ed esterni) al posto di `¬ MSI.reachable s`
(soli passi interni). Le dimostrazioni sono identiche: ogni lemma esibisce una vista cattiva e
applica `badView_unreachable`. I lemmi di conteggio (`cnt_ne_zero`, `muMsgs_ne_zero_of_*`,
`two_le_countP_of_ne`) sono quelli di `MSI.lean`.
-/

open THEORY Relation BackwardGen MSIView

namespace MSITrial

variable {n : Nat}

theorem not_reach_of_not_synced {s : MSIState n} (h : ¬ synced s) : ¬ Reach s :=
  fun hr => h (synced_of_reach hr)

/-- Vista cattiva 1: due messaggi con token `M` per `i`. -/
theorem not_reach_of_two_mu {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ muMsgs s.parent i) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inl (by show Cnt.ofCount (muMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h)⟩

/-- Vista cattiva 1: due messaggi con token `S` per `i`. -/
theorem not_reach_of_two_sig {n} {s : MSIState n} {i : Fin n} (h : 2 ≤ sigMsgs s.parent i) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inl (by show Cnt.ofCount (sigMsgs s.parent i) = .many; rw [Cnt.ofCount_eq_many]; exact h))⟩

/-- Vista cattiva 1: un token `M` e un token `S` in volo per `i`. -/
theorem not_reach_of_mu_sig {n} {s : MSIState n} {i : Fin n} (h₁ : muMsgs s.parent i ≠ 0) (h₂ : sigMsgs s.parent i ≠ 0) :
    ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h₁,
                                          cnt_ne_zero h₂⟩))⟩

/-- Vista cattiva 2: un token `M` per `i` con la riga `i` non a `M`. -/
theorem not_reach_of_mu_row {n} {s : MSIState n} {i : Fin n} (h : muMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.M)) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩)))⟩

/-- Vista cattiva 2: un token `S` per `i` con la riga `i` non a `S`. -/
theorem not_reach_of_sig_row {n} {s : MSIState n} {i : Fin n} (h : sigMsgs s.parent i ≠ 0)
    (hd : ¬(s.parent.shared_state i = Bstate.S)) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hd⟩))))⟩

/-- Vista cattiva 3: la cache `i` in `M` con un token `M` in volo, un token `S` in volo, o la riga non a `M`. -/
theorem not_reach_of_M {n} {s : MSIState n} {i : Fin n} (hM : (s.caches i).state = Bstate.M)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.M)) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, by
    rcases h with h | h | h
    · exact Or.inl (cnt_ne_zero h)
    · exact Or.inr (Or.inl (cnt_ne_zero h))
    · exact Or.inr (Or.inr h)⟩)))))⟩

/-- Vista cattiva 3: la cache `i` in `S` con un token `M` in volo, un token `S` in volo, o la riga non a `S`. -/
theorem not_reach_of_S {n} {s : MSIState n} {i : Fin n} (hS : (s.caches i).state = Bstate.S)
    (h : muMsgs s.parent i ≠ 0 ∨ sigMsgs s.parent i ≠ 0 ∨ ¬(s.parent.shared_state i = Bstate.S)) : ¬ Reach s :=
  badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, by
    rcases h with h | h | h
    · exact Or.inl (cnt_ne_zero h)
    · exact Or.inr (Or.inl (cnt_ne_zero h))
    · exact Or.inr (Or.inr h)⟩))))))⟩

/-- Vista cattiva 4: la riga `i = M` e la riga di `j ≠ i` non a `I`. -/
theorem not_reach_of_rowM_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hd : s.parent.shared_state i = Bstate.M) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hd, hd'⟩)))))))⟩

/-- Vista cattiva 4: la riga `i = S` e la riga di `j ≠ i` a `M`. -/
theorem not_reach_of_rowS_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hd : s.parent.shared_state i = Bstate.S) (hd' : s.parent.shared_state j = Bstate.M) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hd, hd'⟩))))))))⟩

/-- Vista cattiva 5: la cache `i` in `M` e la riga di `j ≠ i` non a `I`. -/
theorem not_reach_of_M_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hM : (s.caches i).state = Bstate.M) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hM, hd'⟩)))))))))⟩

/-- Vista cattiva 5: la cache `i` in `S` e la riga di `j ≠ i` a `M`. -/
theorem not_reach_of_S_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (hS : (s.caches i).state = Bstate.S) (hd' : s.parent.shared_state j = Bstate.M) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨decide_eq_false hne, hS, hd'⟩))))))))))⟩

/-- Vista cattiva 5: un token `M` per `i` e la riga di `j ≠ i` non a `I`. -/
theorem not_reach_of_mu_rowJ {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : muMsgs s.parent i ≠ 0) (hd' : ¬(s.parent.shared_state j = Bstate.I)) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨decide_eq_false hne, cnt_ne_zero h, hd'⟩)))))))))))⟩

/-- Vista cattiva 5: un token `S` per `i` e la riga di `j ≠ i` a `M`. -/
theorem not_reach_of_sig_rowM {n} {s : MSIState n} {i j : Fin n} (hne : i ≠ j)
    (h : sigMsgs s.parent i ≠ 0) (hd' : s.parent.shared_state j = Bstate.M) : ¬ Reach s :=
  badView_unreachable s ⟨i, j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨decide_eq_false hne, cnt_ne_zero h, hd'⟩)))))))))))⟩

end MSITrial
