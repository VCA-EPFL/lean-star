import Mathlib

/-! # Lemmi generici su somme finite e liste

Usati dalle prove di raffinamento di MSI (`MSI_flush_proof.lean`) e di MESI (`MESI_flush_proof.lean`):
somme su `Fin n` confrontate punto per punto, `countP` dopo `eraseIdx`, appartenenza dopo `eraseIdx`,
`eraseIdx` dell'ultimo elemento accodato. Non dipendono dal protocollo. -/

theorem sum_lt_of_pointwise {f g : Fin n → Nat} (hle : ∀ k, f k ≤ g k) (k₀ : Fin n)
    (hlt : f k₀ < g k₀) : Finset.univ.sum f < Finset.univ.sum g := by
  exact Finset.sum_lt_sum (fun k _ => hle k) ⟨k₀, Finset.mem_univ _, hlt⟩

theorem sum_eq_zero_iff_pointwise {f : Fin n → Nat} : Finset.univ.sum f = 0 ↔ ∀ k, f k = 0 := by
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h k
    exact h k (Finset.mem_univ _)
  · intro h k _
    exact h k

theorem exists_pos_of_sum_pos {f : Fin n → Nat} (h : 0 < Finset.univ.sum f) : ∃ k, 0 < f k := by
  by_contra hcon
  have hz : Finset.univ.sum f = 0 := by
    rw [sum_eq_zero_iff_pointwise]
    intro k
    exact Nat.eq_zero_of_not_pos (fun hk => hcon ⟨k, hk⟩)
  rw [hz] at h
  exact Nat.lt_irrefl 0 h

theorem countP_eraseIdx_pos {α : Type} {l : List α} {p : α → Bool} {j : Nat} {a : α}
    (hj : l[j]? = some a) (hp : p a = true) : (l.eraseIdx j).countP p + 1 = l.countP p := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp [hp]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [List.eraseIdx_cons_succ, List.countP_cons]
      have := ih hj
      split <;> omega

theorem countP_eraseIdx_neg {α : Type} {l : List α} {p : α → Bool} {j : Nat} {a : α}
    (hj : l[j]? = some a) (hp : p a = false) : (l.eraseIdx j).countP p = l.countP p := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp [hp]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [List.eraseIdx_cons_succ, List.countP_cons]
      have := ih hj
      split <;> omega

theorem mem_eraseIdx_of_ne {α : Type} {l : List α} {j : Nat} {a b : α} (ha : a ∈ l)
    (hj : l[j]? = some b) (hne : a ≠ b) : a ∈ l.eraseIdx j := by
  induction l generalizing j with
  | nil => simp at ha
  | cons c t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.eraseIdx_cons_zero]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact absurd rfl hne
      · exact ha
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [List.eraseIdx_cons_succ, List.mem_cons]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · left; rfl
      · right; exact ih ha hj

theorem eraseIdx_concat {α : Type} (l : List α) (a : α) : (l ++ [a]).eraseIdx l.length = l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp only [List.cons_append, List.length_cons, List.eraseIdx_cons_succ, ih]
