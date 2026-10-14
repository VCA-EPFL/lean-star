import StarExperimental.DecreasingDiagrams
import StarExperimental.MSI_trial_lift

/-!
# `MSI_trial`: la forma decrescente di un diamante locale

`DecJoin α β b c` è ciò che `DecreasingDiagrams` chiede a un picco `a →α b`, `a →β c`
(etichette `lab` di `MSI_trial_def`):

* `α = β`: `b` e `c` arrivano a un `d` comune con un *passo grande* ciascuno (`big`: passi `< α`,
  al più un passo `= α`, passi `< α`);
* `α < β`: `b` fa al più un passo `= β` **subito**, poi solo passi `< β`; `c` solo passi `< β`;
* `β < α`: simmetrico.

I costruttori (`square`, `of_eq`, `absorb`, ...) coprono le forme ricorrenti; per i cammini lunghi si
usano `ltStar_cons`/`ltStar_single` e `big_mk` direttamente. `DecJoin.symm` permette di dimostrare
ogni coppia di regole una volta sola.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)
open DecreasingDiagrams (lt big)

namespace MSITrial

variable {n : Nat}

/-- Passi con etichetta `< k`. -/
abbrev Lt (k : Nat) : MSIState n → MSIState n → Prop := lt (lstep (n := n)) k
/-- Un passo grande di livello `k`. -/
abbrev Big (k : Nat) : MSIState n → MSIState n → Prop := big (lstep (n := n)) k

def DecJoin (α β : Nat) (b c : MSIState n) : Prop :=
  (α = β ∧ ∃ d, Big α b d ∧ Big α c d) ∨
  (α < β ∧ ∃ b' d, (b' = b ∨ lstep β b b') ∧ trans_refl (Lt β) b' d ∧ trans_refl (Lt β) c d) ∨
  (β < α ∧ ∃ c' d, (c' = c ∨ lstep α c c') ∧ trans_refl (Lt α) c' d ∧ trans_refl (Lt α) b d)

/-! ## Mattoni -/

theorem lstep_of {a b : MSIState n} {e : IEvent n} (h : step_int a e b) : lstep (lab e) a b :=
  ⟨e, rfl, h⟩

theorem lstep_of' {a b : MSIState n} {e : IEvent n} {k : Nat} (h : step_int a e b) (hl : lab e = k) :
    lstep k a b := ⟨e, hl, h⟩

theorem lt_of {a b : MSIState n} {e : IEvent n} {k : Nat} (h : step_int a e b) (hl : lab e < k) :
    Lt k a b := ⟨lab e, hl, e, rfl, h⟩

theorem ltStar_single {a b : MSIState n} {e : IEvent n} {k : Nat} (h : step_int a e b)
    (hl : lab e < k) : trans_refl (Lt k) a b :=
  trans_refl.step (lt_of h hl) trans_refl.refl

theorem ltStar_cons {a b c : MSIState n} {e : IEvent n} {k : Nat} (h : step_int a e b)
    (hl : lab e < k) (rest : trans_refl (Lt k) b c) : trans_refl (Lt k) a c :=
  trans_refl.step (lt_of h hl) rest

theorem ltStar_trans {a b c : MSIState n} {k : Nat} (h₁ : trans_refl (Lt k) a b)
    (h₂ : trans_refl (Lt k) b c) : trans_refl (Lt k) a c := by
  induction h₁ with
  | refl => exact h₂
  | step hab _ ih => exact trans_refl.step hab (ih h₂)

/-- Un passo grande dai suoi tre pezzi. -/
theorem big_mk {a a₁ a₂ b : MSIState n} {k : Nat} (p₁ : trans_refl (Lt k) a a₁)
    (h : a₁ = a₂ ∨ lstep k a₁ a₂) (p₂ : trans_refl (Lt k) a₂ b) : Big k a b :=
  ⟨a₁, a₂, p₁, h, p₂⟩

theorem big_refl (a : MSIState n) (k : Nat) : Big k a a :=
  big_mk trans_refl.refl (Or.inl rfl) trans_refl.refl

theorem big_of_ltStar {a b : MSIState n} {k : Nat} (p : trans_refl (Lt k) a b) : Big k a b :=
  big_mk p (Or.inl rfl) trans_refl.refl

theorem big_of_step {a b : MSIState n} {e : IEvent n} {k : Nat} (h : step_int a e b)
    (hl : lab e = k) : Big k a b :=
  big_mk trans_refl.refl (Or.inr (lstep_of' h hl)) trans_refl.refl

/-! ## Costruttori di `DecJoin` -/

theorem DecJoin.symm {α β : Nat} {b c : MSIState n} (h : DecJoin α β b c) : DecJoin β α c b := by
  unfold DecJoin at *
  rcases h with ⟨he, d, hb, hc⟩ | ⟨hlt, b', d, hb', hbd, hcd⟩ | ⟨hlt, c', d, hc', hcd, hbd⟩
  · exact Or.inl ⟨he.symm, d, he ▸ hc, he ▸ hb⟩
  · exact Or.inr (Or.inr ⟨hlt, b', d, hb', hbd, hcd⟩)
  · exact Or.inr (Or.inl ⟨hlt, c', d, hc', hcd, hbd⟩)

/-- `b = c`: niente da fare. -/
theorem DecJoin.of_eq {α β : Nat} {b c : MSIState n} (h : b = c) : DecJoin α β b c := by
  subst h
  unfold DecJoin
  rcases Nat.lt_trichotomy α β with hlt | heq | hgt
  · exact Or.inr (Or.inl ⟨hlt, b, b, Or.inl rfl, trans_refl.refl, trans_refl.refl⟩)
  · exact Or.inl ⟨heq, b, big_refl _ _, big_refl _ _⟩
  · exact Or.inr (Or.inr ⟨hgt, b, b, Or.inl rfl, trans_refl.refl, trans_refl.refl⟩)

/-- Il quadrato: da `b` il passo che portava in `c`, da `c` il passo che portava in `b`. -/
theorem DecJoin.square {α β : Nat} {b c d : MSIState n} {e₁ e₂ : IEvent n}
    (hb : step_int b e₂ d) (hc : step_int c e₁ d) (l₁ : lab e₁ = α) (l₂ : lab e₂ = β) :
    DecJoin α β b c := by
  unfold DecJoin
  rcases Nat.lt_trichotomy α β with hlt | heq | hgt
  · exact Or.inr (Or.inl ⟨hlt, d, d, Or.inr (lstep_of' hb l₂), trans_refl.refl,
      ltStar_single hc (l₁ ▸ hlt)⟩)
  · subst heq
    exact Or.inl ⟨rfl, d, big_of_step hb l₂, big_of_step hc l₁⟩
  · exact Or.inr (Or.inr ⟨hgt, d, d, Or.inr (lstep_of' hc l₁), trans_refl.refl,
      ltStar_single hb (l₂ ▸ hgt)⟩)

/-- `c` raggiunge `b` con un cammino di passi tutti `< max α β` (per esempio: lo scarto di un
messaggio stantio). -/
theorem DecJoin.absorb {α β : Nat} {b c : MSIState n} (p : trans_refl (Lt (max α β)) c b) :
    DecJoin α β b c := by
  unfold DecJoin
  rcases Nat.lt_trichotomy α β with hlt | heq | hgt
  · have : max α β = β := Nat.max_eq_right (Nat.le_of_lt hlt)
    exact Or.inr (Or.inl ⟨hlt, b, b, Or.inl rfl, trans_refl.refl, this ▸ p⟩)
  · subst heq
    simp only [Nat.max_self] at p
    exact Or.inl ⟨rfl, b, big_refl _ _, big_of_ltStar p⟩
  · have : max α β = α := Nat.max_eq_left (Nat.le_of_lt hgt)
    exact Or.inr (Or.inr ⟨hgt, c, b, Or.inl rfl, this ▸ p, trans_refl.refl⟩)

/-- Caso `α = β`: due passi grandi. -/
theorem DecJoin.top {α : Nat} {b c d : MSIState n} (hb : Big α b d) (hc : Big α c d) :
    DecJoin α α b c :=
  Or.inl ⟨rfl, d, hb, hc⟩

/-- Caso `α < β`: `b` fa al più il passo `β` subito, poi passi `< β`; `c` solo passi `< β`. -/
theorem DecJoin.mix {α β : Nat} {b b' c d : MSIState n} (hlt : α < β)
    (hb : b' = b ∨ lstep β b b') (hbd : trans_refl (Lt β) b' d) (hcd : trans_refl (Lt β) c d) :
    DecJoin α β b c :=
  Or.inr (Or.inl ⟨hlt, b', d, hb, hbd, hcd⟩)

/-- Caso `β < α`: simmetrico di `mix`. -/
theorem DecJoin.mix' {α β : Nat} {b c c' d : MSIState n} (hlt : β < α)
    (hc : c' = c ∨ lstep α c c') (hcd : trans_refl (Lt α) c' d) (hbd : trans_refl (Lt α) b d) :
    DecJoin α β b c :=
  Or.inr (Or.inr ⟨hlt, c', d, hc, hcd, hbd⟩)

/-! ## Uscite -/

theorem not_reach_of_not_synced {s : MSIState n} (h : ¬ synced s) : ¬ Reach s :=
  fun hr => h (synced_of_reach hr)

/-- `Reach` è chiuso per passi interni. -/
theorem reach_step {a b : MSIState n} (ha : Reach a) (h : rule n a b) : Reach b := by
  obtain ⟨l, hl⟩ := ha
  exact ⟨l, ReachingStar.star_extend.step_int _ _ _ _ hl (trans_refl.step h trans_refl.refl)⟩

end MSITrial
