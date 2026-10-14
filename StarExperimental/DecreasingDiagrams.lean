/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import Star.Commute.ARS

/-!
# Decreasing diagrams, strict version

Confluence of a labelled rewrite system from the shape of its *local* peaks.

The steps carry a label `step l a b` with `l : Nat`. Write `⇒_k` (`big k`) for the
relation "small steps (label `< k`), then **at most one** `k`-step, then small steps".
We assume, on the states satisfying `R` (closed under steps):

* **top peaks** `b ←_k a →_k c` (two steps with the same label `k`) close with
  `b ⇒_k d ⇐_k c`;
* **mixed peaks** `b ←_l a →_k c` with `l < k` close with `b →_k^= b' →_{<k}^* d` and
  `c →_{<k}^* d`: the small side first does at most one `k`-step and then only steps
  `< k`; the big side only does steps `< k`.

Then `trans_refl rule` (the reflexive–transitive closure of all steps) is confluent on `R`:
`has_diamond_property_on R (trans_refl rule)`.

## Why this shape

The proof is by induction on `k` of `Conf k`: "the steps with label `< k` are confluent on
`R`". The induction step uses `Conf k` as a black box for everything with label `< k`
and treats the `k`-steps as a *new* relation `⇒_k`. The strict shape of the local
diagrams is exactly what lets one push a single `k`-step through a sequence of small
steps (`pushK`): each mixed peak produces again at most one `k`-step on the small side
and only small steps on the `k` side, so the `k`-step never multiplies. From `pushK` we
get that `⇒_k` has the diamond property (`bigDiamond`), hence its closure is confluent
(`bigStar_confluent`), and since the closure of `⇒_k` is the closure of the steps with
label `≤ k`, this is `Conf (k+1)`. Finally a path in `trans_refl rule` only uses finitely
many labels, so it lives in some `lt k`, and two paths live in a common `lt k`.
-/

namespace DecreasingDiagrams

open ReachingStar (trans_refl trans_refl_trans has_diamond_property_on)

variable {A : Type}

/-! ## The labelled relations -/

section Defs

variable (step : Nat → A → A → Prop)

/-- The unlabelled rewrite relation: some step with some label. -/
def rule : A → A → Prop := fun a b => ∃ l, step l a b

/-- Steps with label `< k`. -/
def lt (k : Nat) : A → A → Prop := fun a b => ∃ l, l < k ∧ step l a b

/-- Steps with label `≤ k`. -/
def le (k : Nat) : A → A → Prop := fun a b => ∃ l, l ≤ k ∧ step l a b

/-- `big k a b`, written `a ⇒_k b`: small steps (label `< k`), then at most one `k`-step,
then small steps. -/
def big (k : Nat) : A → A → Prop := fun a b =>
  ∃ a₁ a₂, trans_refl (lt step k) a a₁ ∧ (a₁ = a₂ ∨ step k a₁ a₂) ∧ trans_refl (lt step k) a₂ b

/-- `Conf R k`: the steps with label `< k` are confluent on `R`. -/
def Conf (R : A → Prop) (k : Nat) : Prop :=
  ∀ a b c, R a → trans_refl (lt step k) a b → trans_refl (lt step k) a c →
    ∃ d, trans_refl (lt step k) b d ∧ trans_refl (lt step k) c d

end Defs

/-- The hypotheses of the decreasing-diagrams theorem: `R` closed under steps, top peaks
closed by `⇒_k`, mixed peaks closed in the strict shape (see the module docstring). -/
structure Decreasing (R : A → Prop) (step : Nat → A → A → Prop) : Prop where
  hR : ∀ a b, R a → rule step a b → R b
  hTop : ∀ a b c k, R a → step k a b → step k a c → ∃ d, big step k b d ∧ big step k c d
  hMix : ∀ a b c l k, R a → l < k → step l a b → step k a c →
    ∃ b' d, (b' = b ∨ step k b b') ∧ trans_refl (lt step k) b' d ∧ trans_refl (lt step k) c d

/-! ## Generic facts about `trans_refl` -/

section TransRefl

variable {r s : A → A → Prop}

/-- A single step is a path. -/
theorem trans_refl_single {a b : A} (h : r a b) : trans_refl r a b :=
  trans_refl.step h trans_refl.refl

/-- `trans_refl` is monotone in the relation. -/
theorem trans_refl_mono (h : ∀ a b, r a b → s a b) {a b : A} (hab : trans_refl r a b) :
    trans_refl s a b := by
  induction hab with
  | refl => exact trans_refl.refl
  | step hxy _ ih => exact trans_refl.step (h _ _ hxy) ih

/-- A predicate closed under `r` is closed under `trans_refl r`. -/
theorem R_of_trans_refl {R : A → Prop} (hR : ∀ a b, R a → r a b → R b) {a b : A}
    (hab : trans_refl r a b) (ha : R a) : R b := by
  induction hab with
  | refl => exact ha
  | step hxy _ ih => exact ih (hR _ _ ha hxy)

end TransRefl

/-! ## Facts about the labelled relations -/

section Labels

variable {step : Nat → A → A → Prop}

/-- `lt k ⊆ lt k'` for `k ≤ k'`. -/
theorem lt_weaken {k k' : Nat} (hk : k ≤ k') {a b : A} (h : lt step k a b) : lt step k' a b := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨l, lt_of_lt_of_le hl hk, hs⟩

theorem rule_of_lt {k : Nat} {a b : A} (h : lt step k a b) : rule step a b := by
  obtain ⟨l, _, hs⟩ := h
  exact ⟨l, hs⟩

theorem le_of_lt_k {k : Nat} {a b : A} (h : lt step k a b) : le step k a b := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨l, Nat.le_of_lt hl, hs⟩

/-- `lt (k+1) = le k`, pointwise. -/
theorem lt_succ_iff_le_k {k : Nat} {a b : A} : lt step (k+1) a b ↔ le step k a b := by
  simp only [DecreasingDiagrams.lt, DecreasingDiagrams.le, Nat.lt_succ_iff]

/-- `lt 0` is empty, so its closure is the identity. -/
theorem eq_of_trans_refl_lt_zero {a b : A} (h : trans_refl (lt step 0) a b) : a = b := by
  induction h with
  | refl => rfl
  | step hxy _ _ =>
    obtain ⟨l, hl, _⟩ := hxy
    exact (Nat.not_lt_zero l hl).elim

/-- `⇒_k` is reflexive. -/
theorem big_refl {k : Nat} (a : A) : big step k a a :=
  ⟨a, a, trans_refl.refl, Or.inl rfl, trans_refl.refl⟩

/-- A single `k`-step is a `⇒_k` step. -/
theorem big_of_step {k : Nat} {a b : A} (h : step k a b) : big step k a b :=
  ⟨a, b, trans_refl.refl, Or.inr h, trans_refl.refl⟩

/-- A single small step is a `⇒_k` step. -/
theorem big_of_lt {k : Nat} {a b : A} (h : lt step k a b) : big step k a b :=
  ⟨b, b, trans_refl_single h, Or.inl rfl, trans_refl.refl⟩

/-- Small steps before and after a `⇒_k` step give a `⇒_k` step. -/
theorem big_of_L_big_L {k : Nat} {a b c d : A} (hab : trans_refl (lt step k) a b)
    (hbc : big step k b c) (hcd : trans_refl (lt step k) c d) : big step k a d := by
  obtain ⟨p, q, hbp, hpq, hqc⟩ := hbc
  exact ⟨p, q, trans_refl_trans hab hbp, hpq, trans_refl_trans hqc hcd⟩

/-- A step with label `≤ k` is a `⇒_k` step. -/
theorem big_of_le {k : Nat} {a b : A} (h : le step k a b) : big step k a b := by
  obtain ⟨l, hl, hs⟩ := h
  rcases Nat.lt_or_eq_of_le hl with hlt | heq
  · exact big_of_lt ⟨l, hlt, hs⟩
  · subst heq
    exact big_of_step hs

/-- A `⇒_k` step is a path of steps with label `≤ k`. -/
theorem leStar_of_big {k : Nat} {a b : A} (h : big step k a b) : trans_refl (le step k) a b := by
  obtain ⟨p, q, hap, hpq, hqb⟩ := h
  have h₁ : trans_refl (le step k) a p := trans_refl_mono (fun _ _ => le_of_lt_k) hap
  have h₃ : trans_refl (le step k) q b := trans_refl_mono (fun _ _ => le_of_lt_k) hqb
  have h₂ : trans_refl (le step k) p q := by
    rcases hpq with rfl | hs
    · exact trans_refl.refl
    · exact trans_refl_single ⟨k, Nat.le_refl k, hs⟩
  exact trans_refl_trans h₁ (trans_refl_trans h₂ h₃)

/-- `(≤ k)^* ⊆ (⇒_k)^*`. -/
theorem le_sub_bigStar {k : Nat} {a b : A} (h : trans_refl (le step k) a b) :
    trans_refl (big step k) a b :=
  trans_refl_mono (fun _ _ => big_of_le) h

/-- `(⇒_k)^* ⊆ (≤ k)^*`. -/
theorem bigStar_sub_le {k : Nat} {a b : A} (h : trans_refl (big step k) a b) :
    trans_refl (le step k) a b := by
  induction h with
  | refl => exact trans_refl.refl
  | step hxy _ ih => exact trans_refl_trans (leStar_of_big hxy) ih

/-- A path of `rule` uses finitely many labels: it is a path of `lt k` for some `k`. -/
theorem exists_lt_of_rule {a b : A} (h : trans_refl (rule step) a b) :
    ∃ k, trans_refl (lt step k) a b := by
  induction h with
  | refl => exact ⟨0, trans_refl.refl⟩
  | step hxy _ ih =>
    obtain ⟨l, hs⟩ := hxy
    obtain ⟨k, hk⟩ := ih
    refine ⟨max (l+1) k, trans_refl.step ⟨l, ?_, hs⟩
      (trans_refl_mono (fun _ _ => lt_weaken (le_max_right _ _)) hk)⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self l) (le_max_left _ _)

end Labels

/-! ## Closure of `R` -/

section Closure

variable {R : A → Prop} {step : Nat → A → A → Prop} (D : Decreasing R step)
include D

theorem R_of_step {k : Nat} {a b : A} (ha : R a) (h : step k a b) : R b :=
  D.hR a b ha ⟨k, h⟩

theorem R_of_optStep {k : Nat} {a b : A} (ha : R a) (h : a = b ∨ step k a b) : R b := by
  rcases h with rfl | hs
  · exact ha
  · exact R_of_step D ha hs

theorem R_of_ltStar {k : Nat} {a b : A} (ha : R a) (h : trans_refl (lt step k) a b) : R b :=
  R_of_trans_refl (fun a b ha h => D.hR a b ha (rule_of_lt h)) h ha

theorem R_of_big {k : Nat} {a b : A} (ha : R a) (h : big step k a b) : R b := by
  obtain ⟨p, q, hap, hpq, hqb⟩ := h
  exact R_of_ltStar D (R_of_optStep D (R_of_ltStar D ha hap) hpq) hqb

end Closure

/-! ## The induction step: from `Conf k` to `Conf (k+1)` -/

section Step

variable {R : A → Prop} {step : Nat → A → A → Prop} (D : Decreasing R step)
  {k : Nat} (hC : Conf step R k)
include D hC

/-- Push one `k`-step through a sequence of small steps: `y ←_k x →_{<k}^* z` closes with
`z →_k^= q →_{<k}^* w` and `y →_{<k}^* w`. -/
theorem pushK {x y z : A} (hx : R x) (hxy : step k x y) (hxz : trans_refl (lt step k) x z) :
    ∃ q w, (q = z ∨ step k z q) ∧ trans_refl (lt step k) q w ∧ trans_refl (lt step k) y w := by
  induction hxz generalizing y with
  | refl => exact ⟨y, y, Or.inr hxy, trans_refl.refl, trans_refl.refl⟩
  | @step x x₁ z hxx₁ hx₁z ih =>
    obtain ⟨l, hl, hs⟩ := hxx₁
    have hx₁ : R x₁ := R_of_step D hx hs
    -- mixed peak at `x`: `x₁ →_k^= q₁ →_{<k}^* d₁` and `y →_{<k}^* d₁`
    obtain ⟨q₁, d₁, hq₁, hq₁d₁, hyd₁⟩ := D.hMix x x₁ y l k hx hl hs hxy
    rcases hq₁ with rfl | hK
    · -- no `k`-step on the small side: close `d₁` and `z` with `Conf k`
      obtain ⟨w, hd₁w, hzw⟩ := hC _ _ _ hx₁ hq₁d₁ hx₁z
      exact ⟨z, w, Or.inl rfl, hzw, trans_refl_trans hyd₁ hd₁w⟩
    · -- a `k`-step `x₁ →_k q₁`: push it through `x₁ →_{<k}^* z` by induction
      obtain ⟨q, w', hq, hqw', hq₁w'⟩ := ih hx₁ hK
      have hq₁R : R q₁ := R_of_step D hx₁ hK
      obtain ⟨w, hd₁w, hw'w⟩ := hC _ _ _ hq₁R hq₁d₁ hq₁w'
      exact ⟨q, w, hq, trans_refl_trans hqw' hw'w, trans_refl_trans hyd₁ hd₁w⟩

/-- Push a `⇒_k` step through small steps: `y ⇐_k x →_{<k}^* z` closes with `y →_{<k}^* w`
and `z ⇒_k w`. -/
theorem pushBig {x y z : A} (hx : R x) (hxy : big step k x y)
    (hxz : trans_refl (lt step k) x z) :
    ∃ w, trans_refl (lt step k) y w ∧ big step k z w := by
  obtain ⟨p, q, hxp, hpq, hqy⟩ := hxy
  obtain ⟨e, hpe, hze⟩ := hC _ _ _ hx hxp hxz
  have hp : R p := R_of_ltStar D hx hxp
  rcases hpq with rfl | hK
  · -- no `k`-step: everything is small, use `Conf k` once more
    obtain ⟨w, hew, hyw⟩ := hC _ _ _ hp hpe hqy
    exact ⟨w, hyw, w, w, trans_refl_trans hze hew, Or.inl rfl, trans_refl.refl⟩
  · -- push `p →_k q` through `p →_{<k}^* e`
    obtain ⟨r, w₁, hr, hrw₁, hqw₁⟩ := pushK D hC hp hK hpe
    have hq : R q := R_of_step D hp hK
    obtain ⟨f, hyf, hw₁f⟩ := hC _ _ _ hq hqy hqw₁
    refine ⟨f, hyf, e, r, hze, ?_, trans_refl_trans hrw₁ hw₁f⟩
    rcases hr with hr | hr
    · exact Or.inl hr.symm
    · exact Or.inr hr

omit hC in
/-- `hTop` for optional `k`-steps. -/
theorem top_of_optStep {e r r' : A} (he : R e) (hr : r = e ∨ step k e r)
    (hr' : r' = e ∨ step k e r') : ∃ d, big step k r d ∧ big step k r' d := by
  rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
  · exact ⟨_, big_refl _, big_refl _⟩
  · exact ⟨_, big_of_step hr', big_refl _⟩
  · exact ⟨_, big_refl _, big_of_step hr⟩
  · exact D.hTop e r r' k he hr hr'

/-- `⇒_k` has the diamond property on `R`. -/
theorem bigDiamond {x y y' : A} (hx : R x) (hxy : big step k x y) (hxy' : big step k x y') :
    ∃ w, big step k y w ∧ big step k y' w := by
  obtain ⟨p, q, hxp, hpq, hqy⟩ := hxy
  obtain ⟨p', q', hxp', hpq', hqy'⟩ := hxy'
  -- close the two small prefixes
  obtain ⟨e, hpe, hp'e⟩ := hC _ _ _ hx hxp hxp'
  have hp : R p := R_of_ltStar D hx hxp
  have hp' : R p' := R_of_ltStar D hx hxp'
  have he : R e := R_of_ltStar D hp hpe
  have hq : R q := R_of_optStep D hp hpq
  have hq' : R q' := R_of_optStep D hp' hpq'
  -- push the two optional `k`-steps to `e`
  have h₁ : ∃ r w₁, (r = e ∨ step k e r) ∧ trans_refl (lt step k) r w₁ ∧
      trans_refl (lt step k) q w₁ := by
    rcases hpq with rfl | hK
    · exact ⟨e, e, Or.inl rfl, trans_refl.refl, hpe⟩
    · exact pushK D hC hp hK hpe
  have h₂ : ∃ r' w₂, (r' = e ∨ step k e r') ∧ trans_refl (lt step k) r' w₂ ∧
      trans_refl (lt step k) q' w₂ := by
    rcases hpq' with rfl | hK
    · exact ⟨e, e, Or.inl rfl, trans_refl.refl, hp'e⟩
    · exact pushK D hC hp' hK hp'e
  obtain ⟨r, w₁, hr, hrw₁, hqw₁⟩ := h₁
  obtain ⟨r', w₂, hr', hr'w₂, hq'w₂⟩ := h₂
  have hrR : R r := R_of_optStep D he (hr.imp Eq.symm id)
  have hr'R : R r' := R_of_optStep D he (hr'.imp Eq.symm id)
  -- top peak at `e`
  obtain ⟨d, hrd, hr'd⟩ := top_of_optStep D he hr hr'
  have hd : R d := R_of_big D hrR hrd
  -- close the small suffixes and push the `⇒_k` steps `r ⇒ d`, `r' ⇒ d` through them
  obtain ⟨f₁, hyf₁, hw₁f₁⟩ := hC _ _ _ hq hqy hqw₁
  obtain ⟨f₂, hy'f₂, hw₂f₂⟩ := hC _ _ _ hq' hqy' hq'w₂
  obtain ⟨w₃, hdw₃, hf₁w₃⟩ := pushBig D hC hrR hrd (trans_refl_trans hrw₁ hw₁f₁)
  obtain ⟨w₄, hdw₄, hf₂w₄⟩ := pushBig D hC hr'R hr'd (trans_refl_trans hr'w₂ hw₂f₂)
  obtain ⟨g, hw₃g, hw₄g⟩ := hC _ _ _ hd hdw₃ hdw₄
  exact ⟨g, big_of_L_big_L hyf₁ hf₁w₃ hw₃g, big_of_L_big_L hy'f₂ hf₂w₄ hw₄g⟩

/-- Strip lemma for `⇒_k`. -/
theorem bigStrip {x y z : A} (hx : R x) (hxy : big step k x y)
    (hxz : trans_refl (big step k) x z) :
    ∃ w, trans_refl (big step k) y w ∧ big step k z w := by
  induction hxz generalizing y with
  | refl => exact ⟨y, trans_refl.refl, hxy⟩
  | @step x x₁ z hxx₁ _ ih =>
    obtain ⟨w₁, hyw₁, hx₁w₁⟩ := bigDiamond D hC hx hxy hxx₁
    obtain ⟨w, hw₁w, hzw⟩ := ih (R_of_big D hx hxx₁) hx₁w₁
    exact ⟨w, trans_refl.step hyw₁ hw₁w, hzw⟩

/-- `(⇒_k)^*` is confluent on `R`. -/
theorem bigStar_confluent {x y z : A} (hx : R x) (hxy : trans_refl (big step k) x y)
    (hxz : trans_refl (big step k) x z) :
    ∃ w, trans_refl (big step k) y w ∧ trans_refl (big step k) z w := by
  induction hxy generalizing z with
  | refl => exact ⟨z, hxz, trans_refl.refl⟩
  | @step x x₁ y hxx₁ _ ih =>
    obtain ⟨w₁, hx₁w₁, hzw₁⟩ := bigStrip D hC hx hxx₁ hxz
    obtain ⟨w, hyw, hw₁w⟩ := ih (R_of_big D hx hxx₁) hx₁w₁
    exact ⟨w, hyw, trans_refl.step hzw₁ hw₁w⟩

/-- `Conf k → Conf (k+1)`. -/
theorem conf_succ : Conf step R (k+1) := by
  intro a b c ha hab hac
  have hab' : trans_refl (big step k) a b :=
    le_sub_bigStar (trans_refl_mono (fun _ _ => lt_succ_iff_le_k.mp) hab)
  have hac' : trans_refl (big step k) a c :=
    le_sub_bigStar (trans_refl_mono (fun _ _ => lt_succ_iff_le_k.mp) hac)
  obtain ⟨d, hbd, hcd⟩ := bigStar_confluent D hC ha hab' hac'
  exact ⟨d, trans_refl_mono (fun _ _ => lt_succ_iff_le_k.mpr) (bigStar_sub_le hbd),
    trans_refl_mono (fun _ _ => lt_succ_iff_le_k.mpr) (bigStar_sub_le hcd)⟩

end Step

/-! ## Main theorem -/

section Main

variable {R : A → Prop} {step : Nat → A → A → Prop}

/-- Confluence of the steps with label `< k`, for every `k`. -/
theorem conf (D : Decreasing R step) : ∀ k, Conf step R k := by
  intro k
  induction k with
  | zero =>
    intro a b c _ hab hac
    obtain rfl := eq_of_trans_refl_lt_zero hab
    obtain rfl := eq_of_trans_refl_lt_zero hac
    exact ⟨_, trans_refl.refl, trans_refl.refl⟩
  | succ k ih => exact conf_succ D ih

/-- **Decreasing diagrams.** Under `Decreasing R step`, the closure of all steps is
confluent on `R`. -/
theorem has_diamond_property_on_of_decreasing (D : Decreasing R step) :
    has_diamond_property_on R (trans_refl (rule step)) := by
  intro a b c ha hac hab
  obtain ⟨k₁, h₁⟩ := exists_lt_of_rule hac
  obtain ⟨k₂, h₂⟩ := exists_lt_of_rule hab
  have h₁' := trans_refl_mono (fun _ _ => lt_weaken (le_max_left k₁ k₂)) h₁
  have h₂' := trans_refl_mono (fun _ _ => lt_weaken (le_max_right k₁ k₂)) h₂
  obtain ⟨d, hcd, hbd⟩ := conf D (max k₁ k₂) a c b ha h₁' h₂'
  exact ⟨d, trans_refl_mono (fun _ _ => rule_of_lt) hcd,
    trans_refl_mono (fun _ _ => rule_of_lt) hbd⟩

end Main

end DecreasingDiagrams
