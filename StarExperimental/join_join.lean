/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import Star.Commute.ARS

/-!
# The join–join rewrite, from scratch

A self-contained model of the rewrite

    lhs                                     rhs
    i_0 ─▶ join1 ─▶ join2 ─▶ o_out          i_1 ─▶ join1 ─▶ join2 ─▶ pure ─▶ o_out
    i_1 ─▶ join1      ▲                     i_2 ─▶ join1      ▲
    i_2 ──────────────┘                     i_0 ──────────────┘

A `join` waits for one value on each of its two inputs and outputs the pair.
`lhs` pairs `i_0` with `i_1` first and outputs `((a, b), c)`; `rhs` pairs `i_1`
with `i_2` first, obtains `(a, (b, c))`, and `pure` re-associates it to `((a, b), c)`.

The specification of the rewrite is `lhs` itself: `rhs_refines_lhs` says that
everything the new circuit can do, the old circuit could already do. It is proved with
`enough_star_upto` (`Star.Commute.ARS`), from the relation `φ₀` and two diamonds.
-/

set_option autoImplicit true  -- unbound names in the rules below are implicit arguments

namespace JoinJoin

/-- A `join`: one FIFO (a list) per input port. -/
abbrev Join (α β : Type) := List α × List β

/-- What can be observed: a value entering on `i_0`, `i_1`, `i_2`, or leaving on `o_out`. -/
inductive Event (T₁ T₂ T₃ : Type) where
  | in0 (a : T₁)
  | in1 (b : T₂)
  | in2 (c : T₃)
  | out (v : (T₁ × T₂) × T₃)

/-- A circuit: a state, an initial state and a step relation.
`Step s (some e) s'` is an observable step, `Step s none s'` an internal one. -/
structure System (E : Type) where
  State : Type
  init : State
  Step : State → Option E → State → Prop

/-! ## `lhs`: `join1 : join T₁ T₂`, then `join2 : join (T₁ × T₂) T₃` -/

abbrev LhsState (T₁ T₂ T₃ : Type) := Join T₁ T₂ × Join (T₁ × T₂) T₃

inductive LhsStep : LhsState T₁ T₂ T₃ → Option (Event T₁ T₂ T₃) → LhsState T₁ T₂ T₃ → Prop where
  /-- `i_0 → join1.in1` -/
  | in0 (a : T₁) : LhsStep ((l, r), j2) (some (.in0 a)) ((l ++ [a], r), j2)
  /-- `i_1 → join1.in2` -/
  | in1 (b : T₂) : LhsStep ((l, r), j2) (some (.in1 b)) ((l, r ++ [b]), j2)
  /-- `i_2 → join2.in2` -/
  | in2 (c : T₃) : LhsStep (j1, (l, r)) (some (.in2 c)) (j1, (l, r ++ [c]))
  /-- `join1.out1 → join2.in1`: `join1` fires; nothing is observed. -/
  | link (a : T₁) (b : T₂) :
      LhsStep ((a :: l, b :: r), (l', r')) none ((l, r), (l' ++ [(a, b)], r'))
  /-- `join2.out1 → o_out`: `join2` fires. -/
  | out (a : T₁) (b : T₂) (c : T₃) :
      LhsStep (j1, ((a, b) :: l, c :: r)) (some (.out ((a, b), c))) (j1, (l, r))

def lhs (T₁ T₂ T₃ : Type) : System (Event T₁ T₂ T₃) :=
  ⟨LhsState T₁ T₂ T₃, (([], []), ([], [])), LhsStep⟩

/-! ## `rhs`: `join1 : join T₂ T₃`, then `join2 : join T₁ (T₂ × T₃)`, then `pure` -/

/-- The function computed by `pure`. -/
def reassoc (x : T₁ × (T₂ × T₃)) : (T₁ × T₂) × T₃ := ((x.1, x.2.1), x.2.2)

/-- The last component is the FIFO of `pure`, holding the re-associated values. -/
abbrev RhsState (T₁ T₂ T₃ : Type) := Join T₂ T₃ × Join T₁ (T₂ × T₃) × List ((T₁ × T₂) × T₃)

inductive RhsStep : RhsState T₁ T₂ T₃ → Option (Event T₁ T₂ T₃) → RhsState T₁ T₂ T₃ → Prop where
  /-- `i_0 → join2.in1` -/
  | in0 (a : T₁) : RhsStep (j1, (l, r), p) (some (.in0 a)) (j1, (l ++ [a], r), p)
  /-- `i_1 → join1.in1` -/
  | in1 (b : T₂) : RhsStep ((l, r), j2, p) (some (.in1 b)) ((l ++ [b], r), j2, p)
  /-- `i_2 → join1.in2` -/
  | in2 (c : T₃) : RhsStep ((l, r), j2, p) (some (.in2 c)) ((l, r ++ [c]), j2, p)
  /-- `join1.out1 → join2.in2`: `join1` fires. -/
  | link1 (b : T₂) (c : T₃) :
      RhsStep ((b :: l, c :: r), (l', r'), p) none ((l, r), (l', r' ++ [(b, c)]), p)
  /-- `join2.out1 → pure.in1`: `join2` fires. -/
  | link2 (a : T₁) (bc : T₂ × T₃) :
      RhsStep (j1, (a :: l, bc :: r), p) none (j1, (l, r), p ++ [reassoc (a, bc)])
  /-- `pure.out1 → o_out` -/
  | out (v : (T₁ × T₂) × T₃) : RhsStep (j1, j2, v :: p) (some (.out v)) (j1, j2, p)

def rhs (T₁ T₂ T₃ : Type) : System (Event T₁ T₂ T₃) :=
  ⟨RhsState T₁ T₂ T₃, (([], []), ([], []), []), RhsStep⟩

/-! ## Refinement -/

section Refinement
variable {E : Type}

/-- Zero or more internal steps. -/
inductive Silent (M : System E) : M.State → M.State → Prop where
  | refl (s) : Silent M s s
  | step {s s' s''} : M.Step s none s' → Silent M s' s'' → Silent M s s''

/-- `impl ⊑ spec`: a relation `R` links the initial states and is preserved by every
step of `impl`, which `spec` matches, after some internal steps if needed. -/
def Refines (impl spec : System E) : Prop :=
  ∃ R : impl.State → spec.State → Prop,
    R impl.init spec.init ∧
    ∀ i s, R i s →
      (∀ e i', impl.Step i (some e) i' →
        ∃ s₁ s₂, Silent spec s s₁ ∧ spec.Step s₁ (some e) s₂ ∧ R i' s₂) ∧
      (∀ i', impl.Step i none i' →
        ∃ s', Silent spec s s' ∧ R i' s')

infix:50 " ⊑ " => Refines

end Refinement

/-! ## Correctness -/

section Correctness
open ReachingStar (Rule Method trans_refl φ_ind star star_extend relation_flush
  relation_flush_method_int relation_method_int has_diamond_property_on
  commutes_method_rule_upto_on enough_star_upto)
variable {T₁ T₂ T₃ : Type}

/-- The rules of `rhs`: its internal steps. -/
def rule : Rule (RhsState T₁ T₂ T₃) := fun i i' => RhsStep i none i'

/-- The methods of `rhs`: its observable steps. -/
def method_i : Method (RhsState T₁ T₂ T₃) (Event T₁ T₂ T₃) := fun i e i' => RhsStep i (some e) i'

/-! ### How `lhs` answers each method

`method_s` is ours to choose: `Refines` only asks that `lhs` matches an observable step of `rhs`
after some internal steps. Following Graphiti's `φ₃` for this rewrite, `lhs` keeps no pair: it
takes an input directly, and fires `link` exactly once, right before an output. -/

/-- The methods of `lhs`, with its internal step pinned down: an input is taken directly; an
output is preceded by exactly one `link`. -/
def method_s : Method (LhsState T₁ T₂ T₃) (Event T₁ T₂ T₃)
  | s, .out v, s' => ∃ s₁, LhsStep s none s₁ ∧ LhsStep s₁ (some (.out v)) s'
  | s, e, s' => LhsStep s (some e) s'

/-- `method_s` is a particular way of answering: internal steps, then the observable step; this is
what `Refines` asks for. -/
theorem method_s_sound {s s' : LhsState T₁ T₂ T₃} {e : Event T₁ T₂ T₃} (h : method_s s e s') :
    ∃ s₁, Silent (lhs T₁ T₂ T₃) s s₁ ∧ LhsStep s₁ (some e) s' := by
  cases e with
  | out v => obtain ⟨s₁, hl, ho⟩ := h; exact ⟨s₁, Silent.step hl (Silent.refl _), ho⟩
  | _ => exact ⟨s, Silent.refl _, h⟩

/-- The direct simulation relation, `φ`, valid in every state. Read each circuit from the
output backwards (`lhs`: `join2`, then `join1`; `rhs`: `pure`, then `join2`, then `join1`):
the `T₁` values still inside, the `T₂` values and the `T₃` values form three streams, and
they are the same on both sides. The rules move values from one FIFO to the next without
changing the streams, so `φ` holds before and after them. It is not used in the refinement
proof; it is here to compare with the flush relation `φ₀` below (`φ₀_iff`). -/
def φ : RhsState T₁ T₂ T₃ → LhsState T₁ T₂ T₃ → Prop
  | ((l1, r1), (l2, r2), p), ((q0, q1), (q12, q2)) =>
      q12.map Prod.fst ++ q0 = p.map (·.1.1) ++ l2 ∧
      q12.map Prod.snd ++ q1 = p.map (·.1.2) ++ r2.map Prod.fst ++ l1 ∧
      q2 = p.map Prod.snd ++ r2.map Prod.snd ++ r1

/-! ### Normal forms of `rhs`

A stuck state of `rhs` is determined by its three streams: `nf` computes it. -/

/-- The stuck state of `rhs` whose three streams are `A`, `B`, `C`: as many triples as possible
in `pure`, then the leftover `a`s or the leftover `(b, c)` pairs in `join2`, then the leftover
`b`s or `c`s in `join1`. -/
def nf : List T₁ → List T₂ → List T₃ → RhsState T₁ T₂ T₃
  | a :: A, b :: B, c :: C => ((nf A B C).1, (nf A B C).2.1, ((a, b), c) :: (nf A B C).2.2)
  | [],     b :: B, c :: C => ((nf [] B C).1, ([], (b, c) :: (nf [] B C).2.1.2), [])
  | A,      [],     C      => (([], C), (A, []), [])
  | A,      B,      []     => ((B, []), (A, []), [])

theorem nf_C_nil (A : List T₁) (B : List T₂) : nf A B ([] : List T₃) = ((B, []), (A, []), []) := by
  cases B <;> simp [nf]

/-- Each join of a normal form has an empty FIFO. -/
theorem nf_shape (A : List T₁) (B : List T₂) (C : List T₃) :
    ((nf A B C).1.1 = [] ∨ (nf A B C).1.2 = []) ∧
      ((nf A B C).2.1.1 = [] ∨ (nf A B C).2.1.2 = []) := by
  induction B generalizing A C with
  | nil => simp [nf]
  | cons b B ih =>
    cases C with
    | nil => simp [nf]
    | cons c C =>
      cases A with
      | nil => exact ⟨by simpa [nf] using (ih [] C).1, by simp [nf]⟩
      | cons a A => simpa [nf] using ih A C

/-- A normal form is stuck. -/
theorem nf_stuck (A : List T₁) (B : List T₂) (C : List T₃) : ∀ i', ¬ rule (nf A B C) i' := by
  have h := nf_shape A B C
  rcases hnf : nf A B C with ⟨⟨l1, r1⟩, ⟨l2, r2⟩, p⟩
  simp only [hnf] at h
  rintro i' hr
  cases hr with
  | link1 b c => exact h.1.elim (List.cons_ne_nil b _) (List.cons_ne_nil c _)
  | link2 a bc => exact h.2.elim (List.cons_ne_nil a _) (List.cons_ne_nil bc _)

/-- With no `a`, `join2` holds no `a` and `pure` is empty. -/
theorem nf_nil (B : List T₂) (C : List T₃) :
    ∃ l1 r1 r2, nf ([] : List T₁) B C = ((l1, r1), ([], r2), []) := by
  cases B <;> cases C <;> exact ⟨_, _, _, rfl⟩

/-- `pure` holds `v` first only if the three streams start with its components; popping `v`
leaves the normal form of the three tails: same joins, `pure` without its head. -/
theorem nf_out {A : List T₁} {B : List T₂} {C : List T₃} {v p}
    (h : (nf A B C).2.2 = v :: p) :
    ∃ A' B' C', A = v.1.1 :: A' ∧ B = v.1.2 :: B' ∧ C = v.2 :: C' ∧
      nf A' B' C' = ((nf A B C).1, (nf A B C).2.1, p) := by
  cases A <;> cases B <;> cases C <;> simp only [nf] at h <;> cases h
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- Appending `a` to the `T₁` stream: `join2` holds no pair and the `a` queues up, or it holds
pairs and `link2` fires. -/
theorem nf_in0 (A : List T₁) (B : List T₂) (C : List T₃) (a : T₁) :
    (∃ l1 r1 l2 p, nf A B C = ((l1, r1), (l2, []), p) ∧
      nf (A ++ [a]) B C = ((l1, r1), (l2 ++ [a], []), p)) ∨
    (∃ l1 r1 bc r2 p, nf A B C = ((l1, r1), ([], bc :: r2), p) ∧
      nf (A ++ [a]) B C = ((l1, r1), ([], r2), p ++ [reassoc (a, bc)])) := by
  induction B generalizing A C with
  | nil => exact Or.inl ⟨[], C, A, [], by simp [nf], by simp [nf]⟩
  | cons b B ih =>
    cases C with
    | nil => exact Or.inl ⟨b :: B, [], A, [], by simp [nf], by simp [nf]⟩
    | cons c C =>
      cases A with
      | nil =>
        obtain ⟨l1, r1, r2, hn⟩ := nf_nil (T₁ := T₁) B C
        exact Or.inr ⟨l1, r1, (b, c), r2, [], by simp [nf, hn], by simp [nf, hn, reassoc]⟩
      | cons a' A =>
        rcases ih A C with ⟨l1, r1, l2, p, h1, h2⟩ | ⟨l1, r1, bc, r2, p, h1, h2⟩
        · exact Or.inl ⟨l1, r1, l2, ((a', b), c) :: p, by simp [nf, h1], by simp [nf, h2]⟩
        · exact Or.inr ⟨l1, r1, bc, r2, ((a', b), c) :: p, by simp [nf, h1], by simp [nf, h2]⟩

/-- Appending `b` to the `T₂` stream: no `c` waits and the `b` queues up; or a `c` waits and
`link1` fires, followed by `link2` if an `a` waits. -/
theorem nf_in1 (A : List T₁) (B : List T₂) (C : List T₃) (b : T₂) :
    (∃ l1 l2 r2 p, nf A B C = ((l1, []), (l2, r2), p) ∧
      nf A (B ++ [b]) C = ((l1 ++ [b], []), (l2, r2), p)) ∨
    (∃ c r1 a l2 p, nf A B C = (([], c :: r1), (a :: l2, []), p) ∧
      nf A (B ++ [b]) C = (([], r1), (l2, []), p ++ [((a, b), c)])) ∨
    (∃ c r1 r2 p, nf A B C = (([], c :: r1), ([], r2), p) ∧
      nf A (B ++ [b]) C = (([], r1), ([], r2 ++ [(b, c)]), p)) := by
  induction B generalizing A C with
  | nil =>
    cases C with
    | nil => exact Or.inl ⟨[], A, [], [], by simp [nf], by simp [nf]⟩
    | cons c C =>
      cases A with
      | nil => exact Or.inr (Or.inr ⟨c, C, [], [], by simp [nf], by simp [nf]⟩)
      | cons a A => exact Or.inr (Or.inl ⟨c, C, a, A, [], by simp [nf], by simp [nf]⟩)
  | cons b' B ih =>
    cases C with
    | nil => exact Or.inl ⟨b' :: B, A, [], [], by simp [nf], by simp [nf]⟩
    | cons c C =>
      cases A with
      | nil =>
        obtain ⟨l1n, r1n, r2n, hn⟩ := nf_nil (T₁ := T₁) B C
        rcases ih [] C with ⟨l1, l2, r2, p, h1, h2⟩ | ⟨c', r1, a, l2, p, h1, h2⟩ |
          ⟨c', r1, r2, p, h1, h2⟩
        · exact Or.inl ⟨l1, [], (b', c) :: r2, [], by simp [nf, h1], by simp [nf, h2]⟩
        · rw [hn] at h1; cases h1
        · exact Or.inr (Or.inr ⟨c', r1, (b', c) :: r2, [], by simp [nf, h1], by simp [nf, h2]⟩)
      | cons a' A =>
        rcases ih A C with ⟨l1, l2, r2, p, h1, h2⟩ | ⟨c', r1, a, l2, p, h1, h2⟩ |
          ⟨c', r1, r2, p, h1, h2⟩
        · exact Or.inl ⟨l1, l2, r2, ((a', b'), c) :: p, by simp [nf, h1], by simp [nf, h2]⟩
        · exact Or.inr (Or.inl ⟨c', r1, a, l2, ((a', b'), c) :: p, by simp [nf, h1],
            by simp [nf, h2]⟩)
        · exact Or.inr (Or.inr ⟨c', r1, r2, ((a', b'), c) :: p, by simp [nf, h1],
            by simp [nf, h2]⟩)

/-- Appending `c` to the `T₃` stream: no `b` waits and the `c` queues up; or a `b` waits and
`link1` fires, followed by `link2` if an `a` waits. -/
theorem nf_in2 (A : List T₁) (B : List T₂) (C : List T₃) (c : T₃) :
    (∃ r1 l2 r2 p, nf A B C = (([], r1), (l2, r2), p) ∧
      nf A B (C ++ [c]) = (([], r1 ++ [c]), (l2, r2), p)) ∨
    (∃ b l1 a l2 p, nf A B C = ((b :: l1, []), (a :: l2, []), p) ∧
      nf A B (C ++ [c]) = ((l1, []), (l2, []), p ++ [((a, b), c)])) ∨
    (∃ b l1 r2 p, nf A B C = ((b :: l1, []), ([], r2), p) ∧
      nf A B (C ++ [c]) = ((l1, []), ([], r2 ++ [(b, c)]), p)) := by
  induction B generalizing A C with
  | nil => exact Or.inl ⟨C, A, [], [], by simp [nf], by simp [nf]⟩
  | cons b' B ih =>
    cases C with
    | nil =>
      cases A with
      | nil => exact Or.inr (Or.inr ⟨b', B, [], [], by simp [nf], by simp [nf, nf_C_nil]⟩)
      | cons a A =>
        exact Or.inr (Or.inl ⟨b', B, a, A, [], by simp [nf], by simp [nf, nf_C_nil]⟩)
    | cons c' C =>
      cases A with
      | nil =>
        obtain ⟨l1n, r1n, r2n, hn⟩ := nf_nil (T₁ := T₁) B C
        rcases ih [] C with ⟨r1, l2, r2, p, h1, h2⟩ | ⟨b, l1, a, l2, p, h1, h2⟩ |
          ⟨b, l1, r2, p, h1, h2⟩
        · exact Or.inl ⟨r1, [], (b', c') :: r2, [], by simp [nf, h1], by simp [nf, h2]⟩
        · rw [hn] at h1; cases h1
        · exact Or.inr (Or.inr ⟨b, l1, (b', c') :: r2, [], by simp [nf, h1], by simp [nf, h2]⟩)
      | cons a' A =>
        rcases ih A C with ⟨r1, l2, r2, p, h1, h2⟩ | ⟨b, l1, a, l2, p, h1, h2⟩ |
          ⟨b, l1, r2, p, h1, h2⟩
        · exact Or.inl ⟨r1, l2, r2, ((a', b'), c') :: p, by simp [nf, h1], by simp [nf, h2]⟩
        · exact Or.inr (Or.inl ⟨b, l1, a, l2, ((a', b'), c') :: p, by simp [nf, h1],
            by simp [nf, h2]⟩)
        · exact Or.inr (Or.inr ⟨b, l1, r2, ((a', b'), c') :: p, by simp [nf, h1],
            by simp [nf, h2]⟩)

/-- The three streams of a normal form are its arguments. -/
theorem nf_streams (A : List T₁) (B : List T₂) (C : List T₃) :
    (nf A B C).2.2.map (·.1.1) ++ (nf A B C).2.1.1 = A ∧
    (nf A B C).2.2.map (·.1.2) ++ (nf A B C).2.1.2.map Prod.fst ++ (nf A B C).1.1 = B ∧
    (nf A B C).2.2.map Prod.snd ++ (nf A B C).2.1.2.map Prod.snd ++ (nf A B C).1.2 = C := by
  induction B generalizing A C with
  | nil => simp [nf]
  | cons b B ih =>
    cases C with
    | nil => simp [nf]
    | cons c C =>
      cases A with
      | nil =>
        obtain ⟨l1, r1, r2, hn⟩ := nf_nil (T₁ := T₁) B C
        have h := ih [] C
        simp only [hn, List.map_nil, List.nil_append] at h
        simp [nf, hn, h.2.1, h.2.2]
      | cons a A => simpa [nf] using ih A C

/-! ### The flush relation `φ₀`

Two clauses: `lhs` holds no pair (`q12 = []`), and the stuck state of `rhs` is the normal form of
its three input FIFOs. No emptiness clause on `rhs` (it is built into `nf`, `nf_shape`) and no
stream equation (the streams of `lhs` are its input FIFOs). -/

/-- The flush relation: `lhs` holds no pair, and the stuck state of `rhs` is the normal form of
the three input FIFOs of `lhs`. -/
def φ₀ : RhsState T₁ T₂ T₃ → LhsState T₁ T₂ T₃ → Prop
  | i, ((q0, q1), (q12, q2)) => q12 = [] ∧ i = nf q0 q1 q2

/-! ### `φ` versus `φ₀`

Both say that the two circuits hold the same values. They differ in where they hold and in how
they say it.

* `φ` holds in every state. It cannot say more than the three stream equations: a state of
  `rhs` that is not stuck may hold the same values in several ways (an `a` and a pair `(b, c)`
  waiting in `join2`, or already combined in `pure`), and `lhs` may or may not have fired its
  `link`. So `φ` has to compare the five FIFOs of `rhs` with the four FIFOs of `lhs` stream by
  stream: `q12.map Prod.fst ++ q0` against `p.map (·.1.1) ++ l2`, and so on.
* `φ₀` holds only in the flushed states of `rhs`, and only against the states of `lhs` that hold
  no pair (`method_s` never leaves one). The first restriction turns the relation into a function
  of the state of `lhs`: a flushed state of `rhs` is determined by its three streams, so instead
  of three equations between FIFOs there is one equation, `i = nf q0 q1 q2`. The second makes it
  one-to-one and removes the last computation: since `lhs` holds no pair, its streams are its
  three input FIFOs, and the arguments of `nf` are read off `lhs` directly.

The rest of the proof is the same from either relation: the diamonds of `rhs` and the three
obligations below. `φ` could serve as the flush relation too, if `lhs` were free to fire `link`
at any time before an observable step: every obligation would then hold with zero rule steps,
because `φ` already holds after the rules and after the same method on both sides (for `out`,
`lhs` needs at most one `link` first). That is a direct simulation, and the flush mechanism does
nothing. With `φ₀` the rules actually run after each input (`nf_in0`, `nf_in1`, `nf_in2`: at
most two of them; after `out` none, `nf_out`) to bring `rhs` back to a flushed state, and the
relation to invent is the function `nf`, read off the circuit.

In one line: `φ₀` is `φ` plus "`rhs` is stuck" plus "`lhs` holds no pair" (`φ₀_iff`). So `φ₀`
implies `φ` (`φ₀_implies_φ`), and not the other way round: `rhs` may hold the right values
without being flushed (`φ_not_φ₀_unflushed`), or `lhs` may already have formed a pair
(`φ_not_φ₀_pair`). -/

/-- `φ₀` implies `φ`: the streams of `nf q0 q1 q2` are `q0`, `q1`, `q2`, and `lhs` holds no
pair, so its streams are `q0`, `q1`, `q2` as well. -/
theorem φ₀_implies_φ {i : RhsState T₁ T₂ T₃} {s : LhsState T₁ T₂ T₃} (h : φ₀ i s) : φ i s := by
  obtain ⟨⟨q0, q1⟩, ⟨q12, q2⟩⟩ := s
  obtain ⟨rfl, rfl⟩ := h
  have hs := nf_streams q0 q1 q2
  rcases hn : nf q0 q1 q2 with ⟨⟨l1, r1⟩, ⟨l2, r2⟩, p⟩
  simp only [hn] at hs
  simp only [φ, List.map_nil, List.nil_append]
  exact ⟨hs.1.symm, hs.2.1.symm, hs.2.2.symm⟩

/-- `φ` does not imply `φ₀`, first way: `rhs` holds the right values but is not flushed (`join2`
holds an `a` and a pair, `link2` can fire). -/
theorem φ_not_φ₀_unflushed (a : T₁) (b : T₂) (c : T₃) :
    φ ((([], []), ([a], [(b, c)]), []) : RhsState T₁ T₂ T₃) (([a], [b]), ([], [c])) ∧
    ¬ φ₀ ((([], []), ([a], [(b, c)]), []) : RhsState T₁ T₂ T₃) (([a], [b]), ([], [c])) :=
  ⟨⟨rfl, rfl, rfl⟩, fun h => by simp [φ₀, nf] at h⟩

/-- `φ` does not imply `φ₀`, second way: `rhs` is flushed and holds the right values, but `lhs`
has already formed the pair `(a, b)`. -/
theorem φ_not_φ₀_pair (a : T₁) (b : T₂) (c : T₃) :
    φ ((([], []), ([], []), [((a, b), c)]) : RhsState T₁ T₂ T₃) (([], []), ([(a, b)], [c])) ∧
    ¬ φ₀ ((([], []), ([], []), [((a, b), c)]) : RhsState T₁ T₂ T₃) (([], []), ([(a, b)], [c])) :=
  ⟨⟨rfl, rfl, rfl⟩, fun h => by simp [φ₀] at h⟩

/-- A stuck state of `rhs` is the normal form of its own streams. -/
theorem eq_nf_of_stuck (l1 : List T₂) (r1 : List T₃) (l2 : List T₁) (r2 : List (T₂ × T₃))
    (p : List ((T₁ × T₂) × T₃)) (h1 : l1 = [] ∨ r1 = []) (h2 : l2 = [] ∨ r2 = []) :
    ((l1, r1), (l2, r2), p) =
      nf (p.map (·.1.1) ++ l2) (p.map (·.1.2) ++ r2.map Prod.fst ++ l1)
        (p.map Prod.snd ++ r2.map Prod.snd ++ r1) := by
  induction p with
  | cons v p ih =>
    obtain ⟨⟨a, b⟩, c⟩ := v
    simp only [List.map_cons, List.cons_append, nf]
    rw [← ih]
  | nil =>
    simp only [List.map_nil, List.nil_append]
    rcases h2 with rfl | rfl
    · induction r2 with
      | nil =>
        rcases h1 with rfl | rfl
        · simp [nf]
        · simp [nf_C_nil]
      | cons bc r2 ih =>
        obtain ⟨b, c⟩ := bc
        simp only [List.map_cons, List.cons_append, nf]
        rw [← ih]
    · simp only [List.map_nil, List.nil_append]
      rcases h1 with rfl | rfl
      · simp [nf]
      · simp [nf_C_nil]

/-- `φ₀`, at a higher level: `φ` restricted to the flushed states of `rhs` and to the states of
`lhs` that hold no pair. -/
theorem φ₀_iff {i : RhsState T₁ T₂ T₃} {s : LhsState T₁ T₂ T₃} :
    φ₀ i s ↔ φ i s ∧ (∀ i', ¬ rule i i') ∧ s.2.1 = [] := by
  obtain ⟨⟨l1, r1⟩, ⟨l2, r2⟩, p⟩ := i
  obtain ⟨⟨q0, q1⟩, ⟨q12, q2⟩⟩ := s
  constructor
  · intro h
    have hφ := φ₀_implies_φ h
    obtain ⟨rfl, hi⟩ := h
    refine ⟨hφ, ?_, rfl⟩
    rw [hi]; exact nf_stuck _ _ _
  · rintro ⟨⟨h1, h2, h3⟩, hnf, hq⟩
    obtain rfl : q12 = [] := hq
    have hs1 : l1 = [] ∨ r1 = [] := by
      cases l1 <;> cases r1 <;>
        first | exact Or.inl rfl | exact Or.inr rfl | exact absurd (by constructor) (hnf _)
    have hs2 : l2 = [] ∨ r2 = [] := by
      cases l2 <;> cases r2 <;>
        first | exact Or.inl rfl | exact Or.inr rfl | exact absurd (by constructor) (hnf _)
    simp only [List.map_nil, List.nil_append] at h1 h2
    subst h1 h2 h3
    exact ⟨rfl, eq_nf_of_stuck l1 r1 l2 r2 p hs1 hs2⟩

/-- A sequence of rules from a normal form is empty, so `φ₀` still holds at its end. -/
theorem φ₀_rule {i i' : RhsState T₁ T₂ T₃} {s : LhsState T₁ T₂ T₃}
    (h : φ₀ i s) (hstep : trans_refl rule i i') : φ₀ i' s := by
  obtain ⟨⟨q0, q1⟩, ⟨q12, q2⟩⟩ := s
  cases hstep with
  | refl => exact h
  | step hr _ => obtain ⟨-, rfl⟩ := h; exact absurd hr (nf_stuck _ _ _ _)

theorem rhs_relation_flush (i i' : RhsState T₁ T₂ T₃) (s : LhsState T₁ T₂ T₃) :
    relation_flush φ₀ i i' s rule :=
  fun h hstep => ⟨i', trans_refl.refl, φ₀_rule h hstep⟩

/-- A method of `rhs` is also possible in `lhs`: an input directly, an output after one `link`. -/
theorem rhs_relation_method_int (i i' i'' : RhsState T₁ T₂ T₃) (s : LhsState T₁ T₂ T₃)
    (e : Event T₁ T₂ T₃) : relation_method_int φ₀ rule method_i method_s i i' i'' s e := by
  obtain ⟨⟨q0, q1⟩, ⟨q12, q2⟩⟩ := s
  intro h hrules hm
  obtain ⟨rfl, h'⟩ := φ₀_rule h hrules
  cases hm with
  | in0 a => exact ⟨_, LhsStep.in0 a⟩
  | in1 b => exact ⟨_, LhsStep.in1 b⟩
  | in2 c => exact ⟨_, LhsStep.in2 c⟩
  | out v =>
    obtain ⟨⟨a, b⟩, c⟩ := v
    obtain ⟨A', B', C', rfl, rfl, rfl, -⟩ :=
      nf_out (v := ((a, b), c)) (congrArg (fun x : RhsState T₁ T₂ T₃ => x.2.2) h'.symm)
    exact ⟨_, _, LhsStep.link a b, LhsStep.out a b c⟩

/-- After the same method on both sides, the rules lead `rhs` to the normal form of the new
input FIFOs of `lhs` (at most two rules), and `lhs` holds no pair again. -/
theorem rhs_relation_flush_method_int (i i' i'' : RhsState T₁ T₂ T₃)
    (s s' : LhsState T₁ T₂ T₃) (e : Event T₁ T₂ T₃) :
    relation_flush_method_int φ₀ rule method_i method_s i i' i'' s s' e := by
  obtain ⟨⟨q0, q1⟩, ⟨q12, q2⟩⟩ := s
  rintro h hrule (hi : RhsStep _ _ _) hs
  obtain ⟨rfl, h'⟩ := φ₀_rule h hrule
  cases hi with
  | out v =>
    obtain ⟨s₁, hl, ho⟩ := hs
    cases hl with
    | link a b =>
      cases ho with
      | out _ _ c =>
      obtain ⟨A', B', C', hA, hB, hC, hn⟩ :=
        nf_out (v := ((a, b), c)) (congrArg (fun x : RhsState T₁ T₂ T₃ => x.2.2) h'.symm)
      obtain rfl := (List.cons.inj hA).2
      obtain rfl := (List.cons.inj hB).2
      obtain rfl := (List.cons.inj hC).2
      rw [← h'] at hn
      exact ⟨_, .refl, rfl, hn.symm⟩
  | in0 a =>
    cases hs
    rcases nf_in0 q0 q1 q2 a with ⟨l1, r1, l2, p, h1, h2⟩ | ⟨l1, r1, bc, r2, p, h1, h2⟩ <;>
      rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, rfl, h2.symm⟩
    · exact ⟨_, .step (.link2 a bc) .refl, rfl, h2.symm⟩
  | in1 b =>
    cases hs
    rcases nf_in1 q0 q1 q2 b with ⟨l1, l2, r2, p, h1, h2⟩ | ⟨c, r1, a, l2, p, h1, h2⟩ |
      ⟨c, r1, r2, p, h1, h2⟩ <;> rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, rfl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) (.step (.link2 a (b, c)) .refl), rfl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) .refl, rfl, h2.symm⟩
  | in2 c =>
    cases hs
    rcases nf_in2 q0 q1 q2 c with ⟨r1, l2, r2, p, h1, h2⟩ | ⟨b, l1, a, l2, p, h1, h2⟩ |
      ⟨b, l1, r2, p, h1, h2⟩ <;> rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, rfl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) (.step (.link2 a (b, c)) .refl), rfl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) .refl, rfl, h2.symm⟩

/-! ### Diamonds of `rhs` -/

/-- Diamond of the rules: `join1` and `join2` of `rhs` fire in any order. -/
theorem rule_diamond :
    has_diamond_property_on (fun _ : RhsState T₁ T₂ T₃ => True) (trans_refl rule) := by
  -- one rule against one rule: the same rule twice, or `link1` and `link2`, which commute
  have one_step (a b c : RhsState T₁ T₂ T₃) (hb : rule a b) (hc : rule a c) :
      ∃ d, Relation.ReflGen rule b d ∧ Relation.ReflTransGen rule c d := by
    cases hb <;> cases hc
    · exact ⟨_, .refl, .refl⟩
    · exact ⟨_, .single (.link2 _ _), .single (.link1 _ _)⟩
    · exact ⟨_, .single (.link1 _ _), .single (.link2 _ _)⟩
    · exact ⟨_, .refl, .refl⟩
  -- Church–Rosser lifts it to sequences of rules
  intro a b c _ hac hab
  simp only [ReachingStar.trans_refl_equiv] at hac hab ⊢
  exact Relation.church_rosser one_step hac hab

/-- Diamond of a method and the rules: a method is still enabled after the rules,
and the two orders lead to the same state. -/
theorem method_rule_diamond :
    commutes_method_rule_upto_on (fun _ : RhsState T₁ T₂ T₃ => True) method_i rule := by
  -- one rule against one method: each is still enabled after the other, same final state
  have one_step {a b c : RhsState T₁ T₂ T₃} {e : Event T₁ T₂ T₃} (hr : rule a b)
      (hm : method_i a e c) : ∃ d, method_i b e d ∧ rule c d := by
    cases hr <;> cases hm <;> exact ⟨_, by constructor, by constructor⟩
  -- it lifts to sequences of rules, and no extra internal step is needed
  apply ReachingStar.commutes_upto_of_weakly_on
  intro _ _ _ _ _
  exact ReachingStar.commutes_strongly_method_rule_implies_weak method_i rule @one_step

/-! ### Why `φ₀` is enough

`enough_star_upto` (`Star.Commute.ARS`) builds the simulation relation from `φ₀` alone. It needs:

* three facts about `φ₀`, the only places where the relation appears: `rhs_relation_flush`
  (after the rules, `rhs` is flushed again: nothing to do, a normal form is stuck, `nf_stuck`),
  `rhs_relation_method_int` (every method of `rhs` is possible in `lhs`: an input directly; for
  `out`, `nf_out` says that `q0`, `q1`, `q2` start with the three components of the value, so
  `lhs` does `link` then `out`) and `rhs_relation_flush_method_int` (after the same method on
  both sides, the rules bring `rhs` back to a flushed state related to the new state of `lhs`:
  `nf_in0`, `nf_in1`, `nf_in2`, at most two rules, and `nf_out`, no rule);
* two diamonds about `rhs` alone, independent of the relation: the rules commute with each
  other (`rule_diamond`) and with the methods (`method_rule_diamond`), on every state
  (`enough_star_upto` takes a predicate `R` on which the diamonds must hold, with closure
  hypotheses for it; here `R := fun _ => True` and they are `trivial`);
* the choice of `method_s`, how `lhs` answers each method.

From these it gives `φ_ind φ₀ rule` as the simulation relation: `i` is related to `s` when the
rules bring `i` to a flushed state related to `s` by `φ₀`. `rhs_refines_lhs` wraps this into
`Refines`, one event at a time. The direct relation `φ` is never used in it.

`φ₀` can be this small because a flushed state of `rhs` is determined by its three streams
(`nf`), and because `lhs` keeps no pair (choice of `method_s`): the relation is the graph of a
function from the states of `lhs` holding no pair to the flushed states of `rhs`. -/

theorem rhs_refines_lhs : rhs T₁ T₂ T₃ ⊑ lhs T₁ T₂ T₃ := by
  have key (i i' : RhsState T₁ T₂ T₃) (s : LhsState T₁ T₂ T₃) (l : List (Event T₁ T₂ T₃)) :
      φ_ind φ₀ rule i s → star_extend rule method_i i l i' →
        ∃ s', star method_s s l s' ∧ φ_ind φ₀ rule i' s' :=
    enough_star_upto φ₀ rule method_i method_s (fun _ => True) i i' s l
      rhs_relation_flush rhs_relation_flush_method_int rhs_relation_method_int
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) rule_diamond method_rule_diamond trivial
  refine ⟨φ_ind φ₀ rule, φ_ind.base _ _ ⟨rfl, rfl⟩, fun i s h => ⟨?_, ?_⟩⟩
  · intro e i' hstep
    obtain ⟨s', hs, hφ⟩ :=
      key i i' s [e] h (star_extend.step_ext _ _ _ _ _ (star_extend.refl i) hstep)
    cases hs with
    | step _ _ _ _ h0 hm =>
      cases h0
      obtain ⟨s₁, hsil, hout⟩ := method_s_sound hm
      exact ⟨s₁, s', hsil, hout, hφ⟩
  · intro i' hstep
    obtain ⟨s', hs, hφ⟩ :=
      key i i' s [] h (star_extend.step_int _ _ _ _ (star_extend.refl i)
        (trans_refl.step hstep trans_refl.refl))
    cases hs
    exact ⟨s, Silent.refl s, hφ⟩

end Correctness

end JoinJoin
