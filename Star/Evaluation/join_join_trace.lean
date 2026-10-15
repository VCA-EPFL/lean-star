/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Evaluation.join_join

/-!
# The join–join rewrite against a specification without rules

`ReachingStar.trace_inclusion` compares an implementation with rules and methods against a
specification with **methods only** (`spec_behaviour method_s := star method_s`). `lhs` has a rule
(`link`, `join1` firing), so in `join_join.lean` the framework is applied to `method_s`, a way of
answering each event with `lhs` (an input directly, an output after one `link`), and the result is
wrapped into `Refines`.

Here the specification has no rules at all: `join3` keeps the three input FIFOs and answers `out`
by popping the three heads at once. It is `lhs` with `link` fused into `out`. The framework then
applies literally:

* `rhs_trace_inclusion`: every trace of `rhs` is a trace of `join3`, by `ReachingStar.trace_inclusion`
  with the six hypotheses (flush relation `ψ`, diamonds of `join_join.lean`);
* `join3_refines_lhs`: every step of `join3` is a step of `lhs` (an output is `link` then `out`), so
  `join3` is a faithful specification of `lhs`.

The flush relation is one equation: the state of `rhs` is the normal form of the three FIFOs of
`join3` (`nf`, from `join_join.lean`).
-/

namespace JoinJoin

section Join3
open ReachingStar (trans_refl relation_flush relation_flush_method_int relation_method_int
  relation_init)
variable {T₁ T₂ T₃ : Type}

/-! ## The specification `join3` -/

/-- State of `join3`: one FIFO per input port. -/
abbrev Join3State (T₁ T₂ T₃ : Type) := List T₁ × List T₂ × List T₃

/-- The methods of `join3`; there are no rules. -/
inductive Join3Step : Join3State T₁ T₂ T₃ → Event T₁ T₂ T₃ → Join3State T₁ T₂ T₃ → Prop where
  | in0 {A B C} (a : T₁) : Join3Step (A, B, C) (.in0 a) (A ++ [a], B, C)
  | in1 {A B C} (b : T₂) : Join3Step (A, B, C) (.in1 b) (A, B ++ [b], C)
  | in2 {A B C} (c : T₃) : Join3Step (A, B, C) (.in2 c) (A, B, C ++ [c])
  /-- The three heads leave together. -/
  | out {A B C} (a : T₁) (b : T₂) (c : T₃) :
      Join3Step (a :: A, b :: B, c :: C) (.out ((a, b), c)) (A, B, C)

/-- `join3` as a `System`: no internal step. -/
def join3 (T₁ T₂ T₃ : Type) : System (Event T₁ T₂ T₃) :=
  ⟨Join3State T₁ T₂ T₃, ([], [], []), fun s e s' => ∃ e', e = some e' ∧ Join3Step s e' s'⟩

/-! ## The flush relation -/

/-- The state of `rhs` is the normal form of the three FIFOs of `join3`. -/
def ψ (i : RhsState T₁ T₂ T₃) (s : Join3State T₁ T₂ T₃) : Prop := i = nf s.1 s.2.1 s.2.2

/-- A normal form is stuck: the rules do nothing from a state related by `ψ`. -/
theorem ψ_rule {i i' : RhsState T₁ T₂ T₃} {s : Join3State T₁ T₂ T₃}
    (h : ψ i s) (hstep : trans_refl rule i i') : ψ i' s := by
  cases hstep with
  | refl => exact h
  | step hr _ => rw [h] at hr; exact absurd hr (nf_stuck _ _ _ _)

theorem j3_relation_init :
    relation_init ψ (rhs T₁ T₂ T₃).init (join3 T₁ T₂ T₃).init := rfl

theorem j3_relation_flush (i i' : RhsState T₁ T₂ T₃) (s : Join3State T₁ T₂ T₃) :
    relation_flush ψ i i' s rule :=
  fun h hstep => ⟨i', trans_refl.refl, ψ_rule h hstep⟩

/-- A method of `rhs` is possible in `join3`: an input always; an output `((a, b), c)` only when
the three FIFOs start with `a`, `b`, `c` (`nf_out`). -/
theorem j3_relation_method_int (i i' i'' : RhsState T₁ T₂ T₃) (s : Join3State T₁ T₂ T₃)
    (e : Event T₁ T₂ T₃) : relation_method_int ψ rule method_i Join3Step i i' i'' s e := by
  obtain ⟨q0, q1, q2⟩ := s
  intro h hrules hm
  have h' : i' = nf q0 q1 q2 := ψ_rule h hrules
  cases hm with
  | in0 a => exact ⟨_, Join3Step.in0 a⟩
  | in1 b => exact ⟨_, Join3Step.in1 b⟩
  | in2 c => exact ⟨_, Join3Step.in2 c⟩
  | out v =>
    obtain ⟨⟨a, b⟩, c⟩ := v
    obtain ⟨A', B', C', rfl, rfl, rfl, -⟩ :=
      nf_out (v := ((a, b), c)) (congrArg (fun x : RhsState T₁ T₂ T₃ => x.2.2) h'.symm)
    exact ⟨_, Join3Step.out a b c⟩

/-- After the same method on both sides, the rules bring `rhs` to the normal form of the new FIFOs
(at most two rules after an input, none after an output). -/
theorem j3_relation_flush_method_int (i i' i'' : RhsState T₁ T₂ T₃)
    (s s' : Join3State T₁ T₂ T₃) (e : Event T₁ T₂ T₃) :
    relation_flush_method_int ψ rule method_i Join3Step i i' i'' s s' e := by
  obtain ⟨q0, q1, q2⟩ := s
  rintro h hrule (hi : RhsStep _ _ _) hs
  have h' : i' = nf q0 q1 q2 := ψ_rule h hrule
  cases hi with
  | out v =>
    cases hs with
    | out a b c =>
      obtain ⟨A', B', C', hA, hB, hC, hn⟩ :=
        nf_out (v := ((a, b), c)) (congrArg (fun x : RhsState T₁ T₂ T₃ => x.2.2) h'.symm)
      obtain rfl := (List.cons.inj hA).2
      obtain rfl := (List.cons.inj hB).2
      obtain rfl := (List.cons.inj hC).2
      rw [← h'] at hn
      exact ⟨_, .refl, hn.symm⟩
  | in0 a =>
    cases hs
    rcases nf_in0 q0 q1 q2 a with ⟨l1, r1, l2, p, h1, h2⟩ | ⟨l1, r1, bc, r2, p, h1, h2⟩ <;>
      rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, h2.symm⟩
    · exact ⟨_, .step (.link2 a bc) .refl, h2.symm⟩
  | in1 b =>
    cases hs
    rcases nf_in1 q0 q1 q2 b with ⟨l1, l2, r2, p, h1, h2⟩ | ⟨c, r1, a, l2, p, h1, h2⟩ |
      ⟨c, r1, r2, p, h1, h2⟩ <;> rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) (.step (.link2 a (b, c)) .refl), h2.symm⟩
    · exact ⟨_, .step (.link1 b c) .refl, h2.symm⟩
  | in2 c =>
    cases hs
    rcases nf_in2 q0 q1 q2 c with ⟨r1, l2, r2, p, h1, h2⟩ | ⟨b, l1, a, l2, p, h1, h2⟩ |
      ⟨b, l1, r2, p, h1, h2⟩ <;> rw [h1] at h' <;> cases h'
    · exact ⟨_, .refl, h2.symm⟩
    · exact ⟨_, .step (.link1 b c) (.step (.link2 a (b, c)) .refl), h2.symm⟩
    · exact ⟨_, .step (.link1 b c) .refl, h2.symm⟩

/-! ## Trace inclusion, by the framework -/

/-- **Every trace of `rhs` is a trace of `join3`**: `ReachingStar.trace_inclusion` applied as it
is, with the specification `join3` (methods only). The two diamonds are those of `join_join.lean`,
proved on every state, hence on the reachable ones. -/
theorem rhs_trace_inclusion (l : List (Event T₁ T₂ T₃)) :
    ReachingStar.imp_behaviour rule method_i l (rhs T₁ T₂ T₃).init →
    ReachingStar.spec_behaviour Join3Step l (join3 T₁ T₂ T₃).init :=
  ReachingStar.trace_inclusion ψ rule method_i Join3Step l (rhs T₁ T₂ T₃).init
    (join3 T₁ T₂ T₃).init j3_relation_flush j3_relation_flush_method_int j3_relation_method_int
    (fun _ hac hab => rule_diamond trivial hac hab)
    (fun _ hab hac => method_rule_diamond trivial hab hac)
    j3_relation_init

/-! ## `join3` is a faithful specification of `lhs` -/

/-- Every step of `join3` is a step of `lhs`: `join3` in state `(A, B, C)` is `lhs` with the three
FIFOs and no pair inside; an output is `link` then `out`. -/
theorem join3_refines_lhs : join3 T₁ T₂ T₃ ⊑ lhs T₁ T₂ T₃ := by
  refine ⟨fun s t => t = ((s.1, s.2.1), ([], s.2.2)), rfl, fun s t h => ⟨?_, ?_⟩⟩
  · rintro e s' ⟨e', he, hs⟩
    cases he
    subst h
    cases hs with
    | in0 a => exact ⟨_, _, Silent.refl _, LhsStep.in0 a, rfl⟩
    | in1 b => exact ⟨_, _, Silent.refl _, LhsStep.in1 b, rfl⟩
    | in2 c => exact ⟨_, _, Silent.refl _, LhsStep.in2 c, rfl⟩
    | out a b c =>
      exact ⟨_, _, Silent.step (LhsStep.link a b) (Silent.refl _), LhsStep.out a b c, rfl⟩
  · rintro s' ⟨e', he, -⟩
    cases he

end Join3

end JoinJoin
