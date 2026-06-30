import Star.Commute.ARS
open ReachingStar

structure Imp where
  a : List Nat
  b : List Nat

inductive event
| enq (e : Nat)
| deq (e : Nat)

inductive imp_step_ext : Imp -> event -> Imp -> Prop where
| enqueue : ∀ l e,
    imp_step_ext l (event.enq e) {l with a := l.a ++ [e]}
| denqueue : ∀ l e rst,
    l.b = e :: rst ->
    imp_step_ext l (event.deq e) {l with b := rst}

inductive imp_step_int : Imp -> Imp -> Prop where
| enqueue : ∀ l e rst,
    l.a = e :: rst ->
    imp_step_int l {l with a := rst, b := l.b ++ [e]}


structure Spec where
  a : List Nat


inductive spec_step_ext : Spec -> event -> Spec -> Prop where
| enqueue : ∀ l e,
    spec_step_ext l (event.enq e) {l with a := l.a ++ [e]}
| denqueue : ∀ l e rst,
    l.a = e :: rst ->
    spec_step_ext l (event.deq e) {l with a := rst}

@[simp]
def base (i : Imp) (s : Spec) :=  i.b = s.a ∧ i.a = []

inductive φb : Imp -> Spec -> Prop where
| base : ∀ (i : Imp) (s : Spec),
          base i s ->
          φb i s
| rule_step : ∀ (i i' : Imp) (s : Spec),
              φb i' s ->
              imp_step_int i i' ->
              φb i s


inductive φf : Imp -> Spec -> Prop where
| base : ∀ (i : Imp) (s : Spec),
          i.b = [] ∧ i.a = [] ∧ s.a = []  ->
          φf i s
| rule_step : ∀ (i i' : Imp) (s : Spec),
              φf i s ->
              imp_step_int i i' ->
              φf i' s

inductive φ : Imp -> Spec -> Prop where
| base : ∀ (i : Imp) (s : Spec),
          i.b ++ i.a = s.a ->
          φ i s

def φ3 (i : Imp) (s : Spec) := i.b ++ i.a = s.a

theorem enoght_internal (i : Imp) (s : Spec) :
  φ i s -> ∀ i', imp_step_int i i' -> φ i' s := by
    intro hφ₀ i' hstep
    induction hφ₀ generalizing i'
    . constructor
      cases hstep
      simp_all

theorem enoght_external (i : Imp) (s : Spec) :
  φ i s -> ∀ i' e, imp_step_ext i e i' -> ∃ (s' : Spec), spec_step_ext s e s' ∧ φ i' s' := by
    intro h1 i' e h3
    cases h1
    . cases h3
      . constructor
        . constructor
          . constructor
          . constructor; simp_all; grind
      . constructor
        . constructor
          . constructor; rotate_left
            . rename_i rst _
              exact rst ++ i.a
            . simp_all
          . constructor; simp_all


theorem φ_flus_smaller_φ : ∀ i s,  i.b = s.a ∧ i.a = [] -> φb i s:= by
  intro i s h
  apply φb.base
  assumption

theorem φ_flus_smaller_φ_neq :¬ (∀ i s, φb i s -> (i.b = s.a ∧ i.a = [])):= by
    intro h
    have hstep : imp_step_int ⟨[0],[]⟩ ⟨[],[0]⟩ := by
      have := imp_step_int.enqueue (⟨[0],[]⟩ : Imp) 0 []
      simpa using this
    have hφb : φb ⟨[0],[]⟩ ⟨[0]⟩ := by
      apply φb.rule_step _ ⟨[],[0]⟩ _
      · apply φb.base; exact ⟨rfl, rfl⟩
      · exact hstep
    have := h ⟨[0],[]⟩ ⟨[0]⟩ hφb
    simp at this

/-
The internal step relation is deterministic: from a given state there is at
most one possible move (popping the head of field `a`).
-/
theorem imp_step_int_det :
    ∀ {a b c : Imp}, imp_step_int a b → imp_step_int a c → b = c := by
  intro a b c hab hbc
  cases hab; cases hbc; grind
/-
For a deterministic rule, two reductions from the same source are linearly
ordered: one reaches the other.
-/
theorem trans_refl_linear {A} {α : Rule A}
    (hdet : ∀ a b c : A, α a b → α a c → b = c) :
    ∀ {a b c : A}, trans_refl α a b → trans_refl α a c →
      trans_refl α b c ∨ trans_refl α c b := by
  intro a b c hab hbc
  induction hab generalizing c with
  | refl => exact Or.inl hbc
  | step hab' _ ih =>
    cases hbc with
    | refl => exact Or.inr (trans_refl.step hab' (by assumption))
    | step hbc' hrest =>
      have := hdet _ _ _ hab' hbc'
      subst this
      exact ih hrest
/-
A deterministic rule has the diamond property on its reflexive–transitive
closure (confluence).
-/
theorem diamond_of_det {A} {α : Rule A}
    (hdet : ∀ a b c : A, α a b → α a c → b = c) :
    has_diamond_property (trans_refl α) := by
  intro a b c h1 h2
  rcases trans_refl_linear hdet h1 h2 with h | h
  · exact ⟨b, h, trans_refl.refl⟩
  · exact ⟨c, trans_refl.refl, h⟩

theorem confluence1 : has_diamond_property (trans_refl imp_step_int) :=
  diamond_of_det (α := imp_step_int) (fun {_ _ _} h1 h2 => imp_step_int_det h1 h2)


theorem confluence_method_strong :
    commutes_strongly_method_rule imp_step_ext imp_step_int := by
      intro a b c e;
      cases e <;> rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ <;> cases a <;> simp_all +decide;
      · exact ⟨ _, imp_step_ext.enqueue _ _, imp_step_int.enqueue _ _ _ rfl ⟩;
      · exact ⟨ _, imp_step_ext.enqueue _ _, imp_step_int.enqueue _ _ _ rfl ⟩;

      · exact ⟨ _, imp_step_ext.denqueue _ _ _ rfl, imp_step_int.enqueue _ _ _ rfl ⟩

theorem confluence_method :
    commutes_weakly_method_rule imp_step_ext imp_step_int :=
  commutes_strongly_method_rule_implies_weak imp_step_ext imp_step_int
    confluence_method_strong






-- theorem enoght_internal1 (i : Imp) (s : Spec) :
--   φb i s -> ∀ i', imp_step_int i i' -> φb i' s := by
--     intro hφ₀ i' hstep
--     induction hφ₀ generalizing i'
--     . constructor
--       cases hstep
--       simp_all
--     . clear i s
--       rename_i i i'' s h1 h2 h4
--       clear h1
--       have hconf : has_diamond_property (imp_step_int) := by admit
--       specialize @hconf i i'' i' hstep h2
--       cases hconf; rename_i d H; rcases H with ⟨H1, H2⟩
--       specialize h4 d H2
--       apply φb.rule_step <;> try assumption


-- theorem enoght_internal1 (i : Imp) (s : Spec) :
--   φb i s -> ∀ i', trans_refl (imp_step_int) i i' -> φb i' s := by
--     intro hφ₀ i' hstep
--     induction hφ₀ generalizing i'
--     . constructor
--       cases hstep
--       . rename_i hstep _; cases hstep; simp_all
--       . simp_all
--     . clear i s
--       rename_i i i'' s h1 h2 h4
--       clear h1
--       have hconf : has_diamond_property (imp_step_int) := by admit
--       specialize @hconf i i'' i' hstep h2
--       cases hconf; rename_i d H; rcases H with ⟨H1, H2⟩
--       specialize h4 d H2
--       apply φb.rule_step <;> try assumption

theorem enoght_internal1 (i : Imp) (s : Spec) :
  φb i s -> ∀ i', imp_step_int i i' -> φb i' s := by
    intro hφ₀ i' hstep
    induction hφ₀ generalizing i'
    . constructor
      cases hstep; simp_all
    . clear i s
      rename_i i i'' s h1 h2 h4
      clear h1
      have hconf : has_diamond_property (imp_step_int) := by admit
      specialize @hconf i i'' i' hstep h2
      cases hconf; rename_i d H; rcases H with ⟨H1, H2⟩
      specialize h4 d H2
      apply φb.rule_step <;> try assumption

theorem enoght_external1 (i : Imp) (s : Spec) :
  φb i s -> ∀ i' e, imp_step_ext i e i' -> ∃ (s' : Spec), spec_step_ext s e s' ∧ φb i' s' := by
    intro h1 i' e h3
    induction h1 generalizing i'
    . cases h3
      . constructor
        . constructor
          . constructor
          . apply φb.rule_step; rotate_left
            . constructor <;> simp_all; rotate_left
              . assumption
              . rename_i i _ _ _ ; exact i.a
              . simp_all
            . constructor; simp_all
      . unfold base at *
        constructor
        . constructor
          . constructor; rotate_left
            . assumption
            . grind
          . constructor; simp_all
    . admit



inductive φf1 : Imp -> Spec -> Prop where
| base : ∀ (i : Imp) (s : Spec),
          i.b = s.a ∧ i.a = []  ->
          φf1 i s
| rule_step : ∀ (i i' : Imp) (s : Spec),
              φf1 i s ->
              imp_step_int i i' ->
              φf1 i' s


theorem enoght_internal2 (i : Imp) (s : Spec) :
  φf1 i s -> ∀ i', imp_step_int i i' -> φf1 i' s := by
    intro hφ₀ i' hstep
    exact φf1.rule_step i i' s hφ₀ hstep



theorem enoght_external2 (i : Imp) (s : Spec) :
  φf1 i s -> ∀ i' e, imp_step_ext i e i' -> ∃ (s' : Spec), spec_step_ext s e s' ∧ φf1 i' s' := by
    intro h1 i' e h3
    induction h1 generalizing i'
    . clear i s; rename_i i s h2
      cases h3
      . constructor
        . constructor
          . apply spec_step_ext.enqueue
          . simp_all
            rename_i e
            apply φf1.rule_step; rotate_left
  -- non funziona perchè io voglio fare uno step nel futuro non mi interessa lo stato da qui sonon veniuto maa non poosso
