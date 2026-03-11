import Star.Commute.ARS

open Star

namespace the_theorem

variable {B C E}
variable [Inhabited C]

abbrev A := B × C

variable (flush : @A B C -> B -> Prop)
variable (rule : Rule (@A B C))
variable (method_i : Method (@A B C) E)
variable (method_s : Method B E)


def method_deterministic := ∀ s s' s'' e,  method_s s e s' ->  method_s s e s'' -> s' = s''

variable (φ : @A B C -> B -> Prop)

def φ_flush : @A B C → B → Prop := fun (a : @A B C) (b : B) => φ a b ∧ a.2 = default

def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'


def refinament_inductive :=
  ∀ i i' s l, φ₀ (φ_flush φ) rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ₀ (φ_flush φ) rule i' s'



theorem completeness (i i' : A) (s : B) (l : List E) :
  (∀ (i i' : A), i = (i.1, default) -> ¬ trans_refl rule i i' ) ->
  (∀ (i : A), ∃ (i' : A), trans_refl rule i i' ∧ i' = (i'.1, default)) ->
  method_deterministic method_s ->
  strongly_normalising (trans_refl rule) ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament_inductive  rule method_i method_s (φ_flush φ)
  ∧
  ((φ_flush φ) i s -> trans_refl rule i i' -> (φ_flush φ) i' s)
  ∧
  (∀ e (s' : B), (φ_flush φ) i s -> method_i i e i' -> method_s s e s' -> ∃ i'', trans_refl rule i' i'' ∧ (φ_flush φ) i'' s')
  ∧
  (∀ e (s' : B), (φ_flush φ) i s -> method_i i e i' -> ∃ s', method_s s e s') := by
    intro hs hd hm h1 h2 h3 h4
    unfold refinament_inductive
    unfold refinament at *
    constructor
    . intro i i' s l
      apply enough_star <;> assumption
    . constructor
      . intro h5 h6
        unfold φ_flush at *
        rcases h5 with ⟨ h5, h5'⟩
        cases i
        simp at h5'
        subst h5'
        rename_i i.fst
        specialize hs (i.fst, default) i'; simp_all
      . constructor
        . intro e s' h5 h6 h7
          have H4 := h4
          unfold φ_flush at *
          rcases h5 with ⟨ h5, h5'⟩
          cases i
          simp at h5'
          subst h5'
          rename_i i.fst
          specialize hd i'
          rcases hd with ⟨i'', hd, hd'⟩
          specialize h4 _ i' _ [e] h5
          have H : star_extend rule method_i (i.fst, default) [e] i' := by
            apply star_extend.step_ext; rotate_right
            . exact (i.fst, default)
            . constructor
            . assumption
          specialize h4 H
          cases h4; rename_i s'' H
          rcases H with ⟨ H, H'⟩
          cases H; rename_i s1 H1 H2
          cases H1
          constructor; rotate_left; exact i''
          specialize H4 i' i'' _ [] H'
          have h8 : star_extend rule method_i i' [] i'' := by
            apply star_extend.step_int; rotate_right
            . exact i'
            . constructor
            . assumption
          specialize H4 h8
          rcases H4 with ⟨ s''', h9, h10 ⟩
          cases h9
          have hh : s' = s'' := by unfold method_deterministic at *; grind
          grind
        . intro e s' h5 h6
          unfold φ_flush at *
          rcases h5 with ⟨ h5, h5'⟩
          cases i
          simp at h5'
          subst h5'
          rename_i i.fst
          specialize h4 _ i' _ [e] h5
          have H : star_extend rule method_i (i.fst, default) [e] i' := by
            apply star_extend.step_ext; rotate_right
            . exact (i.fst, default)
            . constructor
            . assumption
          specialize h4 H
          rcases h4 with ⟨ s', h4, h4'⟩
          cases h4
          rename_i h4 _ ; cases h4
          constructor
          . assumption
#print axioms completeness


end the_theorem
