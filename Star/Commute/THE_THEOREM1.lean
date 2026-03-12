import Star.Commute.ARS

open Star

namespace the_theorem1

variable {A B E}

variable (flush :  A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)


def method_deterministic := ∀ s s' s'' e,  method_s s e s' ->  method_s s e s'' -> s' = s''

variable (φ : A -> B -> Prop)

def φ_flush : A → B → Prop := fun (i : A) (s : B) => φ i s ∧ (∀ (i' : A), ¬ rule i i')

def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'



theorem completeness:
  method_deterministic method_s ->
  strongly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
    intro hm h1 h2 h3 h4
    unfold refinament at *
    intro i i' s l
    apply enough_star <;> try assumption
    . unfold relation_flush
      intro _ _ _ h5 h6
      unfold φ_flush at *
      cases h6
      . rename_i i1 _ _
        rcases h5 with ⟨ h5, h5'⟩; specialize h5' i1
        grind
      . assumption
    . unfold relation_flush_method
      intro ii ii' _ s' e h5 h6 h7
      unfold φ_flush at *
      rcases h5 with ⟨ h5, h5'⟩
      unfold strongly_normalising at *
      specialize h1 ii'
      have H : strongly_normalising' rule ii' -> ∃ i'', trans_refl rule ii' i'' ∧  (∀ (i''' : A), ¬rule i'' i''') := by
        intro H
        clear hm h2 h3 h4 h6 h7 h1
        induction H
        rename_i i1 h1 h2
        by_cases hh :  ∃ (b : A), rule i1 b
        . rcases hh with ⟨ i2, hh⟩
          specialize h2 _ hh
          rcases h2 with ⟨ i3, h2⟩
          constructor; rotate_left
          . exact i3
          . constructor
            . rcases h2 with ⟨ h2, h2'⟩
              constructor
              . assumption
              . assumption
            . grind
        . simp at hh
          constructor; rotate_left
          . exact i1
          . constructor
            . apply trans_refl.refl
            . simp_all
      specialize H h1
      rcases H with ⟨ i'', H⟩
      constructor; rotate_left
      . exact i''
      . constructor
        . grind
        . constructor
          . rcases H with ⟨ H, H'⟩
            specialize h4 _ i'' _ [e] h5
            have H : star_extend rule method_i ii [e] i'' := by
              apply star_extend.step_int; rotate_right 2
              . assumption
              . apply star_extend.step_ext; rotate_right 2
                . assumption
                . apply star_extend.refl
            specialize h4 H
            rcases h4 with ⟨ s'', h4, h4'⟩
            cases h4; rename_i s3 h4 h44
            cases h4
            unfold method_deterministic at hm
            grind
          . grind
    . unfold relation_method
      intro i1 i2 s1 e h5 h6
      unfold φ_flush at *
      rcases h5 with ⟨ h5, h5'⟩
      specialize h4 _ i2 _ [e] h5
      have H : star_extend rule method_i i1 [e] i2 := by
        apply star_extend.step_ext; rotate_right
        . exact i1
        . apply star_extend.refl
        . assumption
      specialize h4 H
      rcases h4 with ⟨ s'', h4, h4'⟩
      cases h4; rename_i H _; cases H
      grind

#print axioms completeness



end the_theorem1
