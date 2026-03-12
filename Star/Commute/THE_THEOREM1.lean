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



theorem completeness (i i' : A) (s : B):
  method_deterministic method_s ->
  strongly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule)
  ∧
  ((φ_flush rule φ) i s -> trans_refl rule i i' -> (φ_flush rule φ) i' s)
  ∧
  (∀ e (s' : B), (φ_flush rule φ) i s -> method_i i e i' -> method_s s e s' -> ∃ i'', trans_refl rule i' i'' ∧ (φ_flush rule φ) i'' s')
  ∧
  (∀ e, (φ_flush rule φ) i s -> method_i i e i' -> ∃ s', method_s s e s') := by
    intro hm h1 h2 h3 h4
    unfold refinament at *
    constructor
    . intro i i' s l
      apply enough_star <;> assumption
    . constructor
      . intro h5 h6
        unfold φ_flush at *
        cases h6
        . rename_i i1 _ _
          rcases h5 with ⟨ h5, h5'⟩; specialize h5' i1
          grind
        . assumption
      . constructor
        . intro e s' h5 h6 h7
          unfold φ_flush at *
          rcases h5 with ⟨ h5, h5'⟩
          unfold strongly_normalising at *
          specialize h1 i'
          have H : strongly_normalising' rule i' -> ∃ i'', trans_refl rule i' i'' ∧  (∀ (i''' : A), ¬rule i'' i''') := by
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
                have H : star_extend rule method_i i [e] i'' := by
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
        . intro e h5 h6
          unfold φ_flush at *
          rcases h5 with ⟨ h5, h5'⟩
          specialize h4 _ i' _ [e] h5
          have H : star_extend rule method_i i [e] i' := by
            apply star_extend.step_ext; rotate_right
            . exact i
            . apply star_extend.refl
            .  assumption
          specialize h4 H
          rcases h4 with ⟨ s'', h4, h4'⟩
          cases h4; rename_i H _; cases H
          grind




end the_theorem1
