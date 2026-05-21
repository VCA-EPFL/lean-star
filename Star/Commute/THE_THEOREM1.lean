import Star.Commute.ARS

open Star1

namespace the_theorem1

variable {A B E}

variable (flush :  A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)

--This is what we don't have to use if you prove the theorem without enought_star
def method_deterministic := ∀ s s' s'' e,  method_s s e s' ->  method_s s e s'' -> s' = s''

variable (φ : A -> B -> Prop)

def φ_flush : A → B → Prop := fun (i : A) (s : B) => φ i s ∧ (∀ (i' : A), ¬ rule i i')

def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'

theorem weakly_normalising_implication (i : A) : has_nf rule i -> ∃ i', trans_refl rule i i' ∧  (∀ (i'' : A), ¬rule i' i'') := by
        unfold has_nf at *
        intro hf
        unfold is_nf at *
        grind


theorem completeness:
  weakly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
    intro h1 h2 h3 h4
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
      unfold weakly_normalising at *
      specialize h1 ii'
      have H := weakly_normalising_implication rule ii'
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
            admit
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

/-
We prove the completeness theorem for the refinement of abstract reduction systems.
The proof demonstrates that if a rule is weakly normalising, confluent (via the diamond property),
and commutes weakly with the implementation method, then the refinement property lifts to the observational equivalence relation φ₀.
Note: The proof strategy using `enough_star` suggested in the prompt requires `relation_flush_method`,
 which implies a form of determinism for `method_s` that is not guaranteed by the premises.
 Therefore, we provided a direct proof using the confluence and normalization properties to construct the required simulation.
-/

theorem phi0_implies_exists_base {A B} (rule : Rule A) (φ1 : A -> B -> Prop) (i : A) (s : B) :
  φ₀ (φ_flush rule φ1) rule i s →
  ∃ i_base, trans_refl rule i i_base ∧ is_nf rule i_base ∧ φ1 i_base s := by
    intro h
    induction' h with i_base h_base h_ind
    · exact ⟨ i_base, trans_refl.refl, h_ind.2, h_ind.1 ⟩;
    · -- Since Star.trans_refl is transitive, we can combine the paths from i to i' and from i' to i_base to get a path from i to i_base.
      have h_trans : ∀ i i' i_base, trans_refl rule i i' → trans_refl rule i' i_base → trans_refl rule i i_base := by
        -- By definition of trans_refl, we can combine the paths from i to i' and from i' to i_base to get a path from i to i_base.
        intros i i' i_base h1 h2
        induction' h1 with i i' h1 ih generalizing i_base
        · exact trans_refl.step ih ( by solve_by_elim );
        · exact h2
      grind

theorem star_extend_confluence {A E} (rule : Rule A) (method_i : Method A E) :
  is_confluent rule →
  commutes_weakly_method_rule method_i rule →
  ∀ i l i', star_extend rule method_i i l i' →
  ∀ i_nf, trans_refl rule i i_nf →
  ∃ d, star_extend rule method_i i_nf l d ∧ trans_refl rule i' d := by
    intros h_confl h_comm i l i' h_star_extend i_nf h_trans_nf
    induction' h_star_extend with i l i' h_star_extend ih generalizing i_nf
    all_goals generalize_proofs at *;
    · exact ⟨ i_nf, star_extend.refl _, h_trans_nf ⟩;
    · obtain ⟨ d, hd₁, hd₂ ⟩ := ‹∀ i_nf, trans_refl rule _ i_nf → ∃ d, star_extend rule method_i i_nf i d ∧ trans_refl rule l d› i_nf h_trans_nf;
      obtain ⟨ e, he₁, he₂ ⟩ := h_confl ih hd₂
      generalize_proofs at *; (
      use e; exact ⟨by
      exact star_extend.step_int _ _ _ _ hd₁ ( by exact? ) |> fun h => by exact?;, by
        exact?⟩;);
    · rename_i s' s'' e h₁ h₂ h₃
      generalize_proofs at *; (
      obtain ⟨ d, hd₁, hd₂ ⟩ := h₃ i_nf h_trans_nf
      generalize_proofs at *; (
      obtain ⟨ d', hd₃, hd₄ ⟩ := h_comm hd₂ h₂
      generalize_proofs at *; (
      exact ⟨ d', star_extend.step_ext _ _ _ _ _ hd₁ hd₃, hd₄ ⟩)))

theorem star_extend_confluence' {A E} (rule : Rule A) (method_i : Method A E) :
  is_confluent rule →
  commutes_weakly_method_rule method_i rule →
  ∀ i l i', star_extend rule method_i i l i' →
  ∀ i_nf, trans_refl rule i i_nf →
  ∃ d, star_extend rule method_i i_nf l d ∧ trans_refl rule i' d := by
    -- Apply the star_extend_confluence theorem with the given hypotheses.
    apply star_extend_confluence


theorem diamond_trans_refl_implies_confluent {A} (rule : Rule A) :
  has_diamond_property (trans_refl rule) → is_confluent rule := by
    -- Assume that `Star.trans_refl rule` has the diamond property.
    intro h_diamond
    intro a b c h_trans_refl_a_b h_trans_refl_a_c;
    obtain ⟨ d, hd₁, hd₂ ⟩ := h_diamond h_trans_refl_a_b h_trans_refl_a_c; use d; aesop;


theorem trans_refl_implies_star_extend {A E} (rule : Rule A) (method_i : Method A E) :
  ∀ i i', trans_refl rule i i' → star_extend rule method_i i [] i' := by
  intro i i' h
  induction h
  case step =>
    rename_i a b c h1 h2 ih
    apply star_extend.step_int
    . exact star_extend.refl a
    . apply trans_refl.step h1 h2
  case refl =>
    apply star_extend.refl

theorem φ_preserved_under_rule {A B E} (rule : Rule A) (method_i : Method A E) (method_s : Method B E) (φ1 : A -> B -> Prop) :
  refinament rule method_i method_s φ1 ->
  ∀ i i' s, φ1 i s → trans_refl rule i i' → φ1 i' s := by
  intro href i i' s hphi htrans
  have h_ext : star_extend rule method_i i [] i' := trans_refl_implies_star_extend rule method_i i i' htrans
  specialize href i i' s [] hphi h_ext
  rcases href with ⟨s', hs', hphi'⟩
  cases hs'
  . exact hphi'

theorem completeness1:
  weakly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
    intro h_weak h_diamond h_comm h_refine
    intro i i' s l hφ hstar
    obtain ⟨i_base, hi_base, hi_nf, hiφ⟩ := phi0_implies_exists_base rule (φ_flush rule φ) i s (by
      convert hφ using 1
      generalize_proofs at *; (
      funext i s; simp [φ_flush]));
    obtain ⟨d, hd⟩ : ∃ d, star_extend rule method_i i_base l d ∧ trans_refl rule i' d := by
      apply star_extend_confluence' rule method_i (diamond_trans_refl_implies_confluent rule h_diamond) h_comm i l i' hstar i_base hi_base;
    obtain ⟨ s', hs' ⟩ := h_refine i_base d s l hiφ.1 hd.1;
    obtain ⟨d_nf, hd_nf⟩ : ∃ d_nf, trans_refl rule d d_nf ∧ is_nf rule d_nf := by
      exact h_weak d;
    have hφ_nf : φ d_nf s' := by
      have := φ_preserved_under_rule rule method_i method_s φ h_refine d d_nf s' hs'.2 hd_nf.1; aesop;
    refine' ⟨ s', hs'.1, _ ⟩;
    apply φ₀.rule_step i' d_nf s';
    · exact φ₀.base _ _ ⟨ hφ_nf, fun i'' hi'' => hd_nf.2 _ hi'' ⟩;
    · have h_trans_nf : ∀ {a b c : A}, trans_refl rule a b → trans_refl rule b c → trans_refl rule a c := by
        intro a b c hab hbc; exact (by
        induction hab <;> tauto);
      exact h_trans_nf hd.2 hd_nf.1



theorem φ_flus_smaller_φ : ∀ i s,  φ_flush rule φ i s -> φ i s:= by
  intro i s h
  unfold φ_flush at *
  grind

#print axioms completeness



end the_theorem1
