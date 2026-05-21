import Star.Commute.ARS

open Star1

namespace the_theorem_ind

set_option quotPrecheck false

variable {A B E}

variable (flush :  A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)
variable (similarity : A -> A -> Prop)

infix:50 " ~ " => similarity

axiom similarity_symm :
  ∀ {a b : A}, a ~ b → b ~ a


variable (φ : A -> B -> Prop)

def φ_flush : A → B → Prop := fun (i : A) (s : B) => φ i s ∧ (∀ (i' : A), ¬ rule i i')

def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'

theorem weakly_normalising_implication (i : A) : has_nf rule i -> ∃ i', trans_refl rule i i' ∧  (∀ (i'' : A), ¬rule i' i'') := by
        unfold has_nf at *
        intro hf
        unfold is_nf at *
        grind

def indistinguishability1 (i : A) (i₁ : A) : Prop := ∀ (i' : A) e, method_i i e i' -> ∃ i₁', method_i i₁ e i₁'


def has_diamond_property1 (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d d₁, α c d ∧ α b d₁ ∧ indistinguishability1 method_i d d₁


def has_diamond_property_similarity (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d d₁, α c d ∧ α b d₁ ∧ d ~ d₁

def preserve_flushing := ∀ i s i', flush i s -> i ~ i' -> flush i' s

def similarity_step := ∀ i i' i₁ , i ~ i' -> rule i i₁ -> ∃ i₁' , rule i' i₁' ∧ i₁ ~ i₁'

/-
Helper: if i ~ i' and trans_refl rule i j, then there exists j' with trans_refl rule i' j' and j ~ j'.
-/
lemma similarity_trans_refl
    (hss : similarity_step rule similarity)
    {i i' j : A} (hsim : i ~ i') (htr : trans_refl rule i j) :
    ∃ j', trans_refl rule i' j' ∧ j ~ j' := by
  induction htr generalizing i' with
  | step h _ ih =>
    obtain ⟨j', hj', hj''⟩ := hss _ _ _ hsim h
    obtain ⟨j'', hj1, hj2⟩ := ih hj''
    exact ⟨j'', trans_refl.step hj' hj1, hj2⟩
  | refl => exact ⟨i', trans_refl.refl, hsim⟩



theorem phi_preserve_similarity :
  preserve_flushing flush similarity ->
  similarity_step rule similarity ->
  ∀ i s i', φ₀ flush rule i s -> i ~ i' -> φ₀ flush rule i' s := by
  intro h₀ h₁ i s i' hi hi'
  induction hi generalizing i' with
  | base i s hfl => exact φ₀.base i' s (h₀ i s i' hfl hi')
  | rule_step i i'' s _ htr ih =>
    obtain ⟨j', hj₁, hj₂⟩ := similarity_trans_refl rule similarity h₁ hi' htr
    exact φ₀.rule_step _ _ _ (ih _ hj₂) hj₁


theorem enoght_internal (i : A) (s : B) :
    preserve_flushing flush similarity ->
    similarity_step rule similarity ->
    (∀ i i' s, relation_flush flush i i' s rule ) ->
    φ₀ flush rule i s -> ∀ i', trans_refl rule i i' -> has_diamond_property_similarity similarity (trans_refl rule) -> φ₀ flush rule i' s := by
      intro hp hs he hφ₀ i' hstep hconf
      have h := hφ₀
      induction hφ₀ generalizing i'
      . rename_i i s' h3
        constructor
        unfold relation_flush at *
        grind
      . clear i s
        rename_i i i'' s h1 h2 h4
        unfold has_diamond_property_similarity at *
        specialize @hconf i i'' i' hstep h2
        cases hconf; rename_i d H
        cases H; rename_i d₁ H
        rcases H with ⟨H1, H2, H3⟩
        specialize h4 d₁ H2
        unfold phi_preserve_similarity at *
        specialize h4 h1
        have H3' := @similarity_symm _ similarity d d₁
        specialize H3' H3
        have hp :=  phi_preserve_similarity flush rule similarity hp hs
        specialize hp _ _ _ h4 H3'
        apply φ₀.rule_step _ d _ <;> try assumption



theorem enough_star (i i' : A) (s : B) (l : List E) :
  preserve_flushing flush similarity ->
  similarity_step rule similarity ->
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
  ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
  has_diamond_property_similarity similarity (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  φ₀ flush rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ₀ flush rule i' s':= by
    intro hp hs hm hm' hm'' HH HHH h1 h2
    revert h1 s
    induction h2 <;> intro s
    . intro h3
      exact ⟨ s, star.refl s, h3⟩
    . rename_i l' i_1 i_2  h9 h7 hi
      intro h11
      have h10 := hi _ h11
      cases h10
      rename_i s_1 h1
      let ⟨H1, H2⟩ := h1
      have h2 :=  enoght_internal _ _ _ _ _ hp hs hm H2 _ h7 HH
      constructor; rotate_left
      . exact s_1
      . constructor <;> assumption
    . clear i'
      rename_i l' i' i'' e _ h2 h3
      intro h4
      have h5 := h3 _ h4
      cases h5
      rename_i s' h6
      have h7 := enoght_external _ _ _ method_s  _ _ hm' hm'' h6.right (by assumption) _ _ h2
      cases h7
      rename_i s2 h8
      cases h8
      rename_i h8 h8'
      rcases h6 with ⟨ h6, h6'⟩
      constructor; rotate_left
      . exact s2
      . constructor
        . apply star.step
          . exact h6
          . assumption
        . assumption
