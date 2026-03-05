/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Star

@[simp] abbrev Rule (A : Type _) := A → A → Prop
@[simp] abbrev Method (A : Type _) (E : Type _) := A → E → A → Prop -- B is the equeu element

structure ARS (I : Type _) where
  A : Type _
  rules : I → Rule A

inductive trans {A} (rule : Rule A) : Rule A where
| step {a b c} : trans rule a b → rule b c → trans rule a c
| refl {a b} : rule a b → trans rule a b

def refl {A} (rule : Rule A) (s e : A) : Prop :=
  rule s e ∨ s = e


-- this is the star and then the user give me A as a union of all possibile rule R1, R2, R3 ecc...
inductive trans_refl {A} (rule : Rule A) : Rule A where
| step {a b c} : rule a b → trans_refl rule b c → trans_refl rule a c
| refl {a} : trans_refl rule a a

inductive trans_refl2 {A} (rule : Rule A) : Rule A where
| step {a b c} : rule b c → trans_refl2 rule a b → trans_refl2 rule a c
| refl {a} : trans_refl2 rule a a



inductive counted_trans_refl {A} (rule : Rule A) : A → A → Nat → Prop where
| step {a b c n} : rule a b → counted_trans_refl rule b c n → counted_trans_refl rule a c (n+1)
| refl {a} : counted_trans_refl rule a a 0

def ARS.red_seq {I} (ars : ARS I) (i : I) : Rule ars.A := trans_refl (ars.rules i)

inductive ARS.indexed_red_seq {I} (ars : ARS I) : List I → Rule ars.A where
| step {i is a b c} : ars.rules i a b → ars.indexed_red_seq is b c → ars.indexed_red_seq (i :: is) a c
| refl {a} : ars.indexed_red_seq [] a a

def union {A} (α β : Rule A) (s e : A) : Prop := α s e ∨ β s e
def inv {A} (α : Rule A) (s e : A) : Prop := α e s
def symm {A} (α : Rule A) : Rule A := union α (inv α)
def compose {A} (α β : Rule A) (s e : A) : Prop := ∃ s', α s s' ∧ β s' e



def commutes_weakly {A} (α β : Rule A) :=
  ∀ {a b c : A}, β a c → α a b → ∃ d, trans_refl α c d ∧ trans_refl β b d

def commutes {A} (α β : Rule A) := commutes_weakly (trans_refl α) (trans_refl β)

def weakly_confluent {A} (α : Rule A) := commutes_weakly α α

def is_subcommutative {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, refl α c d ∧ refl α b d

def has_diamond_property {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, α c d ∧ α b d

def is_confluent {A} (α : Rule A) := commutes α α

def is_nf {A} (α : Rule A) (a : A) : Prop :=
  ∀ b, ¬ α a b

def has_nf {A} (α : Rule A) (b : A) : Prop :=
  ∃ a, trans_refl α b a ∧ is_nf α a

def weakly_normalising {A} (α : Rule A) := ∀ a, has_nf α a

inductive strongly_normalising' {A} (α : Rule A) : A → Prop where
| step {a} : (∀ b, α a b → strongly_normalising' α b) → strongly_normalising' α a

def strongly_normalising {A} (α : Rule A) := ∀ a, strongly_normalising' α a

#print Acc

inductive well_founded' {A} (α : Rule A) : A → Prop where
| step {b} : (∀ a, α a b → well_founded' α a) → well_founded' α b

def well_founded {A} (α : Rule A) := ∀ a, well_founded' α a


def is_inductive {A} (α : Rule A) :=
  ∀ a b n, counted_trans_refl α a b n → ∃ a', trans_refl α b a'

def is_increasing {A} (sz : A → Nat) (α : Rule A) :=
  ∀ a b, α a b → sz a < sz b

namespace Example

inductive xor : Bool → Bool → Bool → Prop where
| t_rule {b} : xor true b (¬ b)
| f_rule {b} : xor false b b

def ars : ARS Bool where
  A := Bool
  rules := xor

example : ARS.indexed_red_seq ars [true, false, true] true true := by repeat constructor

end Example

/-
# Newmans proofs
-/

@[simp]
theorem double_application_term {A} (α: Rule A) :
  ∀ {a b: A},  α a b -> trans_refl α a b := by
  intro a b h
  constructor
  exact h
  apply trans_refl.refl




@[simp]
theorem double_application_term' {A} (α: Rule A) :
  ∀ {a b: A},  α a b -> trans α a b := by grind[trans.refl]


@[simp]
theorem double_application_term1 {A} (α: Rule A) :
  ∀ {a b: A},  trans_refl α a b -> trans_refl (trans_refl α) a b := by
  intro a b h
  induction h
  case step a b c h1 h2 ih =>
    have HH := double_application_term _ h1
    apply trans_refl.step HH ih
  case refl a =>
    apply trans_refl.refl

@[simp]
theorem double_application_term2 {A} (α: Rule A) :
  ∀ {a b: A},  trans_refl (trans_refl α) a b  -> trans_refl α a b := by
  intro a b h
  induction h
  . clear a b
    rename_i a b c h1 h2 h3
    clear h2
    induction h1
    . clear a b
      rename_i a b d e h1 h2
      specialize h2 h3
      constructor <;> assumption
    . assumption
  . apply trans_refl.refl




-- theorem confleunt {A} (α : Rule A) : has_diamond_property α → is_confluent α := by
--   intro h
--   unfold is_confluent commutes commutes_weakly
--   intro a b c t1 t2
--   unfold has_diamond_property at h
--   revert t2 b
--   induction t1
--   . rename_i a' b' c' h1 h2 ih
--     intro b t2
--     clear a c
--     cases h' : t2
--     . rename_i z h4 h5
--       specialize h h1 h4
--       cases h; rename_i d' h
--       rcases h with ⟨H1, H2⟩
--       have H1' := trans_refl.step H1 trans_refl.refl
--       specialize ih H1'
--       cases ih; rename_i d'' h'
--       rcases h' with ⟨H3, H4⟩
--       have H2' : trans_refl α z d'' := by admit
--       clear H4 H3 H1' H2 H1 h2 h1 h' h4
--       induction t2
--       . rename_i z' b'' c'' h3 h4 ih'
--         specialize ih' h5
--         assumption
--       . admit
--     . admit
--   . admit


theorem termination {A} (α : Rule A) : strongly_normalising α → well_founded (inv α) := by
  intro h a
  specialize h a
  induction h
  case step a h1 ih =>
    apply well_founded'.step
    intro b h2
    specialize ih b h2
    assumption




theorem termination_steps' {A} (α : Rule A) : well_founded α -> well_founded (trans α) := by
  intro h a
  apply well_founded'.step
  specialize h a
  intro b h2
  induction h generalizing b
  . rename_i xa xb xc
    cases h2
    . grind
    . constructor
      grind


theorem Newmans_lemma {A} (α : Rule A) :
  strongly_normalising α →  has_diamond_property α → is_confluent α := by
  intro h
  have h1 := termination α h
  have h2 := termination_steps' (inv α) h1
  clear h1
  intro h1
  unfold well_founded at h2
  unfold is_confluent commutes commutes_weakly
  intro a --b c t1 t2
  specialize h2 a
  induction h2
  rename_i a h3 ih; rename_i a'; clear a'
  apply ih
  apply trans.refl
  unfold inv
  unfold has_diamond_property at h1
  specialize @h1 a a a
  admit

/-
# Newmans  thorems implies refinment
-/


/-
# Define i and s and φ
-/



--how the state of the implemenattion and spec are related when they are both in a flush state v
variable {A B E}
variable (flush : A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)


def indistinguishability (i : A) (s : B) : Prop := ∀ (i' : A) e, method_i i e i' -> ∃ s', method_s s e s'


inductive φ : A -> B -> Prop where
| base : ∀ (i : A) (s : B),
          flush i s ->
          φ i s
| rule_step : ∀ (i i' : A) (s : B),
              φ i' s ->
              trans_refl rule i i' ->
              φ i s
-- | method_step : ∀ (i i' : A) (s s' : B) (method_i : Method A) (method_s : Method B) n, --maybe add the forall trick
--               φ i' s' ->
--               method_i i n i' ->
--               method_s s n s' ->
--               φ i s


theorem relation_flush : ∀ (i i' : A) (s : B) (rule : Rule A), flush i s -> trans_refl rule i i' -> flush i' s := by admit
theorem relation_flush_method : ∀ (i i' : A) (s s' : B) e, flush i s -> method_i i e i' -> method_s s e s' ->
                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'  := by admit
theorem relation_method : ∀ (i i' : A) (s : B) e, flush i s -> method_i i e i' -> ∃ s', method_s s e s' := by admit


theorem enoght_internal (i : A) (s : B) :
    φ flush rule i s -> ∀ i', trans_refl rule i i' -> strongly_normalising (trans_refl rule) -> has_diamond_property (trans_refl rule) -> φ flush rule i' s := by
      intro hφ i' hstep hs hconf
      induction hφ generalizing i'
      . rename_i i s' h3
        constructor
        apply relation_flush <;> assumption
      . clear i s
        rename_i i i'' s h1 h2 h4
        have H := @Newmans_lemma A (trans_refl rule) hs hconf
        unfold is_confluent at H
        unfold commutes at H
        unfold commutes_weakly at H
        have h2' := double_application_term1 _ h2
        have hstep' := double_application_term1 _ hstep
        specialize @H i i'' i' hstep' h2'
        cases H; rename_i d H; rcases H with ⟨H1, H2⟩
        have H2' := double_application_term2 _ (double_application_term2 _ H2)
        have H1' := double_application_term2 _ (double_application_term2 _ H1)
        specialize h4 d H2'
        apply φ.rule_step _ d _ <;> try assumption


def commutes_weakly_methods_i (α : Method A E) :=
  ∀ {a b c : A} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_methods_s (α : Method B E) :=
  ∀ {a b c : B} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_method_rule (α : Method A E) ( β : Rule A) :=
  ∀ {a b c : A} { e : E}, trans_refl β a b → α a e c → ∃ d, α b e d ∧ trans_refl β c d


theorem indistinguisability_preservation (i : A) (s : B) :
    φ flush rule i s -> commutes_weakly_method_rule method_i rule -> @indistinguishability  _ _ E method_i method_s i s := by
      intro h1 h2
      induction h1
      . clear i s
        rename_i i s h3
        unfold indistinguishability
        intro i' e h4
        apply relation_method <;> assumption
      . clear i s
        rename_i i i' s h3 h4 h5
        unfold indistinguishability at *
        intro i'' e h6
        unfold commutes_weakly_method_rule at *
        specialize h2 h4 h6
        cases h2; rename_i d h2; cases h2; rename_i h2 h2'
        apply h5 <;> assumption



theorem enoght_external (i : A) (s : B) :
    φ flush rule i s ->
    commutes_weakly_method_rule method_i rule ->
    ∀ i' e, method_i i e i' ->
    ∃ (s' : B), method_s s e s' ∧ φ flush rule i' s' := by
      intro hφ h1 i' e h4
      have hi := @indistinguisability_preservation _ _ E _ _ method_i method_s _ _ hφ h1
      induction hφ generalizing i'
      . clear i s
        rename_i i s h5
        unfold indistinguishability at *
        specialize hi i' e h4
        cases hi; rename_i s' hi
        constructor; rotate_left
        . exact s'
        . constructor
          . assumption
          . have H := @relation_flush_method A B E flush rule method_i method_s i i' s s' e h5 h4 hi
            cases H; rename_i i'' H; cases H; rename_i H1 H2
            apply φ.rule_step _ i''
            . constructor; assumption
            . assumption
      . clear i s
        rename_i i i'' s h5 h6 h7
        unfold commutes_weakly_method_rule at *
        specialize @h1 i i'' i' e h6 h4
        cases h1; rename_i d h1; cases h1; rename_i h1 h1'
        have H' := @indistinguisability_preservation _ _ E _ _ method_i method_s _ _ h5
        specialize h7 d h1 (by sorry)
        cases h7; rename_i s' h7; rcases h7 with ⟨ h7, h7'⟩
        constructor; rotate_left; exact s'
        constructor
        . assumption
        . apply φ.rule_step _ d _ <;> try assumption


inductive star : A -> List E -> A -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1 s2 s3 l e1, star s1 l s2 -> method_i s2 e1 s3 -> star s1 (e1 :: l) s3


inductive star_extend : A -> List E -> A -> Prop where
  | refl : ∀ s, star_extend s [] s
  | step_int : ∀ s l s' s'' , star_extend s l s' ->  rule s' s'' -> star_extend s l s''
  | step_ext : ∀ s l s' s'' e, star_extend s l s' -> method_i s' e s'' -> star_extend s (e :: l) s''



theorem enough_star (i i' : A) (s : B) (l : List E) :
  strongly_normalising (trans_refl rule) ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  φ flush rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ flush rule i' s':= by
    intro H HH HHH h1 h2
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
      have h7' := double_application_term _ h7
      have h2 :=  enoght_internal _ _ _ _ H2 _ h7' H HH
      constructor; rotate_left
      . exact s_1
      . constructor <;> assumption
    . clear i'
      rename_i l' i' i'' e _ h2 h3
      intro h4
      have h5 := h3 _ h4
      cases h5
      rename_i s' h6
      have h7 := enoght_external _ _ _ method_s  _ _ h6.right (by assumption) _ _ h2
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


end Star
