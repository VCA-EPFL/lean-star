/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

namespace ReachingStar

@[simp] abbrev Rule (A : Type _) := A → A → Prop
@[simp] abbrev Method (A : Type _) (E : Type _) := A → E → A → Prop -- B is the equeu element

structure ARS.{u, v} (I : Type u) where
  A : Type v
  rules : I → Rule A

inductive trans {A} (rule : Rule A) : Rule A where
| step {a b c} : trans rule a b → rule b c → trans rule a c
| refl {a b} : rule a b → trans rule a b

theorem trans_equiv {r} :
  trans r a b ↔ Relation.TransGen r a b := by
  constructor
  · intro h
    induction h with
    | refl => constructor; assumption
    | step ha hb ih => trans; assumption; constructor; assumption
  · intro h
    induction h with
    | single => apply trans.refl; assumption
    | tail ha hb ih => constructor; assumption; assumption

def refl {A} (rule : Rule A) (s e : A) : Prop :=
  rule s e ∨ s = e

theorem refl_equiv {r} :
  refl r a b ↔ Relation.ReflGen r a b := by
  constructor
  · intro h
    induction h with
    | inl => constructor; assumption
    | inr => subst a; rfl
  · intro h
    induction h with
    | refl => right; rfl
    | single => constructor; assumption

-- this is the star and then the user give me A as a union of all possibile rule R1, R2, R3 ecc...
inductive trans_refl {A} (rule : Rule A) : Rule A where
| step {a b c} : rule a b → trans_refl rule b c → trans_refl rule a c
| refl {a} : trans_refl rule a a

theorem trans_refl_equiv {r} :
  trans_refl r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | refl => constructor
    | step ha hb ih => trans; apply Relation.ReflTransGen.single; assumption; assumption
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => apply trans_refl.refl
    | head ha hb ih => constructor; assumption; assumption

inductive trans_refl2 {A} (rule : Rule A) : Rule A where
| step {a b c} : rule b c → trans_refl2 rule a b → trans_refl2 rule a c
| refl {a} : trans_refl2 rule a a

theorem trans_refl2_equiv {r} :
  trans_refl2 r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | refl => constructor
    | step ha hb ih => trans; assumption; apply Relation.ReflTransGen.single; assumption
  · intro h
    induction h with
    | refl => apply trans_refl2.refl
    | tail ha hb ih => constructor; assumption; assumption

theorem trans_refl_trans_refl2_equiv {r} : trans_refl2 r a b ↔ trans_refl r a b := by
  rw [trans_refl2_equiv,←trans_refl_equiv]

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

def commutes_weakly' {A} (α β : Rule A) :=
  ∀ {a b c : A}, β a c → α a b → ∃ d, Relation.ReflTransGen α c d ∧ Relation.ReflTransGen β b d

theorem commutes_weakly'_iff_commutes_weakly {A} (α β : Rule A) :
    commutes_weakly' α β ↔ commutes_weakly α β := by
  unfold commutes_weakly' commutes_weakly
  simp_rw [trans_refl_equiv]

def commutes {A} (α β : Rule A) := commutes_weakly (trans_refl α) (trans_refl β)

def weakly_confluent {A} (α : Rule A) := commutes_weakly α α

def is_subcommutative {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, refl α c d ∧ refl α b d

def has_diamond_property {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, α c d ∧ α b d

theorem has_diamond_property_reflTransGen_iff_trans_refl {A} (r : Rule A) :
    has_diamond_property (Relation.ReflTransGen r) ↔ has_diamond_property (trans_refl r) := by
  unfold has_diamond_property
  simp_rw [trans_refl_equiv]

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



inductive xor : Bool → Bool → Bool → Prop where
| t_rule {b} : xor true b (¬ b)
| f_rule {b} : xor false b b

def ars : ARS Bool where
  A := Bool
  rules := xor

example : ARS.indexed_red_seq ars [true, false, true] true true := by repeat constructor


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
  strongly_normalising α → has_diamond_property α → is_confluent α := by
    intro h1 h2 a b c h3 h4;
    -- By induction on the length of the transitions, we can apply the diamond property repeatedly to find a common d that both c and b transition to.
    induction' h3 with c' hc' ih generalizing b;
    · -- Since α has the diamond property, there exists a d such that hc' transitions to d and b transitions to d.
      obtain ⟨d, hd1, hd2⟩ : ∃ d, trans_refl α hc' d ∧ trans_refl α b d := by
        have h_diamond : ∀ {a b c : A}, α a b → trans_refl α a c → ∃ d, trans_refl α b d ∧ trans_refl α c d := by
          intro a b c hab hbc
          induction' hbc with c' hc' ih generalizing b;
          · -- By the diamond property, since α c' b and α c' hc', there exists a d such that α b d and α hc' d.
            obtain ⟨d, hd⟩ : ∃ d, α b d ∧ α hc' d := by
              exact h2 hab ‹_›;
            exact Exists.elim ( ‹∀ { b : A }, α hc' b → ∃ d, trans_refl α b d ∧ trans_refl α ih d› hd.2 ) fun e he => ⟨ e, trans_refl.step hd.1 he.1, he.2 ⟩;
          · exact ⟨ b, trans_refl.refl, trans_refl.step hab ( trans_refl.refl ) ⟩;
        exact h_diamond ‹_› ‹_›;
      rename_i h3 h4 h5;
      exact Exists.elim ( h5 hd1 ) fun e he => ⟨ e, he.1, trans_refl.step ( by tauto ) he.2 ⟩;
    · exact ⟨ b, by exact? , by exact? ⟩

theorem newmans_lemma {α : Rule A} :
  commutes_weakly' α α →
  strongly_normalising α →
  has_diamond_property (Relation.ReflTransGen α) := by
  intro hcomm hsn
  unfold has_diamond_property
  intro a b c hac hab
  have hmain :
      ∀ a, strongly_normalising' α a →
        ∀ {b c : A}, Relation.ReflTransGen α a c → Relation.ReflTransGen α a b →
          ∃ d, Relation.ReflTransGen α c d ∧ Relation.ReflTransGen α b d := by
    intro a ha
    induction ha with
    | step hstep ih =>
        intro b c hac hab
        rcases Relation.ReflTransGen.cases_head hac with hac_eq | ⟨c₁, hac₁, hc₁c⟩
        · subst c
          exact ⟨b, hab, Relation.ReflTransGen.refl⟩
        rcases Relation.ReflTransGen.cases_head hab with hab_eq | ⟨b₁, hab₁, hb₁b⟩
        · subst b
          exact ⟨c, Relation.ReflTransGen.refl, hac⟩
        obtain ⟨x, hc₁x, hb₁x⟩ := hcomm hac₁ hab₁
        obtain ⟨y, hxy, hby⟩ :=
          @ih b₁ hab₁ b x hb₁x hb₁b
        have hc₁y : Relation.ReflTransGen α c₁ y :=
          Relation.ReflTransGen.trans hc₁x hxy
        obtain ⟨z, hcz, hyz⟩ :=
          @ih c₁ hac₁ y c hc₁c hc₁y
        exact ⟨z, hcz, Relation.ReflTransGen.trans hby hyz⟩
  exact hmain a (hsn a) hac hab

/-
# Newmans  thorems implies refinment
-/


/-
# Define i and s and φ₀
-/



--how the state of the implemenattion and spec are related when they are both in a flush state v
variable {A B E}
variable (flush : A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)


def indistinguishability (i : A) (s : B) : Prop := ∀ (i' : A) e, method_i i e i' -> ∃ s', method_s s e s'


inductive φ₀ : A -> B -> Prop where
| base : ∀ (i : A) (s : B),
          flush i s ->
          φ₀ i s
| rule_step : ∀ (i i' : A) (s : B),
              φ₀ i' s ->
              trans_refl rule i i' ->
              φ₀ i s
-- | method_step : ∀ (i i' : A) (s s' : B) (method_i : Method A) (method_s : Method B) n, --maybe add the forall trick
--               φ₀ i' s' ->
--               method_i i n i' ->
--               method_s s n s' ->
--               φ₀ i s


def relation_flush (i i' : A) (s : B) (rule : Rule A) := flush i s -> trans_refl rule i i' -> flush i' s
def relation_flush' (i i' : A) (s : B) (rule : Rule A) := flush i s -> Relation.ReflTransGen rule i i' -> flush i' s
def relation_flush_method (i i' : A) (s s' : B) e := flush i s -> method_i i e i' -> method_s s e s' ->
                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'
def relation_flush_method' (i i' : A) (s s' : B) e := flush i s -> method_i i e i' -> method_s s e s' ->
                                ∃ i'', Relation.ReflTransGen rule i' i'' ∧ flush i'' s'
def relation_method (i i' : A) (s : B) e := flush i s -> method_i i e i' -> ∃ s', method_s s e s'

theorem relation_flush'_iff_relation_flush (i i' : A) (s : B) :
    relation_flush' flush i i' s rule ↔ relation_flush flush i i' s rule := by
  unfold relation_flush' relation_flush
  simp_rw [trans_refl_equiv]

theorem relation_flush_method'_iff_relation_flush_method (i i' : A) (s s' : B) (e : E) :
    relation_flush_method' flush rule method_i method_s i i' s s' e ↔
      relation_flush_method flush rule method_i method_s i i' s s' e := by
  unfold relation_flush_method' relation_flush_method
  simp_rw [trans_refl_equiv]

theorem enoght_internal (i : A) (s : B) :
    (∀ i i' s, relation_flush flush i i' s rule ) ->
    φ₀ flush rule i s -> ∀ i', trans_refl rule i i' -> has_diamond_property (trans_refl rule) -> φ₀ flush rule i' s := by
      intro he hφ₀ i' hstep hconf
      induction hφ₀ generalizing i'
      . rename_i i s' h3
        constructor
        unfold relation_flush at *
        grind
      . clear i s
        rename_i i i'' s h1 h2 h4
        unfold has_diamond_property at *
        specialize @hconf i i'' i' hstep h2
        cases hconf; rename_i d H; rcases H with ⟨H1, H2⟩
        specialize h4 d H2
        apply φ₀.rule_step _ d _ <;> try assumption



def commutes_weakly_methods_i (α : Method A E) :=
  ∀ {a b c : A} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_methods_s (α : Method B E) :=
  ∀ {a b c : B} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_method_rule (α : Method A E) ( β : Rule A) :=
  ∀ {a b c : A} { e : E}, trans_refl β a b → α a e c → ∃ d, α b e d ∧ trans_refl β c d

def commutes_weakly_method_rule' (α : Method A E) ( β : Rule A) :=
  ∀ {a b c : A} { e : E}, Relation.ReflTransGen β a b → α a e c →
    ∃ d, α b e d ∧ Relation.ReflTransGen β c d

theorem commutes_weakly_method_rule'_iff_commutes_weakly_method_rule
    (α : Method A E) (β : Rule A) :
    commutes_weakly_method_rule' α β ↔ commutes_weakly_method_rule α β := by
  unfold commutes_weakly_method_rule' commutes_weakly_method_rule
  simp_rw [trans_refl_equiv]

def commutes_strongly_method_rule (α : Method A E) ( β : Rule A) :=
  ∀ {a b c : A} { e : E}, β a b → α a e c → ∃ d, α b e d ∧ β c d

theorem commutes_strongly_method_rule_implies_weak (α : Method A E) (β : Rule A) :
  commutes_strongly_method_rule α β →
  commutes_weakly_method_rule α β := by
  dsimp [commutes_strongly_method_rule,commutes_weakly_method_rule]
  simp_rw [trans_refl_equiv]
  intro h1 a b c e href ha
  induction href using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl => exists c
  | head h2 h3 ih =>
    obtain ⟨d, hd1, hd2⟩ := h1 h2 ha
    obtain ⟨d1, hd1_1, hd1_2⟩ := ih hd1
    refine ⟨d1, ‹_›, ?_⟩
    trans; apply Relation.ReflTransGen.single; assumption; assumption


theorem indistinguisability_preservation (i : A) (s : B) :
    ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
    φ₀ flush rule i s -> commutes_weakly_method_rule method_i rule -> @indistinguishability  _ _ E method_i method_s i s := by
      intro hm h1 h2
      induction h1
      . clear i s
        rename_i i s h3
        unfold indistinguishability
        intro i' e h4
        unfold relation_method at hm
        grind
      . clear i s
        rename_i i i' s h3 h4 h5
        unfold indistinguishability at *
        intro i'' e h6
        unfold commutes_weakly_method_rule at *
        specialize h2 h4 h6
        cases h2; rename_i d h2; cases h2; rename_i h2 h2'
        apply h5 <;> assumption



theorem enoght_external (i : A) (s : B) :
    ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
    ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
    φ₀ flush rule i s ->
    commutes_weakly_method_rule method_i rule ->
    ∀ i' e, method_i i e i' ->
    ∃ (s' : B), method_s s e s' ∧ φ₀ flush rule i' s' := by
      intro hm hm' hφ₀ h1 i' e h4
      have hi := @indistinguisability_preservation _ _ E _ _ method_i method_s _ _ hm' hφ₀ h1
      induction hφ₀ generalizing i'
      . clear i s
        rename_i i s h5
        unfold indistinguishability at *
        specialize hi i' e h4
        cases hi; rename_i s' hi
        constructor; rotate_left
        . exact s'
        . constructor
          . assumption
          . unfold relation_flush_method at hm
            specialize hm i i' s s' e h5 h4 hi
            rcases hm with ⟨ i'', hm, Hm⟩
            apply φ₀.rule_step _ i''
            . constructor; assumption
            . assumption
      . clear i s
        rename_i i i'' s h5 h6 h7
        have hh {A E} := @h1 A E
        unfold commutes_weakly_method_rule at h1
        specialize @h1 i i'' i' e h6 h4
        cases h1; rename_i d h1; cases h1; rename_i h1 h1'
        have H' := @indistinguisability_preservation _ _ E _ _ method_i method_s _ _ hm' h5
        specialize h7 d h1 (by unfold commutes_weakly_method_rule at *; grind)
        cases h7; rename_i s' h7; rcases h7 with ⟨ h7, h7'⟩
        constructor; rotate_left; exact s'
        constructor
        . assumption
        . apply φ₀.rule_step _ d _ <;> try assumption


inductive star : A -> List E -> A -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1 s2 s3 l e1, star s1 l s2 -> method_i s2 e1 s3 -> star s1 (e1 :: l) s3


inductive star_extend : A -> List E -> A -> Prop where
  | refl : ∀ s, star_extend s [] s
  | step_int : ∀ s l s' s'' , star_extend s l s' ->  trans_refl rule s' s'' -> star_extend s l s''
  | step_ext : ∀ s l s' s'' e, star_extend s l s' -> method_i s' e s'' -> star_extend s (e :: l) s''



theorem enough_star (i i' : A) (s : B) (l : List E) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
  ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  φ₀ flush rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ₀ flush rule i' s':= by
    intro hm hm' hm'' HH HHH h1 h2
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
      have h2 :=  enoght_internal _ _ _ _ hm H2 _ h7 HH
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


end ReachingStar
