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
  transitions : I → Rule A

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


inductive trans_refl1 {A} (α : Rule A) : Rule A where
| step {a b c} : α a b → trans_refl1 α b c → trans_refl1 α a c
| refl {a} : trans_refl1 α a a


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

def ARS.red_seq {I} (ars : ARS I) (i : I) : Rule ars.A := trans_refl (ars.transitions i)

inductive ARS.indexed_red_seq {I} (ars : ARS I) : List I → Rule ars.A where
| step {i is a b c} : ars.transitions i a b → ars.indexed_red_seq is b c → ars.indexed_red_seq (i :: is) a c
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

/-- Confluenza *relativa*: il diamante è richiesto solo negli stati che soddisfano `R` (per noi gli
stati raggiungibili). Equivale a "per ogni `a`, o `¬ R a`, oppure in `a` due riduzioni si
ricongiungono" (`has_diamond_property_on_iff`). -/
def has_diamond_property_on {A} (R : A → Prop) (α : Rule A) :=
  ∀ {a b c : A}, R a → α a c → α a b → ∃ d, α c d ∧ α b d

theorem has_diamond_property_on_iff {A} (R : A → Prop) (α : Rule A) :
    has_diamond_property_on R α ↔ ∀ a, ¬ R a ∨ ∀ b c, α a c → α a b → ∃ d, α c d ∧ α b d := by
  constructor
  · intro h a
    by_cases hR : R a
    · exact Or.inr (fun b c hac hab => h hR hac hab)
    · exact Or.inl hR
  · intro h a b c hR hac hab
    rcases h a with hn | hd
    · exact absurd hR hn
    · exact hd b c hac hab

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
  transitions := xor

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

inductive φ_ind : A -> B -> Prop where
| base : ∀ (i : A) (s : B),
          flush i s ->
          φ_ind i s
| rule_step : ∀ (i i' : A) (s : B),
              φ_ind i' s ->
              trans_refl rule i i' ->
              φ_ind i s
-- | method_step : ∀ (i i' : A) (s s' : B) (method_i : Method A) (method_s : Method B) n, --maybe add the forall trick
--               φ₀ i' s' ->
--               method_i i n i' ->
--               method_s s n s' ->
--               φ₀ i s

/-- Ritorno a flush dopo passi interni: se `i` è flushed rispetto a `s` e con passi interni si
arriva a `i'`, da `i'` si può proseguire con passi interni fino a uno stato `i''` di nuovo flushed
rispetto allo stesso `s`. È l'ipotesi che serve al caso base di `enoght_internal` (la
"flushabilità" `φ_ind` si conserva lungo i passi interni). La vecchia forma
`flush i s → trans_refl rule i i' → flush i' s` chiedeva che *ogni* `i'` fosse flushed, troppo
forte quando dagli stati flushed partono passi interni spontanei; la forma
`flush i s → ∃ i', trans_refl rule i i' ∧ flush i' s` è vera banalmente con `i' := i`. -/
def relation_flush (i i' : A) (s : B) (rule : Rule A) :=
  flush i s -> trans_refl rule i i' -> ∃ i'', trans_refl rule i' i'' ∧ flush i'' s
def relation_flush_method (i i' : A) (s s' : B) e := flush i s -> method_i i e i' -> method_s s e s' ->
                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'
def relation_method (i i' : A) (s : B) e := flush i s -> method_i i e i' -> ∃ s', method_s s e s'
def relation_init (init_i : A) (init_s : B) := flush init_i init_s



theorem enoght_internal (i : A) (s : B) :
    (∀ i i' s, relation_flush flush i i' s rule ) ->
    φ_ind flush rule i s -> ∀ i', trans_refl rule i i' -> has_diamond_property (trans_refl rule) -> φ_ind flush rule i' s := by
      intro he hφ₀ i' hstep hconf
      induction hφ₀ generalizing i'
      . rename_i i s' h3
        -- caso base: `i` flushed e `i →* i'`; per `relation_flush` da `i'` si torna a un `i''`
        -- flushed, quindi `φ_ind i' s'` per `rule_step`
        obtain ⟨i'', h4, h5⟩ := he i i' s' h3 hstep
        exact φ_ind.rule_step i' i'' s' (φ_ind.base i'' s' h5) h4
      . clear i s
        rename_i i i'' s h1 h2 h4
        unfold has_diamond_property at *
        specialize @hconf i i'' i' hstep h2
        cases hconf; rename_i d H; rcases H with ⟨H1, H2⟩
        specialize h4 d H2
        apply φ_ind.rule_step _ d _ <;> try assumption

def commutes_weakly_methods_i (α : Method A E) :=
  ∀ {a b c : A} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_methods_s (α : Method B E) :=
  ∀ {a b c : B} { e e' : E}, α a e c → α a e' b → ∃ d, α c e' d ∧  α b e d

def commutes_weakly_method_rule (α : Method A E) ( β : Rule A) :=
  ∀ {a b c : A} { e : E}, trans_refl β a b → α a e c → ∃ d, α b e d ∧ trans_refl β c d

/-- Commutazione metodo/regole *relativa*: richiesta solo negli stati che soddisfano `R`
("o `a` è irraggiungibile, o il metodo commuta con le regole in `a`"). -/
def commutes_weakly_method_rule_on (R : A → Prop) (α : Method A E) (β : Rule A) :=
  ∀ {a b c : A} {e : E}, R a → trans_refl β a b → α a e c → ∃ d, α b e d ∧ trans_refl β c d

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
    φ_ind flush rule i s -> commutes_weakly_method_rule method_i rule -> @indistinguishability  _ _ E method_i method_s i s := by
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
    φ_ind flush rule i s ->
    commutes_weakly_method_rule method_i rule ->
    ∀ i' e, method_i i e i' ->
    ∃ (s' : B), method_s s e s' ∧ φ_ind flush rule i' s' := by
      intro hm hm' hφ₀ h1 i' e h4
      induction hφ₀ generalizing i'
      . clear i s
        rename_i i s h5
        unfold relation_method at *
        unfold relation_flush_method at *
        specialize hm' _ _ _ _ h5 h4
        cases hm'; rename_i s' hm'
        constructor; rotate_left
        . exact s'
        . constructor
          . assumption
          . specialize hm i i' s s' e h5 h4 hm'
            rcases hm with ⟨ i'', hm, Hm⟩
            apply φ_ind.rule_step _ i''
            . constructor; assumption
            . assumption
      . clear i s
        rename_i i i'' s h5 h6 h7
        have hh {A E} := @h1 A E
        unfold commutes_weakly_method_rule at h1
        specialize @h1 i i'' i' e h6 h4
        cases h1; rename_i d h1; cases h1; rename_i h1 h1'
        specialize h7 d h1
        cases h7; rename_i s' h7; rcases h7 with ⟨ h7, h7'⟩
        constructor; rotate_left; exact s'
        constructor
        . assumption
        . apply φ_ind.rule_step _ d _ <;> try assumption

/-! ### Versioni *relative* a un insieme di stati `R` chiuso per passi

Le ipotesi di confluenza e di commutazione sono richieste solo negli stati che soddisfano `R`
(negli usi, gli stati raggiungibili dallo stato iniziale): "o lo stato è irraggiungibile, o lì vale
il diamante / la commutazione". `R` deve essere chiuso per passi interni (e, dove servono i
metodi, per passi esterni). Le versioni assolute qui sopra restano per gli altri file. -/

/-- `enoght_internal` con confluenza solo sugli stati `R`. -/
theorem enoght_internal_on (R : A → Prop) (i : A) (s : B) :
    (∀ i i' s, relation_flush flush i i' s rule) ->
    (∀ a b, R a → trans_refl rule a b → R b) ->
    has_diamond_property_on R (trans_refl rule) ->
    φ_ind flush rule i s -> R i -> ∀ i', trans_refl rule i i' -> φ_ind flush rule i' s := by
  intro he hR hconf hφ₀
  induction hφ₀ with
  | base i s' h3 =>
    intro _ i' hstep
    obtain ⟨i'', h4, h5⟩ := he i i' s' h3 hstep
    exact φ_ind.rule_step i' i'' s' (φ_ind.base i'' s' h5) h4
  | rule_step i i'' s' _ h2 ih =>
    intro hRi i' hstep
    obtain ⟨d, H1, H2⟩ := hconf hRi hstep h2
    exact φ_ind.rule_step i' d s' (ih (hR i i'' hRi h2) d H2) H1

/-- `indistinguisability_preservation` con commutazione solo sugli stati `R`. -/
theorem indistinguisability_preservation_on (R : A → Prop) (i : A) (s : B) :
    (∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
    (∀ a b, R a → trans_refl rule a b → R b) ->
    commutes_weakly_method_rule_on R method_i rule ->
    φ_ind flush rule i s -> R i -> @indistinguishability _ _ E method_i method_s i s := by
  intro hm hR h2 h1
  induction h1 with
  | base i s h3 =>
    intro _
    unfold indistinguishability
    intro i' e h4
    exact hm i i' s e h3 h4
  | rule_step i i' s _ h4 h5 =>
    intro hRi
    unfold indistinguishability at *
    intro i'' e h6
    obtain ⟨d, hd, _⟩ := h2 hRi h4 h6
    exact h5 (hR i i' hRi h4) d e hd

/-- `enoght_external` con commutazione solo sugli stati `R`. -/
theorem enoght_external_on (R : A → Prop) (i : A) (s : B) :
    (∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
    (∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
    (∀ a b, R a → trans_refl rule a b → R b) ->
    commutes_weakly_method_rule_on R method_i rule ->
    φ_ind flush rule i s -> R i ->
    ∀ i' e, method_i i e i' ->
    ∃ (s' : B), method_s s e s' ∧ φ_ind flush rule i' s' := by
  intro hm hm' hR h1 hφ₀
  induction hφ₀ with
  | base i s h5 =>
    intro _ i' e h4
    obtain ⟨s', hs'⟩ := hm' i i' s e h5 h4
    refine ⟨s', hs', ?_⟩
    obtain ⟨i'', hi'', Hi''⟩ := hm i i' s s' e h5 h4 hs'
    exact φ_ind.rule_step i' i'' s' (φ_ind.base i'' s' Hi'') hi''
  | rule_step i i'' s _ h6 h7 =>
    intro hRi i' e h4
    obtain ⟨d, hd, hd'⟩ := h1 hRi h6 h4
    obtain ⟨s', hs', hφ⟩ := h7 (hR i i'' hRi h6) d e hd
    exact ⟨s', hs', φ_ind.rule_step i' d s' hφ hd'⟩

/-! ### Commutazione *a meno di passi interni* e relazioni "dopo passi interni"

Nei protocolli di cache le risposte (`ld_rs`, `st_rs`) sono possibili solo in stati non flushed
(`S`/`M`), e i passi interni possono revocarli (invalidate, rilasci): la commutazione *immediata*
`commutes_weakly_method_rule_on`, che vuole il metodo abilitato subito dopo i passi interni, è
falsa (`msi_h5_false`). Vale invece una commutazione **a meno di passi interni**: dopo `a →* b` si
può proseguire con passi interni fino a un `b'` in cui il metodo è di nuovo abilitato, e i due esiti
(`c`, dopo il metodo in `a`; `d`, dopo il metodo in `b'`) si ricongiungono con passi interni.

Con questa ipotesi il metodo dello spec non viene più confrontato nello stato flushed ma in uno
stato `i'` raggiunto da uno flushed con passi interni: da qui `relation_method_int` e
`relation_flush_method_int`, che generalizzano `relation_method` e `relation_flush_method`
(caso `i' = i`). Per chiudere il diagramma servono il ritorno a flush (`relation_flush`) e la
confluenza sui raggiungibili (`has_diamond_property_on`): vedi `enoght_external_upto`. -/

/-- Transitività di `trans_refl`. -/
theorem trans_refl_trans {A} {r : Rule A} {a b c : A} (h1 : trans_refl r a b)
    (h2 : trans_refl r b c) : trans_refl r a c := by
  revert h2
  induction h1 with
  | refl => exact id
  | step hab _ ih => intro h2; exact trans_refl.step hab (ih h2)

/-- Commutazione metodo/regole **a meno di passi interni**, sugli stati `R`: se `a →* b` e in `a`
il metodo `e` porta in `c`, allora da `b` si arriva con passi interni a un `b'` in cui `e` è
abilitato e porta in `d`, e `c`, `d` si ricongiungono con passi interni in `j`. -/
def commutes_method_rule_upto_on (R : A → Prop) (α : Method A E) (β : Rule A) :=
  ∀ {a b c : A} {e : E}, R a → trans_refl β a b → α a e c →
    ∃ b' d j, trans_refl β b b' ∧ α b' e d ∧ trans_refl β c j ∧ trans_refl β d j

/-- La commutazione immediata implica quella a meno di passi interni (`b' := b`, `j := d`). -/
theorem commutes_upto_of_weakly_on (R : A → Prop) (α : Method A E) (β : Rule A)
    (h : commutes_weakly_method_rule_on R α β) : commutes_method_rule_upto_on R α β := by
  intro a b c e hR hab hac
  obtain ⟨d, hd, hcd⟩ := h hR hab hac
  exact ⟨b, d, d, trans_refl.refl, hd, hcd, trans_refl.refl⟩

/-- `relation_method` in uno stato `i'` raggiunto con passi interni da uno stato `i` flushed
rispetto a `s`: ogni metodo dell'implementazione in `i'` è possibile anche nello spec in `s`. -/
def relation_method_int (i i' i'' : A) (s : B) e :=
  flush i s -> trans_refl rule i i' -> method_i i' e i'' -> ∃ s', method_s s e s'

/-- `relation_flush_method` in uno stato `i'` raggiunto con passi interni da uno stato `i` flushed
rispetto a `s`: dopo lo stesso metodo in `i'` e in `s` si torna con passi interni a uno stato
flushed rispetto a `s'`. -/
def relation_flush_method_int (i i' i'' : A) (s s' : B) e :=
  flush i s -> trans_refl rule i i' -> method_i i' e i'' -> method_s s e s' ->
    ∃ i''', trans_refl rule i'' i''' ∧ flush i''' s'

/-- Se il flush è conservato dai passi interni (come in Paxos), `relation_method` dà
`relation_method_int`. -/
theorem relation_method_int_of_relation_method
    (hpres : ∀ i i' s, flush i s → trans_refl rule i i' → flush i' s)
    (hm : ∀ i i' s e, relation_method flush method_i method_s i i' s e) :
    ∀ i i' i'' s e, relation_method_int flush rule method_i method_s i i' i'' s e := by
  intro i i' i'' s e hf htr hmeth
  exact hm i' i'' s e (hpres i i' s hf htr) hmeth

/-- Se il flush è conservato dai passi interni, `relation_flush_method` dà
`relation_flush_method_int`. -/
theorem relation_flush_method_int_of_relation_flush_method
    (hpres : ∀ i i' s, flush i s → trans_refl rule i i' → flush i' s)
    (hm : ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) :
    ∀ i i' i'' s s' e, relation_flush_method_int flush rule method_i method_s i i' i'' s s' e := by
  intro i i' i'' s s' e hf htr hmeth hs
  exact hm i' i'' s s' e (hpres i i' s hf htr) hmeth hs

/-- `enoght_external` con la commutazione a meno di passi interni.

La conclusione è generalizzata al metodo eseguito in uno stato `i₀` raggiunto da `i` con passi
interni (serve per l'induzione su `φ_ind`). Caso base, `i` flushed: bastano `relation_method_int`
e `relation_flush_method_int`. Caso induttivo, `φ_ind i s` via `i →* i''`: la confluenza in `i`
(`has_diamond_property_on`) ricongiunge `i₀` e `i''` in `k`; la commutazione debole in `i₀`
lungo `i₀ →* k` sposta il metodo in un `b'` oltre `k`, quindi oltre `i''`, dove vale l'ipotesi
induttiva e si ottengono `s'` e `φ_ind d s'`; da `d` a `j` (ricongiungimento con `i'`) `φ_ind` si
conserva per `enoght_internal_on`, che usa il ritorno a flush e di nuovo la confluenza; infine
`i' →* j` dà `φ_ind i' s'`. `R` deve essere chiuso per passi interni ed esterni. -/
theorem enoght_external_upto (R : A → Prop) (i : A) (s : B) :
    (∀ i i' s, relation_flush flush i i' s rule) ->
    (∀ i i' i'' s s' e, relation_flush_method_int flush rule method_i method_s i i' i'' s s' e) ->
    (∀ i i' i'' s e, relation_method_int flush rule method_i method_s i i' i'' s e) ->
    (∀ a b, R a → trans_refl rule a b → R b) ->
    (∀ a b e, R a → method_i a e b → R b) ->
    has_diamond_property_on R (trans_refl rule) ->
    commutes_method_rule_upto_on R method_i rule ->
    φ_ind flush rule i s -> R i ->
    ∀ i₀ i' e, trans_refl rule i i₀ -> method_i i₀ e i' ->
    ∃ (s' : B), method_s s e s' ∧ φ_ind flush rule i' s' := by
  intro hfl hfm hm hR1 hR2 hconf hcomm hφ
  induction hφ with
  | base i s hf =>
    intro _ i₀ i' e h0 hmeth
    obtain ⟨s', hs'⟩ := hm i i₀ i' s e hf h0 hmeth
    obtain ⟨i''', h1, h2⟩ := hfm i i₀ i' s s' e hf h0 hmeth hs'
    exact ⟨s', hs', φ_ind.rule_step i' i''' s' (φ_ind.base i''' s' h2) h1⟩
  | rule_step i i'' s _ h6 ih =>
    intro hRi i₀ i' e h0 hmeth
    -- confluenza in `i`: `i₀` e `i''` si ricongiungono in `k`
    obtain ⟨k, hk1, hk2⟩ := hconf hRi h0 h6
    -- commutazione a meno di passi interni in `i₀`, lungo `i₀ →* k`
    have hRi₀ : R i₀ := hR1 i i₀ hRi h0
    obtain ⟨b', d, j, hb', hd, hj1, hj2⟩ := hcomm hRi₀ hk1 hmeth
    -- `b'` è oltre `i''`: ipotesi induttiva
    have hRi'' : R i'' := hR1 i i'' hRi h6
    have hib' : trans_refl rule i'' b' := trans_refl_trans hk2 hb'
    obtain ⟨s', hs', hφd⟩ := ih hRi'' b' d e hib' hd
    -- da `d` a `j` si conserva `φ_ind`; poi `i' →* j`
    have hRd : R d := hR2 b' d e (hR1 i'' b' hRi'' hib') hd
    have hφj : φ_ind flush rule j s' :=
      enoght_internal_on flush rule R d s' hfl hR1 hconf hφd hRd j hj2
    exact ⟨s', hs', φ_ind.rule_step i' j s' hφj hj1⟩

inductive star : A -> List E -> A -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1 s2 s3 l e1, star s1 l s2 -> method_i s2 e1 s3 -> star s1 (e1 :: l) s3

inductive star_extend : A -> List E -> A -> Prop where
  | refl : ∀ s, star_extend s [] s
  | step_int : ∀ s l s' s'' , star_extend s l s' ->  trans_refl rule s' s'' -> star_extend s l s''
  | step_ext : ∀ s l s' s'' e, star_extend s l s' -> method_i s' e s'' -> star_extend s (e :: l) s''


def reachable (i : A) (init) :=
  ∃ l, star_extend rule method_i init l i


-- theorem enough_star (i i' : A) (s : B) (l : List E) :
--   (∀ i i' s, relation_flush flush i i' s rule ) ->
--   ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
--   ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
--   has_diamond_property (trans_refl rule) ->
--   commutes_weakly_method_rule method_i rule ->
--   φ_ind flush rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ_ind flush rule i' s':= by
--     intro hm hm' hm'' HH HHH h1 h2
--     revert h1 s
--     induction h2 <;> intro s
--     . intro h3
--       exact ⟨ s, star.refl s, h3⟩
--     . rename_i l' i_1 i_2  h9 h7 hi
--       intro h11
--       have h10 := hi _ h11
--       cases h10
--       rename_i s_1 h1
--       let ⟨H1, H2⟩ := h1
--       have h2 :=  enoght_internal _ _ _ _ hm H2 _ h7 HH
--       constructor; rotate_left
--       . exact s_1
--       . constructor <;> assumption
--     . clear i'
--       rename_i l' i' i'' e _ h2 h3
--       intro h4
--       have h5 := h3 _ h4
--       cases h5
--       rename_i s' h6
--       have h7 := enoght_external _ _ _ method_s  _ _ hm' hm'' h6.right (by assumption) _ _ h2
--       cases h7
--       rename_i s2 h8
--       cases h8
--       rename_i h8 h8'
--       rcases h6 with ⟨ h6, h6'⟩
--       constructor; rotate_left
--       . exact s2
--       . constructor
--         . apply star.step
--           . exact h6
--           . assumption
--         . assumption

theorem enough_star (i i' : A) (s : B) (l : List E) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
  ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  φ_ind flush rule i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ_ind flush rule i' s':= by
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




/-- Un insieme di stati chiuso per passi interni ed esterni è chiuso lungo le esecuzioni. -/
theorem R_of_star_extend (R : A → Prop) (hR1 : ∀ a b, R a → trans_refl rule a b → R b)
    (hR2 : ∀ a b e, R a → method_i a e b → R b) {i i' : A} {l : List E}
    (hi : R i) (h : star_extend rule method_i i l i') : R i' := by
  induction h with
  | refl => exact hi
  | step_int l' s' s'' _ hstep ih => exact hR1 s' s'' ih hstep
  | step_ext l' s' s'' e _ hstep ih => exact hR2 s' s'' e ih hstep

/-- `enough_star` con confluenza e commutazione solo sugli stati `R`, chiuso per passi interni ed
esterni e vero nello stato di partenza. -/
theorem enough_star_on (R : A → Prop) (i i' : A) (s : B) (l : List E) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
  ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
  (∀ a b, R a → trans_refl rule a b → R b) ->
  (∀ a b e, R a → method_i a e b → R b) ->
  has_diamond_property_on R (trans_refl rule) ->
  commutes_weakly_method_rule_on R method_i rule ->
  R i -> φ_ind flush rule i s -> star_extend rule method_i i l i' ->
  ∃ s', star method_s s l s' ∧ φ_ind flush rule i' s' := by
  intro hm hm' hm'' hR1 hR2 HH HHH hRi h1 h2
  revert h1 s
  induction h2 with
  | refl =>
    intro s h3
    exact ⟨s, star.refl s, h3⟩
  | step_int l' i_1 i_2 h9 h7 ih =>
    intro s h11
    obtain ⟨s_1, H1, H2⟩ := ih s h11
    have hR' : R i_1 := R_of_star_extend _ _ R hR1 hR2 hRi h9
    exact ⟨s_1, H1, enoght_internal_on _ _ R i_1 s_1 hm hR1 HH H2 hR' i_2 h7⟩
  | step_ext l' i_1 i_2 e h9 h2 ih =>
    intro s h4
    obtain ⟨s', H1, H2⟩ := ih s h4
    have hR' : R i_1 := R_of_star_extend _ _ R hR1 hR2 hRi h9
    obtain ⟨s2, h8, h8'⟩ := enoght_external_on _ _ _ _ R i_1 s' hm' hm'' hR1 HHH H2 hR' i_2 e h2
    exact ⟨s2, star.step s s' s2 l' e H1 h8, h8'⟩

/-- `enough_star` con la commutazione a meno di passi interni: come `enough_star_on`, ma i passi
esterni sono trattati da `enoght_external_upto` (con `i₀ := i`, zero passi interni prima del
metodo) e le relazioni con lo spec sono nella forma `_int`. -/
theorem enough_star_upto (R : A → Prop) (i i' : A) (s : B) (l : List E) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  (∀ i i' i'' s s' e, relation_flush_method_int flush rule method_i method_s i i' i'' s s' e) ->
  (∀ i i' i'' s e, relation_method_int flush rule method_i method_s i i' i'' s e) ->
  (∀ a b, R a → trans_refl rule a b → R b) ->
  (∀ a b e, R a → method_i a e b → R b) ->
  has_diamond_property_on R (trans_refl rule) ->
  commutes_method_rule_upto_on R method_i rule ->
  R i -> φ_ind flush rule i s -> star_extend rule method_i i l i' ->
  ∃ s', star method_s s l s' ∧ φ_ind flush rule i' s' := by
  intro hm hm' hm'' hR1 hR2 HH HHH hRi h1 h2
  revert h1 s
  induction h2 with
  | refl =>
    intro s h3
    exact ⟨s, star.refl s, h3⟩
  | step_int l' i_1 i_2 h9 h7 ih =>
    intro s h11
    obtain ⟨s_1, H1, H2⟩ := ih s h11
    have hR' : R i_1 := R_of_star_extend _ _ R hR1 hR2 hRi h9
    exact ⟨s_1, H1, enoght_internal_on _ _ R i_1 s_1 hm hR1 HH H2 hR' i_2 h7⟩
  | step_ext l' i_1 i_2 e h9 h2 ih =>
    intro s h4
    obtain ⟨s', H1, H2⟩ := ih s h4
    have hR' : R i_1 := R_of_star_extend _ _ R hR1 hR2 hRi h9
    obtain ⟨s2, h8, h8'⟩ :=
      enoght_external_upto _ _ _ _ R i_1 s' hm hm' hm'' hR1 hR2 HH HHH H2 hR' i_1 i_2 e
        trans_refl.refl h2
    exact ⟨s2, star.step s s' s2 l' e H1 h8, h8'⟩

def imp_behaviour (l : List E) (init : A): Prop :=
  exists s', star_extend rule method_i init l s'

def spec_behaviour (l : List E) (init : B): Prop :=
  exists s', star method_s init l s'





/-- Inclusione delle tracce, versione con commutazione **immediata** (`commutes_weakly_method_rule_on`):
è la versione precedente, tenuta per i sistemi in cui i metodi restano abilitati dopo i passi interni
(per i protocolli di cache è inapplicabile, vedi `msi_h5_false`; usare `trace_inclusion`).

Le ipotesi di confluenza e di commutazione sono *relative agli stati raggiungibili* da `init_i`:
per ogni stato `i'`, o `i'` non è raggiungibile (`¬ reachable rule method_i i' init_i`), oppure in
`i'` due riduzioni interne si ricongiungono e i metodi commutano con le regole
(`has_diamond_property_on_iff`). Negli stati irraggiungibili non c'è nulla da dimostrare: la prova
(`enough_star_on`) usa il diamante e la commutazione solo negli stati dell'esecuzione, tutti
raggiungibili da `init_i`.

Nota: senza un legame tra `init_i` e `init_s` il teorema è falso (controesempio:
`flush := fun _ _ => False`, `method_s := fun _ _ _ => False`, `l := [()]`), da cui l'ipotesi
`relation_init flush init_i init_s`, cioè `flush init_i init_s`, che dà
`φ_ind flush rule init_i init_s` con `φ_ind.base`. -/
theorem trace_inclusion_strong (l : List E) (init_i : A) (init_s : B) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  ( ∀ i i' s s' e, relation_flush_method flush rule method_i method_s i i' s s' e) ->
  ( ∀ i i' s e, relation_method flush method_i method_s i i' s e) ->
  has_diamond_property_on (fun i' => reachable rule method_i i' init_i) (trans_refl rule) ->
  commutes_weakly_method_rule_on (fun i' => reachable rule method_i i' init_i) method_i rule ->
  relation_init flush init_i init_s ->
  imp_behaviour rule method_i l init_i -> spec_behaviour method_s l init_s := by
    intro ha hb hc hd he hφ h1
    obtain ⟨i', h5⟩ := h1
    have hR1 : ∀ a b, reachable rule method_i a init_i → trans_refl rule a b →
        reachable rule method_i b init_i := by
      intro a b hab hb'
      obtain ⟨l₀, hl₀⟩ := hab
      exact ⟨l₀, star_extend.step_int init_i l₀ a b hl₀ hb'⟩
    have hR2 : ∀ a b e, reachable rule method_i a init_i → method_i a e b →
        reachable rule method_i b init_i := by
      intro a b e hab hb'
      obtain ⟨l₀, hl₀⟩ := hab
      exact ⟨e :: l₀, star_extend.step_ext init_i l₀ a b e hl₀ hb'⟩
    have hR0 : reachable rule method_i init_i init_i := ⟨[], star_extend.refl init_i⟩
    obtain ⟨s', h6, _⟩ :=
      enough_star_on flush rule method_i method_s (fun i' => reachable rule method_i i' init_i)
        init_i i' init_s l ha hb hc hR1 hR2 hd he hR0 (φ_ind.base _ _ hφ) h5
    exact ⟨s', h6⟩

/-- **Inclusione delle tracce.**

Le ipotesi di confluenza e di commutazione sono *relative agli stati raggiungibili* da `init_i`
("o lo stato è irraggiungibile, o lì vale la proprietà", `has_diamond_property_on_iff`), e la
commutazione è **a meno di passi interni** (`commutes_method_rule_upto_on`): dopo i passi interni
il metodo può richiedere altri passi interni prima di essere di nuovo abilitato, e i due esiti si
ricongiungono. Di conseguenza le relazioni con lo spec sono nella forma "dopo passi interni da uno
stato flushed" (`relation_method_int`, `relation_flush_method_int`); per i sistemi in cui il flush è
conservato dai passi interni si ottengono dalle forme semplici con
`relation_method_int_of_relation_method` e `relation_flush_method_int_of_relation_flush_method`,
e la commutazione debole da quella immediata con `commutes_upto_of_weakly_on`.

La prova (`enough_star_upto`) usa il diamante e la commutazione solo negli stati dell'esecuzione,
tutti raggiungibili da `init_i`; il ritorno a flush (`relation_flush`) e la confluenza servono per
chiudere il diagramma dei passi esterni (`enoght_external_upto`).

Nota: senza un legame tra `init_i` e `init_s` il teorema è falso (controesempio:
`flush := fun _ _ => False`, `method_s := fun _ _ _ => False`, `l := [()]`), da cui l'ipotesi
`relation_init flush init_i init_s`, cioè `flush init_i init_s`, che dà
`φ_ind flush rule init_i init_s` con `φ_ind.base`. -/
theorem trace_inclusion (l : List E) (init_i : A) (init_s : B) :
  (∀ i i' s, relation_flush flush i i' s rule ) ->
  (∀ i i' i'' s s' e, relation_flush_method_int flush rule method_i method_s i i' i'' s s' e) ->
  (∀ i i' i'' s e, relation_method_int flush rule method_i method_s i i' i'' s e) ->
  has_diamond_property_on (fun i' => reachable rule method_i i' init_i) (trans_refl rule) ->
  commutes_method_rule_upto_on (fun i' => reachable rule method_i i' init_i) method_i rule ->
  relation_init flush init_i init_s ->
  imp_behaviour rule method_i l init_i -> spec_behaviour method_s l init_s := by
    intro ha hb hc hd he hφ h1
    obtain ⟨i', h5⟩ := h1
    have hR1 : ∀ a b, reachable rule method_i a init_i → trans_refl rule a b →
        reachable rule method_i b init_i := by
      intro a b hab hb'
      obtain ⟨l₀, hl₀⟩ := hab
      exact ⟨l₀, star_extend.step_int init_i l₀ a b hl₀ hb'⟩
    have hR2 : ∀ a b e, reachable rule method_i a init_i → method_i a e b →
        reachable rule method_i b init_i := by
      intro a b e hab hb'
      obtain ⟨l₀, hl₀⟩ := hab
      exact ⟨e :: l₀, star_extend.step_ext init_i l₀ a b e hl₀ hb'⟩
    have hR0 : reachable rule method_i init_i init_i := ⟨[], star_extend.refl init_i⟩
    obtain ⟨s', h6, _⟩ :=
      enough_star_upto flush rule method_i method_s (fun i' => reachable rule method_i i' init_i)
        init_i i' init_s l ha hb hc hR1 hR2 hd he hR0 (φ_ind.base _ _ hφ) h5
    exact ⟨s', h6⟩

end ReachingStar
