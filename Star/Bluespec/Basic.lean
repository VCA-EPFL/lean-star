/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Commute.ARS
import Star.Extra.HVector
import Star.Bluespec.Lib.BluespecPrelude

open BluespecPrelude

namespace ReachingStar.Bluespec

structure Footprint where
  V : Type
  α : Type
  f : α → Type
  l : List α
  args : HVector f l
  ret : V

structure Event (M : Type _) where
  name : M
  footprint : Footprint

inductive MethodOrRule (R M : Type) where
| rule (name : R)
| method (name : M) (footprint : Footprint)

def ARSModule R M := ARS (MethodOrRule R M)

def ARSModule.getRule {R M} (m : ARSModule R M) (name : R) : Rule m.A :=
  m.transitions (.rule name)

def ARSModule.getARule {R M} (m : ARSModule R M) : Rule m.A := fun s s' =>
  ∃ r : R, ARSModule.getRule m r s s'

def ARSModule.getMethod {R M} (m : ARSModule R M) : Method m.A (Event M) := fun s e =>
  m.transitions (.method e.1 e.2) s

@[simp] abbrev Methods (M : Type) (State : Type) := M → Footprint → State → State → Prop
@[simp] abbrev Rules (R : Type) (State : Type) := R → State → State → Prop

structure Module (R M : Type) where
  State : Type
  rules : Rules R State
  methods : Methods M State

def Module.toModule {R M} (s : Module R M) : ARSModule R M where
  A := s.State
  transitions e :=
    match e with
    | .rule n => s.rules n
    | .method n e => s.methods n e

def Module.getRule {R M} (m : Module R M) (name : R) : Rule m.State :=
  m.rules name

def Module.getARule {R M} (m : Module R M) : Rule m.State := fun s s' =>
  ∃ r : R, m.getRule r s s'

def Module.getMethod {R M} (m : Module R M) : Method m.State (Event M) := fun s e =>
  m.methods e.1 e.2 s

def Footprint.arg0 {V} v := @Footprint.mk V (Fin 0) (λ _ => Empty) [] .nil v
def Footprint.arg1 {V A1} a1 v := @Footprint.mk V (Fin 1) (λ 0 => A1) [0] (.cons a1 <| .nil) v
def Footprint.arg2 {V A1 A2} a1 a2 v := @Footprint.mk V (Fin 2) (λ | 0 => A1 | 1 => A2) [0, 1] (.cons a1 <| .cons a2 <| .nil) v

def ofAVMethod0 {State Value} (meth : State → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Footprint → State → State → Prop := fun e s s' =>
  ∃ v, meth s = ⟨v, s'⟩
         ∧ e = Footprint.arg0 v
         ∧ meth_RDY s = BTrue Unit_

def ofAVMethod1 {State A1 Value} (meth : State → A1 → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Footprint → State → State → Prop := fun e s s' =>
  ∃ a1 v, meth s a1 = ⟨v, s'⟩
         ∧ e = Footprint.arg1 a1 v
         ∧ meth_RDY s = BTrue Unit_

def ofAVMethod2 {State A1 A2 Value} (meth : State → A1 → A2 → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Footprint → State → State → Prop := fun e s s' =>
  ∃ a1 a2 v, meth s a1 a2 = ⟨v, s'⟩
         ∧ e = Footprint.arg2 a1 a2 v
         ∧ meth_RDY s = BTrue Unit_

/-- A zero-argument, unit-valued method that may also stutter: besides its real behaviour `m`,
it can fire without changing the state. -/
def orStutter0 {State} (m : Footprint → State → State → Prop) : Footprint → State → State → Prop :=
  fun e s s' => m e s s' ∨ (e = Footprint.arg0 Unit_ ∧ s' = s)

def orStutterRl {State} (rule : State → State → Prop) : State → State → Prop :=
  fun s s' => rule s s' ∨ (s' = s)

def ofRule {State} (rule : State → t_bool × State) : State → State → Prop := fun s s' =>
  rule s = ⟨BTrue Unit_, s'⟩

def liftRule {State₁} {State₂} (lift : State₁ → State₂) (acc : State₂ → State₁) (rule : State₁ → t_bool × State₁) : State₂ → t_bool × State₂ :=
  fun s =>
    let (f, s') := rule <| acc s
    (f, lift s')

theorem get_a_rule {m : Module R M} {s s' : m.State} : m.getRule r s s' → m.getARule s s' := by grind [Module.getARule]

theorem method_rule_commute_trans_refl {A : Type _} {E : Type _}
    (r : ReachingStar.Rule A) (m : ReachingStar.Method A E)
    (h : ∀ {a b c : A} {e : E}, r a b → m a e c → ∃ d, m b e d ∧ r c d) :
    ∀ {a b c : A} {e : E},
      Relation.ReflTransGen r a b → m a e c → ∃ d, m b e d ∧ Relation.ReflTransGen r c d := by
  intro a b c e href hm
  induction href using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl =>
      exact ⟨c, hm, Relation.ReflTransGen.refl⟩
  | head hstep _ ih =>
      obtain ⟨c', hc', hrc'⟩ := h hstep hm
      obtain ⟨d, hd_method, hd_rule⟩ := ih hc'
      exact ⟨d, hd_method, Relation.ReflTransGen.head hrc' hd_rule⟩

section RELATIONS

variable {A B E : Type _}

-- `Relation.ReflTransGen` versions of `relation_flush` / `relation_flush_method` from ARS.
def relation_flush' (flush : A → B → Prop) (i i' : A) (s : B) (rule : Rule A) :=
  flush i s → Relation.ReflTransGen rule i i' → ∃ i'', Relation.ReflTransGen rule i' i'' ∧ flush i'' s

def relation_flush_method' (flush : A → B → Prop) (rule : Rule A) (method_i : Method A E)
    (method_s : Method B E) (i i' : A) (s s' : B) (e : E) :=
  flush i s → method_i i e i' → method_s s e s' →
    ∃ i'', Relation.ReflTransGen rule i' i'' ∧ flush i'' s'

theorem relation_flush'_iff_relation_flush (flush : A → B → Prop) (rule : Rule A) (i i' : A) (s : B) :
    relation_flush' flush i i' s rule ↔ relation_flush flush i i' s rule := by
  unfold relation_flush' relation_flush
  simp_rw [trans_refl_equiv]

theorem relation_flush_method'_iff_relation_flush_method (flush : A → B → Prop) (rule : Rule A)
    (method_i : Method A E) (method_s : Method B E) (i i' : A) (s s' : B) (e : E) :
    relation_flush_method' flush rule method_i method_s i i' s s' e ↔
      relation_flush_method flush rule method_i method_s i i' s s' e := by
  unfold relation_flush_method' relation_flush_method
  simp_rw [trans_refl_equiv]

end RELATIONS

structure StructuredRefinement where
  Method : Type
  Rule : Type
  spec : Module Empty Method
  impl : Module Rule Method
  flushed : impl.State → spec.State → Prop
  rules_strongly_normalising : strongly_normalising impl.getARule
  method_rule_commute {a b c : impl.State} {e : Event Method} :
    impl.getARule a b →
      impl.getMethod a e c → ∃ d, impl.getMethod b e d ∧ impl.getARule c d := by grind
  rules_commute_weakly : commutes_weakly' impl.getARule impl.getARule := by grind
  flushed_indistinguishable :
    ∀ {i i' s e}, relation_method flushed impl.getMethod spec.getMethod i i' s e := by grind
  flushed_method_preserved : ∀ {i i' s s' e},
    relation_flush_method' flushed impl.getARule impl.getMethod spec.getMethod i i' s s' e := by grind
  flush_reaches_flush : ∀ {i i' s}, relation_flush' flushed i i' s impl.getARule := by
    unfold relation_flush'
    intro i i' s hflush htrans
    refine ⟨i', .refl, ?_⟩
    induction htrans with
    | refl => grind
    | tail htrans hget ih => grind

section REFINEMENT

variable (sr : StructuredRefinement)

theorem method_rule_commute
    : commutes_weakly_method_rule' sr.impl.getMethod sr.impl.getARule := by
  apply method_rule_commute_trans_refl
  apply @sr.method_rule_commute

theorem rules_commuting : has_diamond_property (Relation.ReflTransGen sr.impl.getARule) :=
  newmans_lemma sr.rules_commute_weakly sr.rules_strongly_normalising

theorem enough_star {i i' : sr.impl.State} {s : sr.spec.State} {l : List (Event sr.Method)} :
  φ_ind sr.flushed sr.impl.getARule i s ->
  star_extend sr.impl.getARule sr.impl.getMethod i l i' ->
  ∃ s', star sr.spec.getMethod s l s'
        ∧ φ_ind sr.flushed sr.impl.getARule i' s' := by
  have rules_commuting' := @rules_commuting sr
  have method_rule_commute := @method_rule_commute sr
  cases sr; dsimp at *; apply ReachingStar.enough_star
  · simp_rw[←relation_flush'_iff_relation_flush]; assumption
  · simp_rw[←relation_flush_method'_iff_relation_flush_method]; assumption
  · assumption
  · simp_rw[←has_diamond_property_reflTransGen_iff_trans_refl]; assumption
  · simp_rw[←commutes_weakly_method_rule'_iff_commutes_weakly_method_rule]; assumption

end REFINEMENT

/-- Like `StructuredRefinement`, for implementations whose methods only commute with rules
*up to internal steps* (`method_rule_commute`: after the rule, more rules may be needed before the
method can fire, and the two sides then reconverge), e.g. because a method may stutter.
Commutation is only required in states satisfying `reachable`, and the simulation is in `∃` form
(`flushed_simulates`), so the spec may be nondeterministic on an event label. -/
structure StructuredRefinementUpto where
  Method : Type
  Rule : Type
  spec : Module Empty Method
  impl : Module Rule Method
  flushed : impl.State → spec.State → Prop
  reachable : impl.State → Prop
  reachable_rule : ∀ {a b}, reachable a → impl.getARule a b → reachable b
  reachable_method : ∀ {a b e}, reachable a → impl.getMethod a e b → reachable b
  rules_strongly_normalising : strongly_normalising impl.getARule
  rules_commute_weakly : ∀ {a b c}, reachable a → impl.getARule a c → impl.getARule a b →
    ∃ d, Relation.ReflTransGen impl.getARule c d ∧ Relation.ReflTransGen impl.getARule b d
  method_rule_commute : ∀ {a b c : impl.State} {e : Event Method}, reachable a →
    impl.getARule a b → impl.getMethod a e c →
    ∃ b' d j, Relation.ReflTransGen impl.getARule b b' ∧ impl.getMethod b' e d ∧
      Relation.ReflTransGen impl.getARule c j ∧ Relation.ReflTransGen impl.getARule d j
  flushed_simulates : ∀ {i i' i'' s e}, flushed i s → Relation.ReflTransGen impl.getARule i i' →
    impl.getMethod i' e i'' →
    ∃ s', spec.getMethod s e s' ∧
      ∃ i''', Relation.ReflTransGen impl.getARule i'' i''' ∧ flushed i''' s'
  flush_reaches_flush : ∀ {i i' s}, relation_flush' flushed i i' s impl.getARule := by
    unfold relation_flush'
    intro i i' s hflush htrans
    refine ⟨i', .refl, ?_⟩
    induction htrans with
    | refl => grind
    | tail htrans hget ih => grind

section REFINEMENT_UPTO

variable (sr : StructuredRefinementUpto)

theorem StructuredRefinementUpto.reachable_trans_refl :
    ∀ a b, sr.reachable a → trans_refl sr.impl.getARule a b → sr.reachable b :=
  closed_trans_refl _ fun _ _ => sr.reachable_rule

theorem StructuredRefinementUpto.rules_confluent :
    has_diamond_property_on sr.reachable (trans_refl sr.impl.getARule) :=
  newmans_lemma_on (α := sr.impl.getARule) _ (fun _ _ => sr.reachable_rule)
    (fun hR hac hab => by
      simp_rw [trans_refl_equiv]; exact sr.rules_commute_weakly hR hac hab)
    sr.rules_strongly_normalising

theorem StructuredRefinementUpto.method_rule_commute_upto :
    commutes_method_rule_upto_on sr.reachable sr.impl.getMethod sr.impl.getARule :=
  commutes_upto_lift sr.impl.getARule sr.impl.getMethod _ sr.reachable_trans_refl (fun _ _ _ => sr.reachable_method)
    sr.rules_confluent sr.rules_strongly_normalising
    (fun hR hab hac => by simp_rw [trans_refl_equiv]; exact sr.method_rule_commute hR hab hac)

theorem enough_star_upto' {i i' : sr.impl.State} {s : sr.spec.State} {l : List (Event sr.Method)} :
  sr.reachable i →
  φ_ind sr.flushed sr.impl.getARule i s ->
  star_extend sr.impl.getARule sr.impl.getMethod i l i' ->
  ∃ s', star sr.spec.getMethod s l s'
        ∧ φ_ind sr.flushed sr.impl.getARule i' s' := by
  intro hR hφ hstar
  refine ReachingStar.enough_star_upto_sim sr.flushed sr.impl.getARule sr.impl.getMethod
    sr.spec.getMethod sr.reachable i i' s l ?_ ?_
    sr.reachable_trans_refl (fun _ _ _ => sr.reachable_method) sr.rules_confluent
    sr.method_rule_commute_upto hR hφ hstar
  · intro i i' s
    rw [← relation_flush'_iff_relation_flush]
    exact sr.flush_reaches_flush
  · intro i i' i'' s e hf h0 hm
    rw [trans_refl_equiv] at h0
    obtain ⟨s', hs', i''', h1, h2⟩ := sr.flushed_simulates hf h0 hm
    exact ⟨s', hs', i''', trans_refl_equiv.mpr h1, h2⟩

/-- Trace inclusion (as `ReachingStar.trace_inclusion`): from a reachable implementation state
flushed with respect to a spec state, every trace of the implementation (methods interleaved
with any internal steps) is a trace of the spec. -/
theorem trace_inclusion_upto (l : List (Event sr.Method)) (init_i : sr.impl.State)
    (init_s : sr.spec.State) (hR : sr.reachable init_i) (hinit : sr.flushed init_i init_s) :
    imp_behaviour sr.impl.getARule sr.impl.getMethod l init_i →
    spec_behaviour sr.spec.getMethod l init_s := by
  rintro ⟨i', h⟩
  obtain ⟨s', hs, -⟩ := enough_star_upto' sr hR (φ_ind.base _ _ hinit) h
  exact ⟨s', hs⟩

end REFINEMENT_UPTO

end ReachingStar.Bluespec
