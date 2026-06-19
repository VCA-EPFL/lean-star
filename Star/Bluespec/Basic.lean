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

def ofRule {State} (rule : State → t_bool × State) : State → State → Prop := fun s s' =>
  rule s = ⟨BTrue Unit_, s'⟩

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

end ReachingStar.Bluespec
