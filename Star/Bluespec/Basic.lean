/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Commute.ARS
import Star.Extra.HVector
import Star.Bluespec.Lib.BluespecPrelude

open BluespecPrelude

namespace ReachingStar.Bluespec

structure Event (M : Type) where
  V : Type
  α : Type
  f : α → Type
  l : List α
  name : M
  args : HVector f l
  ret : V

inductive MethodOrRule (R M : Type) where
| rule (name : R)
| method (event : Event M)

def Module R M := ARS (MethodOrRule R M)

def Module.getRule {R M} (m : Module R M) (name : R) : Rule m.A :=
  m.transitions (.rule name)

def Module.getARule {R M} (m : Module R M) : Rule m.A := fun s s' =>
  ∃ r : R, Module.getRule m r s s'

def Module.getMethod {R M} (m : Module R M) : Method m.A (Event M) := fun s e =>
  m.transitions (.method e) s

section ENOUGH

variable {R M}
variable {impl  : Module R M}
variable {spec  : Module Empty M}
variable {flush : impl.A → spec.A → Prop}
variable (FlushRulePreserved    : ∀ {i i' s}, relation_flush' flush i i' s impl.getARule)
variable (FlushMethodPreserved  : ∀ {i i' s s' e}, relation_flush_method' flush impl.getARule impl.getMethod spec.getMethod i i' s s' e)
variable (SpecMethodExists      : ∀ {i i' s e}, relation_method flush impl.getMethod spec.getMethod i i' s e)
variable (RulesCommute          : has_diamond_property (Relation.ReflTransGen impl.getARule))
variable (MethodAndRulesCommute : commutes_weakly_method_rule' impl.getMethod impl.getARule)

include FlushRulePreserved FlushMethodPreserved SpecMethodExists RulesCommute MethodAndRulesCommute in
theorem enough_star {i i' : impl.A} {s : spec.A} {l : List (Event M)} :
  φ₀ flush impl.getARule i s ->
  star_extend impl.getARule impl.getMethod i l i' ->
  ∃ s', star spec.getMethod s l s'
        ∧ φ₀ flush impl.getARule i' s' := by
  apply ReachingStar.enough_star
  · simp_rw[←relation_flush'_iff_relation_flush]; assumption
  · simp_rw[←relation_flush_method'_iff_relation_flush_method]; assumption
  · assumption
  · simp_rw[←has_diamond_property_reflTransGen_iff_trans_refl]; assumption
  · simp_rw[←commutes_weakly_method_rule'_iff_commutes_weakly_method_rule]; assumption

end ENOUGH

def Event.arg0 {M V} name v := @Event.mk M V (Fin 0) (λ _ => Empty) [] name .nil v
def Event.arg1 {M V A1} name a1 v := @Event.mk M V (Fin 1) (λ 0 => A1) [0] name (.cons a1 <| .nil) v
def Event.arg2 {M V A1 A2} name a1 a2 v := @Event.mk M V (Fin 2) (λ | 0 => A1 | 1 => A2) [0, 1] name (.cons a1 <| .cons a2 <| .nil) v

def ofAVMethod0 {M State Value} (meth : State → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Event M → State → State → Prop := fun e s s' =>
  ∃ v name, meth s = ⟨v, s'⟩
         ∧ e = Event.arg0 name v
         ∧ meth_RDY s = BTrue Unit_

def ofAVMethod1 {M State A1 Value} (meth : State → A1 → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Event M → State → State → Prop := fun e s s' =>
  ∃ a1 v name, meth s a1 = ⟨v, s'⟩
         ∧ e = Event.arg1 name a1 v
         ∧ meth_RDY s = BTrue Unit_

def ofAVMethod2 {M State A1 A2 Value} (meth : State → A1 → A2 → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Event M → State → State → Prop := fun e s s' =>
  ∃ a1 a2 v name, meth s a1 a2 = ⟨v, s'⟩
         ∧ e = Event.arg2 name a1 a2 v
         ∧ meth_RDY s = BTrue Unit_

def ofRule {State} (rule : State → t_bool × State) : State → State → Prop := fun s s' =>
  rule s = ⟨BTrue Unit_, s'⟩

theorem get_a_rule {m : Module R M} {s s' : m.A} : m.getRule r s s' → m.getARule s s' := by grind [Module.getARule]

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

end ReachingStar.Bluespec
