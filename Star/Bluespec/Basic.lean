/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Commute.ARS
import Star.Extra.HVector

namespace Star.Bluespec

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
  m.rules (.rule name)

def Module.getARule {R M} (m : Module R M) : Rule m.A := fun s s' =>
  ∃ r : R, Module.getRule m r s s'

def Module.getMethod {R M} (m : Module R M) : Method m.A (Event M) := fun s e =>
  m.rules (.method e) s

section ENOUGH

variable {R M}
variable {impl  : Module R M}
variable {spec  : Module Empty M}
variable {flush : impl.A → spec.A → Prop}
variable (FlushRulePreserved    : ∀ {i i' s}, relation_flush flush i i' s impl.getARule)
variable (FlushMethodPreserved  : ∀ {i i' s s' e}, relation_flush_method flush impl.getARule impl.getMethod spec.getMethod i i' s s' e)
variable (SpecMethodExists      : ∀ {i i' s e}, relation_method flush impl.getMethod spec.getMethod i i' s e)
variable (RulesCommute          : has_diamond_property (trans_refl impl.getARule))
variable (MethodAndRulesCommute : commutes_weakly_method_rule impl.getMethod impl.getARule)

include FlushRulePreserved FlushMethodPreserved SpecMethodExists RulesCommute MethodAndRulesCommute in
theorem enough_star {i i' : impl.A} {s : spec.A} {l : List (Event M)} :
  φ₀ flush impl.getARule i s ->
  star_extend impl.getARule impl.getMethod i l i' ->
  ∃ s', star spec.getMethod s l s' 
        ∧ φ₀ flush impl.getARule i' s' := by
  apply Star.enough_star <;> assumption

end ENOUGH

end Star.Bluespec
