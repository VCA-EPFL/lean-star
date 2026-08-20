import Star.Bluespec.Lib.BluespecPrelude
import mkFIFO
import mkFIFOTest
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
open BluespecPrelude
open BluespecVerification
open ReachingStar Bluespec

set_option maxHeartbeats 1000000

-- ═══ Specification (fill in State, methods, and phi0) ═══

namespace M_mkFIFOTest.Spec

def State : Type := sorry

end M_mkFIFOTest.Spec

namespace M_mkFIFOTest.Refines

@[grind cases]
inductive Method : Type where

@[grind cases]
inductive Rule : Type where
| RL_r1
| RL_r2

def SpecModule : Bluespec.Module Empty Method where
  State := M_mkFIFOTest.Spec.State
  methods
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mkFIFOTest.state
  methods
  rules
    | .RL_r1 => ofRule M_mkFIFOTest.rule_RL_r1
    | .RL_r2 => ofRule M_mkFIFOTest.rule_RL_r2

-- The abstraction relation (the user's `phi0`); couples impl and spec state.
def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop := sorry

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  False := by
  sorry

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  False := by
  sorry

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .RL_r1 i i' ∨ ImplModule.getRule .RL_r2 i i' := by
  sorry

@[local grind →] theorem commutes_RL_r1_RL_r1 {a b c : ImplModule.State} :
  ImplModule.getRule .RL_r1 a c →
  ImplModule.getRule .RL_r1 a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_r1_RL_r2 {a b c : ImplModule.State} :
  ImplModule.getRule .RL_r1 a c →
  ImplModule.getRule .RL_r2 a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_r2_RL_r1 {a b c : ImplModule.State} :
  ImplModule.getRule .RL_r2 a c →
  ImplModule.getRule .RL_r1 a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_r2_RL_r2 {a b c : ImplModule.State} :
  ImplModule.getRule .RL_r2 a c →
  ImplModule.getRule .RL_r2 a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_r1 (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_r1 i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_r2 (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_r2 i i' → phi0 i' s := by
  sorry

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  sorry

-- ──────────────────────────────────────────────────────────────────────
-- Below: fixed generic boilerplate (closes `refines` via enough_star).
-- ──────────────────────────────────────────────────────────────────────

attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

def mkFIFOTest_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := phi0
  rules_strongly_normalising := rules_strongly_normalising
  method_rule_commute := by intro a b c e h hm; obtain ⟨r, hr⟩ := h; cases r <;> grind

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mkFIFOTest_refinement

#print axioms refines

end M_mkFIFOTest.Refines