/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification

open BluespecPrelude
open BluespecVerification

namespace ReachingStar.DoubleQueue

structure State where
  queue1 : List Nat
  queue2 : List Nat

def meth_push (s : State) (n : Nat) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { s with queue1 := s.queue1.concat n } }

def meth_RDY_push (_ : State) : t_bool := BTrue Unit_

def meth_pop (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.queue2.headD 0
  , avAction_ := { s with queue2 := s.queue2.tail } }

def meth_RDY_pop (s : State) : t_bool :=
  if s.queue2 ≠ [] then BTrue Unit_ else BFalse Unit_

def rule_do_transfer (s : State) : t_bool × State :=
  if s.queue1 ≠ [] then
    let elem := s.queue1.headD 0
    (BTrue Unit_, { queue1 := s.queue1.tail, queue2 := s.queue2.concat elem })
  else (BFalse Unit_, s)

end ReachingStar.DoubleQueue

namespace ReachingStar.SingleQueue

@[simp] abbrev State := List Nat

def meth_push (s : State) (n : Nat) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := s.concat n }

def meth_RDY_push (_ : State) : t_bool := BTrue Unit_

def meth_pop (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.headD 0
  , avAction_ := s.tail }

def meth_RDY_pop (s : State) : t_bool :=
  if s ≠ [] then BTrue Unit_ else BFalse Unit_

end ReachingStar.SingleQueue

namespace ReachingStar.Bluespec.Trivial

@[grind cases]
inductive Method : Type where
| push
| pop

@[grind cases]
inductive Rule : Type where
| do_transfer

def SpecModule : Bluespec.Module Empty Method where
  State := ReachingStar.SingleQueue.State
  methods
    | .push => ofAVMethod1 ReachingStar.SingleQueue.meth_push ReachingStar.SingleQueue.meth_RDY_push
    | .pop => ofAVMethod0 ReachingStar.SingleQueue.meth_pop ReachingStar.SingleQueue.meth_RDY_pop
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := ReachingStar.DoubleQueue.State
  methods
    | .push => ofAVMethod1 ReachingStar.DoubleQueue.meth_push ReachingStar.DoubleQueue.meth_RDY_push
    | .pop => ofAVMethod0 ReachingStar.DoubleQueue.meth_pop ReachingStar.DoubleQueue.meth_RDY_pop
  rules
    | .do_transfer => ofRule ReachingStar.DoubleQueue.rule_do_transfer

/- @[local grind →] theorem SpecModule.get_method_cases :
 -   SpecModule.getMethod i e i' →
 -   (∃ (arg : Nat) (v : unit_), e.1 = .push ∧ e.2 = (Footprint.arg1 arg v)) ∨ (∃ (v : Nat), e.1 = .pop ∧ e.2 = (Footprint.arg0 v)) := by
 -   intro h
 -   obtain ⟨name, footprint⟩ := e
 -   cases name <;> (dsimp [SpecModule, Module.getMethod, ofAVMethod0, ofAVMethod1, ofAVMethod2] at *; grind)
 - 
 - @[local grind →] theorem ImplModule.get_method_cases :
 -   ImplModule.getMethod i e i' →
 -   (∃ (arg : Nat) (v : unit_), e.1 = .push ∧ e.2 = (Footprint.arg1 arg v)) ∨ (∃ (v : Nat), e.1 = .pop ∧ e.2 = (Footprint.arg0 v)) := by
 -   intro h
 -   obtain ⟨name, footprint⟩ := e
 -   cases name <;> (dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0, ofAVMethod1, ofAVMethod2] at *; grind)
 - 
 - @[local grind →] theorem ImplModule.get_rule_cases :
 -   ImplModule.getARule i i' →
 -   ImplModule.getRule .do_transfer i i' := by
 -   intro h
 -   obtain ⟨r, hr⟩ := h
 -   cases r
 -   exact hr -/

@[local grind →] theorem commutes_do_transfer_do_transfer {a b c : ImplModule.State} :
  ImplModule.getRule .do_transfer a c →
  ImplModule.getRule .do_transfer a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hcb : c = b := by
    dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.DoubleQueue.rule_do_transfer] at hc hb
    split at hc
    · split at hb
      · injection hc with _ hc'
        injection hb with _ hb'
        rw [← hc', ← hb']
      · contradiction
    · simp at hc
  subst b
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem reconverge_do_transfer_push (s s' s'': ReachingStar.DoubleQueue.State) (val : Nat) (v : unit_) :
  ImplModule.getRule .do_transfer s s' →
  ImplModule.getMethod s ⟨.push, Footprint.arg1 val v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.push, Footprint.arg1 val v⟩ s'''
    ∧ ImplModule.getRule .do_transfer s'' s''' := by
  sorry

@[local grind →] theorem reconverge_do_transfer_pop (s s' s'': ReachingStar.DoubleQueue.State) (v : Nat) :
  ImplModule.getRule .do_transfer s s' →
  ImplModule.getMethod s ⟨.pop, Footprint.arg0 v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.pop, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .do_transfer s'' s''' := by
  sorry

inductive flush : ImplModule.State → SpecModule.State → Prop where
| intro : flush { queue1 := [], queue2 := s } s

@[local grind →] theorem flush_indistinguishable_push (i i' : ImplModule.State) (s : SpecModule.State) (val : Nat) (v : unit_) :
  flush i s ->
  ImplModule.getMethod i ⟨.push, Footprint.arg1 val v⟩ i' ->
  ∃ s', SpecModule.getMethod s ⟨.push, Footprint.arg1 val v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod1,
    ReachingStar.SingleQueue.meth_push, ReachingStar.SingleQueue.meth_RDY_push,
    ReachingStar.DoubleQueue.meth_push, ReachingStar.DoubleQueue.meth_RDY_push] at hm ⊢
  cases v
  grind

@[local grind →] theorem flush_indistinguishable_pop (i i' : ImplModule.State) (s : SpecModule.State) (v : Nat) :
  flush i s ->
  ImplModule.getMethod i ⟨.pop, Footprint.arg0 v⟩ i' ->
  ∃ s', SpecModule.getMethod s ⟨.pop, Footprint.arg0 v⟩ s' := by
  sorry

@[local grind →] theorem reach_flush_again_pull (i i' : ImplModule.State) (s s' : SpecModule.State) (val : Nat) (v : unit_) :
  flush i s ->
  ImplModule.getMethod i ⟨.push, Footprint.arg1 val v⟩ i' ->
  SpecModule.getMethod s ⟨.push, Footprint.arg1 val v⟩ s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  sorry

@[local grind →] theorem reach_flush_again_pop (i i' : ImplModule.State) (s s' : SpecModule.State) (v : Nat) :
  flush i s ->
  ImplModule.getMethod i ⟨.pop, Footprint.arg0 v⟩ i' ->
  SpecModule.getMethod s ⟨.pop, Footprint.arg0 v⟩ s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  sorry

@[local grind →] theorem flush_reaches_flush_do_transfer (i i' : ImplModule.State) (s : SpecModule.State) :
  flush i s -> ImplModule.getRule .do_transfer i i' -> flush i' s := by
  intro hf hr
  cases hf
  dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.DoubleQueue.rule_do_transfer] at hr
  simp at hr

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  intro a
  cases a with
  | mk q1 q2 =>
    induction q1 generalizing q2 with
    | nil =>
      apply strongly_normalising'.step
      intro b hb
      dsimp [Module.getARule] at hb
      obtain ⟨r, hr⟩ := hb
      cases r
      dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.DoubleQueue.rule_do_transfer] at hr
      simp at hr
    | cons x xs ih =>
      apply strongly_normalising'.step
      intro b hb
      dsimp [Module.getARule] at hb
      obtain ⟨r, hr⟩ := hb
      cases r
      dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.DoubleQueue.rule_do_transfer] at hr
      simp at hr
      subst b
      simpa [List.concat_eq_append] using ih (q2.concat x)

------------------------------------------------------------------------------------------------------------------------

attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

#check Relation.TransGen.tail
#check Relation.reflTransGen_iff_eq

def queue_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := flush
  rules_strongly_normalising := rules_strongly_normalising
  method_rule_commute := sorry
  rules_commute_weakly := sorry
  flushed_indistinguishable := sorry
  flushed_method_preserved := sorry
  flush_reaches_flush := sorry

------------------------------------------------------------------------------------------------------------------------

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind flush queue_refinement.impl.getARule i s ->
  star_extend queue_refinement.impl.getARule queue_refinement.impl.getMethod i l i' ->
  ∃ s', star queue_refinement.spec.getMethod s l s'
        ∧ φ_ind queue_refinement.flushed queue_refinement.impl.getARule i' s' := enough_star queue_refinement

/- info: 'ReachingStar.Bluespec.Trivial.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in #print axioms refines

end ReachingStar.Bluespec.Trivial
