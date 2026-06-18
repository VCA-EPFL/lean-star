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

inductive Method : Type where
| push
| pop

inductive Rule : Type where
| do_transfer

def SpecModule : Bluespec.Module Empty Method where
  A := ReachingStar.SingleQueue.State
  transitions e :=
    match e with
    | .rule s => Empty.casesOn _ s
    | .method e =>
      match e.name with
      | .push => ofAVMethod1 ReachingStar.SingleQueue.meth_push ReachingStar.SingleQueue.meth_RDY_push e
      | .pop => ofAVMethod0 ReachingStar.SingleQueue.meth_pop ReachingStar.SingleQueue.meth_RDY_pop e

def ImplModule : Bluespec.Module Rule Method where
  A := ReachingStar.DoubleQueue.State
  transitions e :=
    match e with
    | .rule .do_transfer => ofRule ReachingStar.DoubleQueue.rule_do_transfer
    | .method e =>
      match e.name with
      | .push => ofAVMethod1 ReachingStar.DoubleQueue.meth_push ReachingStar.DoubleQueue.meth_RDY_push e
      | .pop => ofAVMethod0 ReachingStar.DoubleQueue.meth_pop ReachingStar.DoubleQueue.meth_RDY_pop e

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (arg : Nat) (v : unit_), e = (Event.arg1 .push arg v)) ∨ (∃ (v : Nat), e = (Event.arg0 .pop v)) := by
  intro h
  cases e with
  | mk V α f l name args ret =>
    cases name
    · dsimp [SpecModule, Module.getMethod, ofAVMethod1,
        ReachingStar.SingleQueue.meth_push, ReachingStar.SingleQueue.meth_RDY_push] at h
      obtain ⟨arg, v, name, _hstate, hevent, _hready⟩ := h
      have hevent' := hevent
      injection hevent with _hV _hα _hf _hl hname _hargs _hret
      subst name
      exact Or.inl ⟨arg, v, hevent'⟩
    · dsimp [SpecModule, Module.getMethod, ofAVMethod0,
        ReachingStar.SingleQueue.meth_pop, ReachingStar.SingleQueue.meth_RDY_pop] at h
      obtain ⟨v, name, _hstate, hevent, _hready⟩ := h
      have hevent' := hevent
      injection hevent with _hV _hα _hf _hl hname _hargs _hret
      subst name
      exact Or.inr ⟨v, hevent'⟩

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (arg : Nat) (v : unit_), e = (Event.arg1 .push arg v)) ∨ (∃ (v : Nat), e = (Event.arg0 .pop v)) := by
  intro h
  cases e with
  | mk V α f l name args ret =>
    cases name
    · dsimp [ImplModule, Module.getMethod, ofAVMethod1,
        ReachingStar.DoubleQueue.meth_push, ReachingStar.DoubleQueue.meth_RDY_push] at h
      obtain ⟨arg, v, name, _hstate, hevent, _hready⟩ := h
      have hevent' := hevent
      injection hevent with _hV _hα _hf _hl hname _hargs _hret
      subst name
      exact Or.inl ⟨arg, v, hevent'⟩
    · dsimp [ImplModule, Module.getMethod, ofAVMethod0,
        ReachingStar.DoubleQueue.meth_pop, ReachingStar.DoubleQueue.meth_RDY_pop] at h
      obtain ⟨v, name, _hstate, hevent, _hready⟩ := h
      have hevent' := hevent
      injection hevent with _hV _hα _hf _hl hname _hargs _hret
      subst name
      exact Or.inr ⟨v, hevent'⟩

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .do_transfer i i' := by
  intro h
  obtain ⟨r, hr⟩ := h
  cases r
  exact hr

@[local grind →] theorem commutes_do_transfer_do_transfer {a b c : ImplModule.A} :
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
  ImplModule.getMethod s (Event.arg1 .push val v) s'' →
  ∃ s''',
    ImplModule.getMethod s' (Event.arg1 .push val v) s'''
    ∧ ImplModule.getRule .do_transfer s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod1,
    ReachingStar.DoubleQueue.rule_do_transfer, ReachingStar.DoubleQueue.meth_push,
    ReachingStar.DoubleQueue.meth_RDY_push] at hr hm ⊢
  cases v
  obtain ⟨a1, ret, name, hm_state, hevent, _hready⟩ := hm
  injection hevent with _hV _hα _hf _hl hname hargs hret
  subst name
  subst ret
  have hval : val = a1 := congrArg HVector.toSingle hargs
  subst a1
  injection hm_state with _ hs''
  subst s''
  split at hr
  · rename_i hs_ne
    injection hr with _ hs'
    subst s'
    cases s with
    | mk q1 q2 =>
      cases q1 with
      | nil => contradiction
      | cons x xs =>
        exists { queue1 := xs.concat val, queue2 := q2.concat x }
        constructor
        · exact ⟨val, Unit_, .push, rfl, rfl, rfl⟩
        · simp
  · simp at hr

@[local grind →] theorem reconverge_do_transfer_pop (s s' s'': ReachingStar.DoubleQueue.State) (v : Nat) :
  ImplModule.getRule .do_transfer s s' →
  ImplModule.getMethod s (Event.arg0 .pop v) s'' →
  ∃ s''',
    ImplModule.getMethod s' (Event.arg0 .pop v) s'''
    ∧ ImplModule.getRule .do_transfer s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.DoubleQueue.rule_do_transfer, ReachingStar.DoubleQueue.meth_pop,
    ReachingStar.DoubleQueue.meth_RDY_pop] at hr hm ⊢
  obtain ⟨ret, name, hm_state, hevent, hready⟩ := hm
  cases s with
  | mk q1 q2 =>
    cases q1 with
    | nil => simp at hr
    | cons x xs =>
      simp at hr
      subst s'
      cases q2 with
      | nil => cases hready
      | cons y ys =>
        injection hm_state with hret hs''
        subst ret
        subst s''
        exists { queue1 := xs, queue2 := ys.concat x }
        constructor
        · exact ⟨y, name, by
            dsimp [ReachingStar.DoubleQueue.meth_pop]
            rw [List.concat_eq_append], hevent, rfl⟩
        · simp

inductive flush : ImplModule.A → SpecModule.A → Prop where
| intro : flush { queue1 := [], queue2 := s } s

@[local grind →] theorem flush_indistinguishable_push (i i' : ImplModule.A) (s : SpecModule.A) (val : Nat) (v : unit_) :
  flush i s ->
  ImplModule.getMethod i (Event.arg1 .push val v) i' ->
  ∃ s', SpecModule.getMethod s (Event.arg1 .push val v) s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod1,
    ReachingStar.SingleQueue.meth_push, ReachingStar.SingleQueue.meth_RDY_push,
    ReachingStar.DoubleQueue.meth_push, ReachingStar.DoubleQueue.meth_RDY_push] at hm ⊢
  cases v
  exact ⟨s.concat val, val, Unit_, .push, rfl, rfl, rfl⟩

@[local grind →] theorem flush_indistinguishable_pop (i i' : ImplModule.A) (s : SpecModule.A) (v : Nat) :
  flush i s ->
  ImplModule.getMethod i (Event.arg0 .pop v) i' ->
  ∃ s', SpecModule.getMethod s (Event.arg0 .pop v) s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.SingleQueue.meth_pop, ReachingStar.SingleQueue.meth_RDY_pop,
    ReachingStar.DoubleQueue.meth_pop, ReachingStar.DoubleQueue.meth_RDY_pop] at hm ⊢
  obtain ⟨ret, name, hm_state, hevent, hready⟩ := hm
  injection hm_state with hret _hi'
  subst ret
  exists s.tail
  exact ⟨s.headD 0, name, rfl, hevent, hready⟩

@[local grind →] theorem reach_flush_again_pull (i i' : ImplModule.A) (s s' : SpecModule.A) (val : Nat) (v : unit_) :
  flush i s ->
  ImplModule.getMethod i (Event.arg1 .push val v) i' ->
  SpecModule.getMethod s (Event.arg1 .push val v) s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf him hsm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod1,
    ReachingStar.SingleQueue.meth_push, ReachingStar.SingleQueue.meth_RDY_push,
    ReachingStar.DoubleQueue.meth_push, ReachingStar.DoubleQueue.meth_RDY_push] at him hsm
  cases v
  obtain ⟨ia1, iret, iname, him_state, ih_event, _ih_ready⟩ := him
  injection ih_event with _hV _hα _hf _hl hiname hiargs hiret
  subst iname
  subst iret
  have hiarg : val = ia1 := congrArg HVector.toSingle hiargs
  subst ia1
  injection him_state with _ hi'
  subst i'
  obtain ⟨sa1, sret, sname, hsm_state, hs_event, _hs_ready⟩ := hsm
  injection hs_event with _hV _hα _hf _hl hsname hsargs hsret
  subst sname
  subst sret
  have hsarg : val = sa1 := congrArg HVector.toSingle hsargs
  subst sa1
  injection hsm_state with _ hs'
  subst s'
  exists { queue1 := [], queue2 := List.concat s val }
  constructor
  · apply Relation.ReflTransGen.single
    dsimp [Module.getARule, Module.getRule, ImplModule, ofRule, ReachingStar.DoubleQueue.rule_do_transfer]
    exact ⟨.do_transfer, by simp⟩
  · rw [List.concat_eq_append]
    exact flush.intro

@[local grind →] theorem reach_flush_again_pop (i i' : ImplModule.A) (s s' : SpecModule.A) (v : Nat) :
  flush i s ->
  ImplModule.getMethod i (Event.arg0 .pop v) i' ->
  SpecModule.getMethod s (Event.arg0 .pop v) s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf him hsm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.SingleQueue.meth_pop, ReachingStar.SingleQueue.meth_RDY_pop,
    ReachingStar.DoubleQueue.meth_pop, ReachingStar.DoubleQueue.meth_RDY_pop] at him hsm
  obtain ⟨iret, _iname, him_state, _ih_event, _ih_ready⟩ := him
  injection him_state with _hiret hi'
  subst i'
  obtain ⟨sret, _sname, hsm_state, _hs_event, _hs_ready⟩ := hsm
  injection hsm_state with _hsret hs'
  subst s'
  exists { queue1 := [], queue2 := s.tail }
  constructor
  · exact Relation.ReflTransGen.refl
  · exact flush.intro

@[local grind →] theorem flush_reaches_flush_do_transfer (i i' : ImplModule.A) (s : SpecModule.A) :
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

theorem method_rule_commute' {a b c : ImplModule.A} {e : Event Method} :
  ImplModule.getARule a b →
    ImplModule.getMethod a e c → ∃ d, ImplModule.getMethod b e d ∧ ImplModule.getARule c d := by grind

theorem rules_commute_weakly : commutes_weakly' ImplModule.getARule ImplModule.getARule := by grind

theorem flush_indistinguishable :
  ∀ {i i' s e}, relation_method flush ImplModule.getMethod SpecModule.getMethod i i' s e := by grind

theorem flush_method_preserved : ∀ {i i' s s' e},
  relation_flush_method' flush ImplModule.getARule ImplModule.getMethod SpecModule.getMethod i i' s s' e := by grind

theorem flush_reaches_flush : ∀ {i i' s}, relation_flush' flush i i' s ImplModule.getARule := by
  unfold relation_flush'
  intro i i' s hflush htrans
  induction htrans with
  | refl => grind
  | tail htrans hget ih => grind

------------------------------------------------------------------------------------------------------------------------

theorem method_rule_commute : commutes_weakly_method_rule' ImplModule.getMethod ImplModule.getARule := by
  apply method_rule_commute_trans_refl
  apply method_rule_commute'

theorem rules_commuting : has_diamond_property (Relation.ReflTransGen ImplModule.getARule) :=
  newmans_lemma rules_commute_weakly rules_strongly_normalising

theorem refines {i i' : ImplModule.A} {s : SpecModule.A} {l : List (Event Method)} :
  φ₀ flush ImplModule.getARule i s ->
  star_extend ImplModule.getARule ImplModule.getMethod i l i' ->
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ₀ flush ImplModule.getARule i' s' := by
  apply enough_star
  · exact flush_reaches_flush
  · exact flush_method_preserved
  · exact flush_indistinguishable
  · exact rules_commuting
  · exact method_rule_commute

/-- info: 'ReachingStar.Bluespec.Trivial.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refines

end ReachingStar.Bluespec.Trivial
