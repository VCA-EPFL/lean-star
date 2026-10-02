/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification

open BluespecPrelude
open BluespecVerification

namespace ReachingStar.MultiplierSpec

structure State where
  result : Nat
  busy   : Bool

def width   : Nat := 32
def base    : Nat := 2
def modulus : Nat := base ^ width

def meth_put (_ : State) (v1 v2 : BitVec 32) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { result := (v1.toNat * v2.toNat) % modulus, busy := true } }

def meth_RDY_put (s : State) : t_bool :=
  if s.busy then BFalse Unit_ else BTrue Unit_

def meth_getV (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.result
  , avAction_ := s }

def meth_RDY_getV (s : State) : t_bool :=
  if s.busy then BTrue Unit_ else BFalse Unit_

def meth_getA (s : State) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { s with busy := false } }

def meth_RDY_getA (s : State) : t_bool :=
  if s.busy then BTrue Unit_ else BFalse Unit_

end ReachingStar.MultiplierSpec

namespace ReachingStar.MultiplierImpl

structure State where
  a     : Nat
  b     : Nat
  prod  : Nat
  carry : Nat
  step  : Nat
  busy  : Bool

def width    : Nat := 32
def base     : Nat := 2
def modulus  : Nat := base ^ width
def topPlace : Nat := modulus / base

def bit0 (x : Nat) : Nat := x % base
def selected (s : State) : Nat := s.a * bit0 s.b
def stepSum (s : State) : Nat := selected s + s.carry

def meth_put (_ : State) (v1 v2 : BitVec 32) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { a := v1.toNat, b := v2.toNat, prod := 0, carry := 0, step := 0, busy := true } }

def meth_RDY_put (s : State) : t_bool :=
  if s.busy then BFalse Unit_ else BTrue Unit_

def meth_getV (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.prod
  , avAction_ := s }

def meth_RDY_getV (s : State) : t_bool :=
  if s.busy ∧ s.step = width then BTrue Unit_ else BFalse Unit_

def meth_getA (s : State) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { s with busy := false } }

def meth_RDY_getA (s : State) : t_bool :=
  if s.busy ∧ s.step = width then BTrue Unit_ else BFalse Unit_

def rule_mulStep (s : State) : t_bool × State :=
  if s.busy ∧ s.a ≠ 0 ∧ s.step < width then
    (BTrue Unit_,
      { a := s.a
      , b := s.b / base
      , prod := (stepSum s % base) * topPlace + s.prod / base
      , carry := stepSum s / base
      , step := s.step + 1
      , busy := s.busy })
  else (BFalse Unit_, s)

def rule_mulStepFast (s : State) : t_bool × State :=
  if s.busy ∧ s.a = 0 ∧ s.step < width then
    (BTrue Unit_, { s with prod := s.a, step := width })
  else (BFalse Unit_, s)

end ReachingStar.MultiplierImpl

namespace ReachingStar.Bluespec.Multiplier

@[grind cases]
inductive Method : Type where
| put
| getA
| getV

@[grind cases]
inductive Rule : Type where
| mulStep
| mulStepFast

def SpecModule : Bluespec.Module Empty Method where
  State := ReachingStar.MultiplierSpec.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierSpec.meth_put  ReachingStar.MultiplierSpec.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierSpec.meth_getA ReachingStar.MultiplierSpec.meth_RDY_getA
    | .getV => ofAVMethod0 ReachingStar.MultiplierSpec.meth_getV ReachingStar.MultiplierSpec.meth_RDY_getV
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := ReachingStar.MultiplierImpl.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierImpl.meth_put  ReachingStar.MultiplierImpl.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getA ReachingStar.MultiplierImpl.meth_RDY_getA
    | .getV => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getV ReachingStar.MultiplierImpl.meth_RDY_getV
  rules
    | .mulStep     => ofRule ReachingStar.MultiplierImpl.rule_mulStep
    | .mulStepFast => ofRule ReachingStar.MultiplierImpl.rule_mulStepFast

def concret (i : BitVec 32) : Bluespec.Module Rule Method :=
  { ImplModule with
    methods a := match a with
                 | .put => fun f s1 s2 => ∃ a1 a2 v v', ReachingStar.MultiplierImpl.meth_put s1 i a2 = ⟨v, s2⟩
                                           ∧ f = Footprint.arg2 a1 a2 v'
                                           ∧ ReachingStar.MultiplierImpl.meth_RDY_put s1 = BTrue Unit_
                 | _ => ImplModule.methods a
  }

def concret (i : BitVec 32) : Bluespec.Module Rule Method :=
  { ImplModule with
    methods a := match a with
                 | .put => fun f s1 s2 =>
                 ∃ a1 a2 v v' f', f = Footprint.arg2 a1 a2 v ∧ f' = Footprint.arg2 i a2 v' ∧ ImplModule.methods.put f' s1 s2
                 | _ => ImplModule.methods a
  }

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v1 v2 : BitVec 32) (v : unit_), e.1 = .put ∧ e.2 = (Footprint.arg2 v1 v2 v)) ∨
    (∃ (v : unit_), e.1 = .getA ∧ e.2 = (Footprint.arg0 v)) ∨
    (∃ (v : Nat), e.1 = .getV ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [ImplModule, Module.getMethod, ofAVMethod0, ofAVMethod2] at *; grind)

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .mulStep i i' ∨ ImplModule.getRule .mulStepFast i i' := by
  intro h
  obtain ⟨r, hr⟩ := h
  cases r
  · exact Or.inl hr
  · exact Or.inr hr

@[local grind →] theorem commutes_mulStep_mulStep {s b c : ImplModule.State} :
  ImplModule.getRule .mulStep s c →
  ImplModule.getRule .mulStep s b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hcb : c = b := by
    dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.MultiplierImpl.rule_mulStep] at hc hb
    split at hc
    · split at hb
      · injection hc with _ hc'
        injection hb with _ hb'
        rw [← hc', ← hb']
      · simp_all
    · simp_all
  subst b
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_mulStepFast_mulStepFast {s b c : ImplModule.State} :
  ImplModule.getRule .mulStepFast s c →
  ImplModule.getRule .mulStepFast s b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hcb : c = b := by
    dsimp [ImplModule, Module.getRule, ofRule, ReachingStar.MultiplierImpl.rule_mulStepFast] at hc hb
    split at hc
    · split at hb
      · injection hc with _ hc'
        injection hb with _ hb'
        rw [← hc', ← hb']
      · simp_all
    · simp_all
  subst b
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_mulStep_mulStepFast {s b c : ImplModule.State} :
  ImplModule.getRule .mulStep s c →
  ImplModule.getRule .mulStepFast s b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule,
    ReachingStar.MultiplierImpl.rule_mulStep,
    ReachingStar.MultiplierImpl.rule_mulStepFast] at hc hb
  split at hc
  · rename_i hcond
    split at hb
    · rename_i hcond'
      exact hcond.2.1 hcond'.2.1
    · simp_all
  · simp_all

@[local grind →] theorem reconverge_mulStep_put (s s' s'' : ReachingStar.MultiplierImpl.State)
    (v1 v2 : BitVec 32) (v : unit_) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.put, Footprint.arg2 v1 v2 v⟩ s'''
    ∧ ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod2,
    ReachingStar.MultiplierImpl.rule_mulStep, ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hr hm
  split at hr <;> simp_all

@[local grind →] theorem reconverge_mulStepFast_put (s s' s'' : ReachingStar.MultiplierImpl.State)
    (v1 v2 : BitVec 32) (v : unit_) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.put, Footprint.arg2 v1 v2 v⟩ s'''
    ∧ ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod2,
    ReachingStar.MultiplierImpl.rule_mulStepFast, ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hr hm
  split at hr <;> simp_all

@[local grind →] theorem reconverge_mulStep_getA (s s' s'' : ReachingStar.MultiplierImpl.State) (v : unit_) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getA, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStep, ReachingStar.MultiplierImpl.meth_getA,
    ReachingStar.MultiplierImpl.meth_RDY_getA] at hr hm
  split at hr <;> simp_all

@[local grind →] theorem reconverge_mulStepFast_getA (s s' s'' : ReachingStar.MultiplierImpl.State) (v : unit_) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getA, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStepFast, ReachingStar.MultiplierImpl.meth_getA,
    ReachingStar.MultiplierImpl.meth_RDY_getA] at hr hm
  split at hr <;> simp_all

@[local grind →] theorem reconverge_mulStep_getV (s s' s'' : ReachingStar.MultiplierImpl.State) (v : Nat) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getV, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStep, ReachingStar.MultiplierImpl.meth_getV,
    ReachingStar.MultiplierImpl.meth_RDY_getV] at hr hm
  obtain ⟨w, hm_action, hm_fp, hm_ready⟩ := hm
  injection hm_action with _ hm_state
  subst s''
  split at hr
  · rename_i hrcond
    split at hm_ready
    · rename_i hmcond
      omega
    · simp_all
  · simp_all

@[local grind →] theorem reconverge_mulStepFast_getV (s s' s'' : ReachingStar.MultiplierImpl.State) (v : Nat) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getV, Footprint.arg0 v⟩ s'''
    ∧ ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  exfalso
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStepFast, ReachingStar.MultiplierImpl.meth_getV,
    ReachingStar.MultiplierImpl.meth_RDY_getV] at hr hm
  obtain ⟨w, hm_action, hm_fp, hm_ready⟩ := hm
  injection hm_action with _ hm_state
  subst s''
  split at hr
  · rename_i hrcond
    split at hm_ready
    · rename_i hmcond
      omega
    · simp_all
  · simp_all


inductive flush : ImplModule.State → SpecModule.State → Prop where
| intro {a b prod carry step busy} :
    (busy = true → step = ReachingStar.MultiplierImpl.width) →
    flush { a := a, b := b, prod := prod, carry := carry, step := step, busy := busy }
           { result := prod, busy := busy }

@[local grind →] theorem flush_indistinguishable_put (i i' : ImplModule.State) (s : SpecModule.State)
    (v1 v2 : BitVec 32) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.put, Footprint.arg2 v1 v2 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod2,
    ReachingStar.MultiplierSpec.meth_put, ReachingStar.MultiplierSpec.meth_RDY_put,
    ReachingStar.MultiplierImpl.meth_put, ReachingStar.MultiplierImpl.meth_RDY_put] at hm ⊢
  cases v
  grind

@[local grind →] theorem flush_indistinguishable_getA (i i' : ImplModule.State) (s : SpecModule.State) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.getA, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.MultiplierSpec.meth_getA, ReachingStar.MultiplierSpec.meth_RDY_getA,
    ReachingStar.MultiplierImpl.meth_getA, ReachingStar.MultiplierImpl.meth_RDY_getA] at hm ⊢
  cases v
  grind

@[local grind →] theorem flush_indistinguishable_getV (i i' : ImplModule.State) (s : SpecModule.State) (v : Nat) :
  flush i s →
  ImplModule.getMethod i ⟨.getV, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.MultiplierSpec.meth_getV, ReachingStar.MultiplierSpec.meth_RDY_getV,
    ReachingStar.MultiplierImpl.meth_getV, ReachingStar.MultiplierImpl.meth_RDY_getV] at hm ⊢
  grind

@[local grind →] theorem reach_flush_again_getA (i i' : ImplModule.State) (s s' : SpecModule.State) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.getA, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf hm hs
  cases hf with
  | intro hcond =>
    dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
      ReachingStar.MultiplierSpec.meth_getA, ReachingStar.MultiplierSpec.meth_RDY_getA,
      ReachingStar.MultiplierImpl.meth_getA, ReachingStar.MultiplierImpl.meth_RDY_getA] at hm hs
    cases v
    obtain ⟨_, hm_action, hm_fp, hm_rdy⟩ := hm
    cases hm_fp
    obtain ⟨_, hs_action, hs_fp, _⟩ := hs
    cases hs_fp
    refine ⟨_, Relation.ReflTransGen.refl, ?_⟩
    injection hm_action with _ hm_state
    injection hs_action with _ hs_state
    rw [← hm_state, ← hs_state]
    exact flush.intro (by simp)

@[local grind →] theorem reach_flush_again_getV (i i' : ImplModule.State) (s s' : SpecModule.State) (v : Nat) :
  flush i s →
  ImplModule.getMethod i ⟨.getV, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf hm hs
  cases hf with
  | intro hcond =>
    dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
      ReachingStar.MultiplierSpec.meth_getV, ReachingStar.MultiplierSpec.meth_RDY_getV,
      ReachingStar.MultiplierImpl.meth_getV, ReachingStar.MultiplierImpl.meth_RDY_getV] at hm hs
    obtain ⟨wm, hm_action, hm_fp, hm_ready⟩ := hm
    obtain ⟨ws, hs_action, hs_fp, hs_ready⟩ := hs
    injection hm_action with _ hm_state
    injection hs_action with _ hs_state
    -- `getV` doesn't change state at all, on either side.
    refine ⟨i', Relation.ReflTransGen.refl, ?_⟩
    rw [← hm_state, ← hs_state]
    exact flush.intro hcond



private def mulInv (result : Nat) (s : ImplModule.State) : Prop :=
  ∃ lo,
    s.busy = true ∧
    s.step ≤ ReachingStar.MultiplierImpl.width ∧
    s.prod = lo * ReachingStar.MultiplierImpl.base ^
      (ReachingStar.MultiplierImpl.width - s.step) ∧
    lo < ReachingStar.MultiplierImpl.base ^ s.step ∧
    result =
      (lo + ReachingStar.MultiplierImpl.base ^ s.step *
        (s.carry + s.a * s.b)) % ReachingStar.MultiplierImpl.modulus ∧
    (s.a = 0 → lo = 0 ∧ s.carry = 0)

private theorem topPlace_eq_pow :
    ReachingStar.MultiplierImpl.topPlace =
      ReachingStar.MultiplierImpl.base ^
        (ReachingStar.MultiplierImpl.width - 1) := by
  rfl

private theorem radix_value_step (a b carry lo k : Nat) :
    lo + (a * (b % ReachingStar.MultiplierImpl.base) + carry) %
          ReachingStar.MultiplierImpl.base *
          ReachingStar.MultiplierImpl.base ^ k +
        ReachingStar.MultiplierImpl.base ^ (k + 1) *
          ((a * (b % ReachingStar.MultiplierImpl.base) + carry) /
              ReachingStar.MultiplierImpl.base +
            a * (b / ReachingStar.MultiplierImpl.base)) =
      lo + ReachingStar.MultiplierImpl.base ^ k * (carry + a * b) := by
  calc
    _ = lo + ReachingStar.MultiplierImpl.base ^ k *
        ((a * (b % ReachingStar.MultiplierImpl.base) + carry) %
            ReachingStar.MultiplierImpl.base +
          ReachingStar.MultiplierImpl.base *
            ((a * (b % ReachingStar.MultiplierImpl.base) + carry) /
              ReachingStar.MultiplierImpl.base) +
          ReachingStar.MultiplierImpl.base * a *
            (b / ReachingStar.MultiplierImpl.base)) := by
          rw [pow_succ]
          ring
    _ = lo + ReachingStar.MultiplierImpl.base ^ k *
        (a * (b % ReachingStar.MultiplierImpl.base) + carry +
          ReachingStar.MultiplierImpl.base * a *
            (b / ReachingStar.MultiplierImpl.base)) := by
          rw [Nat.mod_add_div]
    _ = lo + ReachingStar.MultiplierImpl.base ^ k *
        (carry + a *
          (b % ReachingStar.MultiplierImpl.base +
            ReachingStar.MultiplierImpl.base *
              (b / ReachingStar.MultiplierImpl.base))) := by
          ring
    _ = lo + ReachingStar.MultiplierImpl.base ^ k * (carry + a * b) := by
          rw [Nat.mod_add_div]

private theorem radix_prod_step (lo digit k : Nat)
    (hk : k < ReachingStar.MultiplierImpl.width) :
    digit * ReachingStar.MultiplierImpl.topPlace +
        (lo * ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - k)) /
          ReachingStar.MultiplierImpl.base =
      (lo + digit * ReachingStar.MultiplierImpl.base ^ k) *
        ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - (k + 1)) := by
  have h₁ : ReachingStar.MultiplierImpl.width - k =
      (ReachingStar.MultiplierImpl.width - (k + 1)) + 1 := by omega
  have h₂ : ReachingStar.MultiplierImpl.width - 1 =
      k + (ReachingStar.MultiplierImpl.width - (k + 1)) := by omega
  rw [topPlace_eq_pow, h₁, h₂, pow_add, pow_succ]
  rw [show lo *
      (ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - (k + 1)) *
        ReachingStar.MultiplierImpl.base) =
      (lo * ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - (k + 1))) *
        ReachingStar.MultiplierImpl.base by
        simp [mul_assoc]]
  have hcancel :
      (lo * ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - (k + 1))) *
          ReachingStar.MultiplierImpl.base /
          ReachingStar.MultiplierImpl.base =
        lo * ReachingStar.MultiplierImpl.base ^
          (ReachingStar.MultiplierImpl.width - (k + 1)) := by
    simp only [ReachingStar.MultiplierImpl.base]
    omega
  rw [hcancel]
  ring

private theorem radix_lo_bound (lo digit k : Nat)
    (hlo : lo < ReachingStar.MultiplierImpl.base ^ k)
    (hdigit : digit < ReachingStar.MultiplierImpl.base) :
    lo + digit * ReachingStar.MultiplierImpl.base ^ k <
      ReachingStar.MultiplierImpl.base ^ (k + 1) := by
  simp only [ReachingStar.MultiplierImpl.base] at hlo hdigit ⊢
  interval_cases digit <;> simp_all [pow_succ] <;> omega

private theorem mulInv_initial (v1 v2 : Nat) :
    mulInv ((v1 * v2) % ReachingStar.MultiplierImpl.modulus)
      { a := v1, b := v2, prod := 0, carry := 0, step := 0, busy := true } := by
  refine ⟨0, rfl, by simp, ?_, by simp [ReachingStar.MultiplierImpl.base], ?_, ?_⟩
  · simp
  · simp [ReachingStar.MultiplierImpl.base]
  · intro h
    exact ⟨rfl, rfl⟩

private theorem mulInv_done {result : Nat} {s : ImplModule.State}
    (hi : mulInv result s)
    (hdone : s.step = ReachingStar.MultiplierImpl.width) :
    s.prod = result := by
  obtain ⟨lo, -, -, hprod, hlo, hresult, -⟩ := hi
  rw [hdone] at hprod hlo hresult
  simp only [Nat.sub_self, pow_zero, mul_one] at hprod
  rw [hprod]
  have hresult' : result = lo := by
    simpa [ReachingStar.MultiplierImpl.modulus,
      Nat.mod_eq_of_lt hlo, Nat.add_mul_mod_self_left] using hresult
  exact hresult'.symm

private theorem mulInv_step {result : Nat} {s : ImplModule.State}
    (hi : mulInv result s)
    (hlt : s.step < ReachingStar.MultiplierImpl.width) :
    ∃ s', ImplModule.getARule s s' ∧ mulInv result s' := by
  obtain ⟨lo, hbusy, hle, hprod, hlo, hresult, hzero⟩ := hi
  by_cases ha : s.a = 0
  · let s' : ImplModule.State :=
      { s with prod := s.a, step := ReachingStar.MultiplierImpl.width }
    refine ⟨s', ?_, ?_⟩
    · refine ⟨.mulStepFast, ?_⟩
      dsimp [ImplModule, Module.getRule, ofRule,
        ReachingStar.MultiplierImpl.rule_mulStepFast, s']
      simp [hbusy, ha, hlt]
    · obtain ⟨hlo0, hcarry0⟩ := hzero ha
      have hresult0 : result = 0 := by
        simpa [ha, hlo0, hcarry0] using hresult
      refine ⟨0, by simp [s', hbusy], by simp [s'], ?_, ?_, ?_, ?_⟩
      · simp [s', ha]
      · norm_num [s', ReachingStar.MultiplierImpl.base,
          ReachingStar.MultiplierImpl.width]
      · rw [hresult0]
        simp [s', ha, hcarry0]
      · intro
        exact ⟨rfl, by simpa [hcarry0]⟩
  · let digit := ReachingStar.MultiplierImpl.stepSum s %
      ReachingStar.MultiplierImpl.base
    let lo' := lo + digit * ReachingStar.MultiplierImpl.base ^ s.step
    let s' : ImplModule.State :=
      { a := s.a
      , b := s.b / ReachingStar.MultiplierImpl.base
      , prod := digit * ReachingStar.MultiplierImpl.topPlace +
          s.prod / ReachingStar.MultiplierImpl.base
      , carry := ReachingStar.MultiplierImpl.stepSum s /
          ReachingStar.MultiplierImpl.base
      , step := s.step + 1
      , busy := s.busy }
    refine ⟨s', ?_, ?_⟩
    · refine ⟨.mulStep, ?_⟩
      dsimp [ImplModule, Module.getRule, ofRule,
        ReachingStar.MultiplierImpl.rule_mulStep, s', digit]
      simp [hbusy, ha, hlt]
    · refine ⟨lo', by simp [s', hbusy], by simp [s']; omega, ?_, ?_, ?_, ?_⟩
      · dsimp [s', lo', digit]
        rw [hprod]
        exact radix_prod_step lo
          (ReachingStar.MultiplierImpl.stepSum s %
            ReachingStar.MultiplierImpl.base) s.step hlt
      · dsimp [lo', digit]
        apply radix_lo_bound
        · exact hlo
        · exact Nat.mod_lt _ (by
            simp [ReachingStar.MultiplierImpl.base])
      · dsimp [s', lo', digit]
        rw [hresult]
        apply congrArg (fun x => x % ReachingStar.MultiplierImpl.modulus)
        simpa [ReachingStar.MultiplierImpl.stepSum,
          ReachingStar.MultiplierImpl.bit0] using
          (radix_value_step s.a s.b s.carry lo s.step).symm
      · intro ha'
        exact (ha ha').elim

private theorem rule_measure_decreases {s s' : ImplModule.State}
    (hr : ImplModule.getARule s s') :
    ReachingStar.MultiplierImpl.width - s'.step <
      ReachingStar.MultiplierImpl.width - s.step := by
  rcases ImplModule.get_rule_cases hr with hr | hr
  · dsimp [ImplModule, Module.getRule, ofRule,
      ReachingStar.MultiplierImpl.rule_mulStep] at hr
    split at hr
    · rename_i hcond
      obtain ⟨-, -, hlt⟩ := hcond
      injection hr with _ hstate
      subst s'
      dsimp
      omega
    · simp_all
  · dsimp [ImplModule, Module.getRule, ofRule,
      ReachingStar.MultiplierImpl.rule_mulStepFast] at hr
    split at hr
    · rename_i hcond
      obtain ⟨-, -, hlt⟩ := hcond
      injection hr with _ hstate
      subst s'
      dsimp
      omega
    · simp_all

private theorem mulInv_reaches_done {result : Nat} {s : ImplModule.State}
    (hi : mulInv result s) :
    ∃ t, Relation.ReflTransGen ImplModule.getARule s t ∧
      t.step = ReachingStar.MultiplierImpl.width ∧ mulInv result t := by
  let P : Nat → Prop := fun n =>
    ∀ u : ImplModule.State,
      ReachingStar.MultiplierImpl.width - u.step = n →
      mulInv result u →
      ∃ t, Relation.ReflTransGen ImplModule.getARule u t ∧
        t.step = ReachingStar.MultiplierImpl.width ∧ mulInv result t
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [P]
        intro u hmeasure hiu
        have hiu_copy := hiu
        obtain ⟨-, -, hle, -, -, -, -⟩ := hiu_copy
        by_cases hdone : u.step = ReachingStar.MultiplierImpl.width
        · exact ⟨u, Relation.ReflTransGen.refl, hdone, hiu⟩
        · have hlt : u.step < ReachingStar.MultiplierImpl.width := by omega
          obtain ⟨u₁, hu₁, hi₁⟩ := mulInv_step hiu hlt
          have hdec : ReachingStar.MultiplierImpl.width - u₁.step < n := by
            rw [← hmeasure]
            exact rule_measure_decreases hu₁
          obtain ⟨t, hstar, ht, hit⟩ :=
            ih (ReachingStar.MultiplierImpl.width - u₁.step) hdec u₁ rfl hi₁
          exact ⟨t, Relation.ReflTransGen.head hu₁ hstar, ht, hit⟩
  exact hP (ReachingStar.MultiplierImpl.width - s.step) s rfl hi

@[local grind →] theorem reach_flush_again_put (i i' : ImplModule.State) (s s' : SpecModule.State)
    (v1 v2 : BitVec 32) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.put, Footprint.arg2 v1 v2 v⟩ i' →
  SpecModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro _ hm hs
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod2,
    ReachingStar.MultiplierSpec.meth_put, ReachingStar.MultiplierSpec.meth_RDY_put,
    ReachingStar.MultiplierImpl.meth_put, ReachingStar.MultiplierImpl.meth_RDY_put] at hm hs
  cases v
  obtain ⟨iw1, iw2, iv, hm_action, hm_fp, -⟩ := hm
  cases hm_fp
  obtain ⟨sw1, sw2, sv, hs_action, hs_fp, -⟩ := hs
  cases hs_fp
  injection hm_action with _ hm_state
  injection hs_action with _ hs_state
  have hreach := mulInv_reaches_done (mulInv_initial v1.toNat v2.toNat)
  obtain ⟨t, hstar, hstep, hinv⟩ := hreach
  have hprod := mulInv_done hinv hstep
  refine ⟨t, ?_, ?_⟩
  · rw [← hm_state]
    exact hstar
  · have hbusy : t.busy = true := by
      obtain ⟨-, hb, -⟩ := hinv
      exact hb
    have htflush : flush t
        { result := (v1.toNat * v2.toNat) % ReachingStar.MultiplierSpec.modulus
        , busy := true } := by
      rw [show ReachingStar.MultiplierSpec.modulus =
        ReachingStar.MultiplierImpl.modulus by rfl]
      rw [← hprod, ← hbusy]
      exact flush.intro (by intro; exact hstep)
    rw [← hs_state]
    exact htflush

@[local grind →] theorem flush_reaches_flush_rule (r : Rule) (i i' : ImplModule.State) (s : SpecModule.State) :
  flush i s → ImplModule.getRule r i i' → flush i' s := by
  intro hf hr
  cases hf with
  | intro hcond =>
    cases r <;>
      · dsimp [ImplModule, Module.getRule, ofRule,
          ReachingStar.MultiplierImpl.rule_mulStep,
          ReachingStar.MultiplierImpl.rule_mulStepFast] at hr
        split at hr <;> simp_all

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  intro s
  let P : Nat → Prop := fun n =>
    ∀ u : ImplModule.State,
      ReachingStar.MultiplierImpl.width - u.step = n →
      strongly_normalising' ImplModule.getARule u
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [P]
        intro u hmeasure
        apply strongly_normalising'.step
        intro u' hr
        have hdec : ReachingStar.MultiplierImpl.width - u'.step < n := by
          rw [← hmeasure]
          exact rule_measure_decreases hr
        exact ih (ReachingStar.MultiplierImpl.width - u'.step) hdec u' rfl
  exact hP (ReachingStar.MultiplierImpl.width - s.step) s rfl


attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

def multiplier_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := flush
  rules_strongly_normalising := rules_strongly_normalising


theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind flush multiplier_refinement.impl.getARule i s ->
  star_extend multiplier_refinement.impl.getARule multiplier_refinement.impl.getMethod i l i' ->
  ∃ s', star multiplier_refinement.spec.getMethod s l s'
        ∧ φ_ind multiplier_refinement.flushed multiplier_refinement.impl.getARule i' s' := enough_star multiplier_refinement


def weakBisimulationRel (i : ImplModule.State) (s : SpecModule.State) : Prop :=
  φ_ind flush ImplModule.getARule i s

structure IsWeakBisimulation
    (R : ImplModule.State → SpecModule.State → Prop) : Prop where
  impl_internal :
    ∀ {i i' s}, R i s → ImplModule.getARule i i' → R i' s
  impl_observable :
    ∀ {i i' s e}, R i s → ImplModule.getMethod i e i' →
      ∃ s', SpecModule.getMethod s e s' ∧ R i' s'
  spec_observable :
    ∀ {i s s' e}, R i s → SpecModule.getMethod s e s' →
      ∃ i₀ i', trans_refl ImplModule.getARule i i₀ ∧
        ImplModule.getMethod i₀ e i' ∧ R i' s'

private theorem trans_refl_append {a b c : ImplModule.State}
    (hab : trans_refl ImplModule.getARule a b)
    (hbc : trans_refl ImplModule.getARule b c) :
    trans_refl ImplModule.getARule a c := by
  apply trans_refl_equiv.mpr
  exact (trans_refl_equiv.mp hab).trans (trans_refl_equiv.mp hbc)

private theorem weakBisimulationRel_reaches_flush
    {i : ImplModule.State} {s : SpecModule.State}
    (hrel : weakBisimulationRel i s) :
    ∃ f, trans_refl ImplModule.getARule i f ∧ flush f s := by
  induction hrel with
  | base i s hf =>
      exact ⟨i, trans_refl.refl, hf⟩
  | rule_step i i' s _ hpath ih =>
      obtain ⟨f, hi'f, hf⟩ := ih
      exact ⟨f, trans_refl_append hpath hi'f, hf⟩

private theorem flush_matches_spec_method
    {i : ImplModule.State} {s s' : SpecModule.State} {e : Event Method}
    (hf : flush i s) (hs : SpecModule.getMethod s e s') :
    ∃ i', ImplModule.getMethod i e i' := by
  cases hf with
  | intro hdone =>
      obtain ⟨name, footprint⟩ := e
      cases name <;>
        dsimp [SpecModule, ImplModule, Module.getMethod,
          ofAVMethod0, ofAVMethod2,
          ReachingStar.MultiplierSpec.meth_put,
          ReachingStar.MultiplierSpec.meth_RDY_put,
          ReachingStar.MultiplierSpec.meth_getA,
          ReachingStar.MultiplierSpec.meth_RDY_getA,
          ReachingStar.MultiplierSpec.meth_getV,
          ReachingStar.MultiplierSpec.meth_RDY_getV,
          ReachingStar.MultiplierImpl.meth_put,
          ReachingStar.MultiplierImpl.meth_RDY_put,
          ReachingStar.MultiplierImpl.meth_getA,
          ReachingStar.MultiplierImpl.meth_RDY_getA,
          ReachingStar.MultiplierImpl.meth_getV,
          ReachingStar.MultiplierImpl.meth_RDY_getV] at hs ⊢ <;>
        grind

private theorem weakBisimulationRel_impl_internal
    {i i' : ImplModule.State} {s : SpecModule.State}
    (hrel : weakBisimulationRel i s)
    (hr : ImplModule.getARule i i') :
    weakBisimulationRel i' s := by
  have htrace :
      star_extend ImplModule.getARule ImplModule.getMethod i [] i' := by
    apply star_extend.step_int
    · exact star_extend.refl i
    · exact trans_refl.step hr trans_refl.refl
  obtain ⟨s', hs', hrel'⟩ := refines hrel htrace
  cases hs'
  exact hrel'

private theorem weakBisimulationRel_impl_observable
    {i i' : ImplModule.State} {s : SpecModule.State} {e : Event Method}
    (hrel : weakBisimulationRel i s)
    (hm : ImplModule.getMethod i e i') :
    ∃ s', SpecModule.getMethod s e s' ∧ weakBisimulationRel i' s' := by
  have htrace :
      star_extend ImplModule.getARule ImplModule.getMethod i [e] i' := by
    apply star_extend.step_ext
    · exact star_extend.refl i
    · exact hm
  obtain ⟨s', hs', hrel'⟩ := refines hrel htrace
  cases hs'
  rename_i s₂ hprefix hspec
  cases hprefix
  exact ⟨s', hspec, hrel'⟩

private theorem weakBisimulationRel_spec_observable
    {i : ImplModule.State} {s s' : SpecModule.State} {e : Event Method}
    (hrel : weakBisimulationRel i s)
    (hs : SpecModule.getMethod s e s') :
    ∃ i₀ i', trans_refl ImplModule.getARule i i₀ ∧
      ImplModule.getMethod i₀ e i' ∧ weakBisimulationRel i' s' := by
  obtain ⟨i₀, hi₀, hf⟩ := weakBisimulationRel_reaches_flush hrel
  obtain ⟨i', hm⟩ := flush_matches_spec_method hf hs
  obtain ⟨f, hi'f, hff⟩ :=
    multiplier_refinement.flushed_method_preserved hf hm hs
  have hi'f' : trans_refl ImplModule.getARule i' f :=
    trans_refl_equiv.mpr hi'f
  refine ⟨i₀, i', hi₀, hm, ?_⟩
  exact φ_ind.rule_step i' f s' (φ_ind.base f s' hff) hi'f'

theorem multiplier_weak_bisimulation :
    IsWeakBisimulation weakBisimulationRel where
  impl_internal := weakBisimulationRel_impl_internal
  impl_observable := weakBisimulationRel_impl_observable
  spec_observable := weakBisimulationRel_spec_observable

theorem spec_trace_is_implementable
    {i : ImplModule.State} {s s' : SpecModule.State} {l : List (Event Method)}
    (hrel : weakBisimulationRel i s)
    (hs : star SpecModule.getMethod s l s') :
    ∃ i', star_extend ImplModule.getARule ImplModule.getMethod i l i' ∧
      weakBisimulationRel i' s' := by
  induction hs generalizing i with
  | refl =>
      exact ⟨i, star_extend.refl i, hrel⟩
  | step s₁ s₂ l e hprefix hm ih =>
      obtain ⟨i₁, htrace, hrel₁⟩ := ih hrel
      obtain ⟨i₂, i₃, hi₁i₂, hi₂i₃, hrel₃⟩ :=
        multiplier_weak_bisimulation.spec_observable hrel₁ hm
      have htrace₂ :
          star_extend ImplModule.getARule ImplModule.getMethod i l i₂ :=
        star_extend.step_int i l i₁ i₂ htrace hi₁i₂
      exact ⟨i₃,
        star_extend.step_ext i l i₂ i₃ e htrace₂ hi₂i₃,
        hrel₃⟩

theorem correctness_by_weak_bisimulation :
    (∀ {i i' s l}, weakBisimulationRel i s →
      star_extend ImplModule.getARule ImplModule.getMethod i l i' →
      ∃ s', star SpecModule.getMethod s l s' ∧
        weakBisimulationRel i' s') ∧
    (∀ {i s s' l}, weakBisimulationRel i s →
      star SpecModule.getMethod s l s' →
      ∃ i', star_extend ImplModule.getARule ImplModule.getMethod i l i' ∧
        weakBisimulationRel i' s') := by
  constructor
  · intro i i' s l hrel htrace
    exact refines hrel htrace
  · intro i s s' l hrel htrace
    exact spec_trace_is_implementable hrel htrace

/-- info: 'ReachingStar.Bluespec.Multiplier.correctness_by_weak_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms correctness_by_weak_bisimulation

/-- info: 'ReachingStar.Bluespec.Multiplier.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refines
end ReachingStar.Bluespec.Multiplier
