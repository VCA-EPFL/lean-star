/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import NFI

open BluespecPrelude
open BluespecVerification
open ReachingStar.Security

namespace ReachingStar.MultiplierParams
/-! ## Parameters -/

/-- The base the multiplier counts in. -/
def base  : Nat := 2

/-- The number of digits of the operands, here bits. -/
def width : Nat := 8

end ReachingStar.MultiplierParams

namespace ReachingStar.MultiplierSpec

/-- The externally observable state of the specification. -/
structure State where
  /-- The result of the multiplication. -/
  result : Nat
  /-- Whether a computation is in progress. -/
  busy   : Bool

/-- The operand width of the specification. -/
def width   : Nat := ReachingStar.MultiplierParams.width

/-- The base of the specification. -/
def base    : Nat := ReachingStar.MultiplierParams.base

/-- The modulus: the computation is done in `ℤ/(base^width)ℤ`. -/
def modulus : Nat := base ^ width

/-- Specification of `put`: stores the product of the operands and sets `busy`.

Arguments:
* `_`: the current state, ignored.
* `v1`: the first operand.
* `v2`: the second operand. -/
def meth_put (_ : State) (v1 v2 : BitVec width) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { result := (v1.toNat * v2.toNat) % modulus, busy := true } }

/-- Guard of `put`: ready when not busy.

Arguments:
* `s`: the current state. -/
def meth_RDY_put (s : State) : t_bool :=
  if s.busy then BFalse Unit_ else BTrue Unit_

/-- Specification of `getV`: returns the result and keeps the state.

Arguments:
* `s`: the current state. -/
def meth_getV (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.result
  , avAction_ := s }

/-- Guard of `getV`: ready when busy.

Arguments:
* `s`: the current state. -/
def meth_RDY_getV (s : State) : t_bool :=
  if s.busy then BTrue Unit_ else BFalse Unit_

/-- Specification of `getA`: acknowledges the result and clears `busy`.

Arguments:
* `s`: the current state. -/
def meth_getA (s : State) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { s with busy := false } }

/-- Guard of `getA`: ready when busy.

Arguments:
* `s`: the current state. -/
def meth_RDY_getA (s : State) : t_bool :=
  if s.busy then BTrue Unit_ else BFalse Unit_

end ReachingStar.MultiplierSpec

namespace ReachingStar.MultiplierImpl

/-- The internal state of the iterative implementation. -/
structure State where
  /-- The first operand. -/
  a     : Nat
  /-- The second operand, consumed digit by digit. -/
  b     : Nat
  /-- The intermediate product. -/
  prod  : Nat
  /-- The intermediate carry. -/
  carry : Nat
  /-- The step counter. -/
  step  : Nat
  /-- Whether a computation is in progress. -/
  busy  : Bool

/-- The operand width of the implementation. -/
def width    : Nat := ReachingStar.MultiplierParams.width

/-- The base of the implementation. -/
def base     : Nat := ReachingStar.MultiplierParams.base

/-- The modulus: the computation is done in `ℤ/(base^width)ℤ`. -/
def modulus  : Nat := base ^ width

/-- The weight of the most significant digit. -/
def topPlace : Nat := modulus / base

/-- The lowest digit of a number.

Arguments:
* `x`: the number. -/
def unit_place (x : Nat) : Nat := x % base

/-- The first operand multiplied by the lowest digit of `b`.

Arguments:
* `s`: the current state. -/
def selected (s : State) : Nat := s.a * unit_place s.b

/-- `selected` plus the carry of the previous step.

Arguments:
* `s`: the current state. -/
def stepSum (s : State) : Nat := selected s + s.carry

/-! ## Methods -/

/-- Implementation of `put`: stores the operands and starts the computation.

Arguments:
* `_`: the current state, ignored.
* `v1`: the first operand.
* `v2`: the second operand. -/
def meth_put (_ : State) (v1 v2 : BitVec width) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ :=
      { a := v1.toNat
      , b := v2.toNat
      , prod := 0
      , carry := 0
      , step := 0
      , busy := true } }

/-- Guard of `put`: ready when not busy.

Arguments:
* `s`: the current state. -/
def meth_RDY_put (s : State) : t_bool :=
  if s.busy then BFalse Unit_ else BTrue Unit_

/-- Implementation of `getV`: returns the product and keeps the state.

Arguments:
* `s`: the current state. -/
def meth_getV (s : State) : t_actionvalue_ Nat State :=
  { avValue_ := s.prod
  , avAction_ := s }

/-- Guard of `getV`: ready when the computation is finished.

Arguments:
* `s`: the current state. -/
def meth_RDY_getV (s : State) : t_bool :=
  if s.busy ∧ s.step = width then BTrue Unit_ else BFalse Unit_

/-- Implementation of `getA`: clears `busy`.

Arguments:
* `s`: the current state. -/
def meth_getA (s : State) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_
  , avAction_ := { s with busy := false } }

/-- Guard of `getA`: ready when the computation is finished.

Arguments:
* `s`: the current state. -/
def meth_RDY_getA (s : State) : t_bool :=
  if s.busy ∧ s.step = width then BTrue Unit_ else BFalse Unit_

/-! ## Rules -/

/-- One step of the iterative multiplication, when `a ≠ 0`. It returns whether the rule fires and
the next state.

Arguments:
* `s`: the current state. -/
def rule_mulStep (s : State) : t_bool × State :=
  if s.busy ∧ s.a ≠ 0 ∧ s.step < width then
    (BTrue Unit_,
      { s with
        b := s.b / base
        prod := (stepSum s % base) * topPlace + s.prod / base
        carry := stepSum s / base
        step := s.step + 1 })
  else (BFalse Unit_, s)

/-- The shortcut when `a = 0`: it finishes the computation at once. It returns whether the rule
fires and the next state.

Arguments:
* `s`: the current state. -/
def rule_mulStepFast (s : State) : t_bool × State :=
  if s.busy ∧ s.a = 0 ∧ s.step < width then
    (BTrue Unit_, { s with prod := s.a, step := width })
  else (BFalse Unit_, s)

end ReachingStar.MultiplierImpl

namespace ReachingStar.Bluespec.Multiplier

/-- The operand width is positive.

Proof: By computation. -/
private theorem width_pos : 0 < ReachingStar.MultiplierImpl.width := by
  simp [ReachingStar.MultiplierImpl.width, ReachingStar.MultiplierParams.width]

/-- The method names of the multiplier. -/
@[grind cases]
inductive Method : Type where
/-- Starts a multiplication. -/
| put
/-- Acknowledges the result. -/
| getA
/-- Returns the result. -/
| getV

/-- The rule names of the implementation. -/
@[grind cases]
inductive Rule : Type where
/-- One step of the iteration. -/
| mulStep
/-- The shortcut when `a = 0`. -/
| mulStepFast

/-- The specification of the multiplier: its methods compute the product in one step, and it has no
rules. -/
def SpecModule : Bluespec.Module Empty Method where
  State := ReachingStar.MultiplierSpec.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierSpec.meth_put
        ReachingStar.MultiplierSpec.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierSpec.meth_getA
        ReachingStar.MultiplierSpec.meth_RDY_getA
    | .getV => ofAVMethod0 ReachingStar.MultiplierSpec.meth_getV
        ReachingStar.MultiplierSpec.meth_RDY_getV
  rules := Empty.casesOn _

/-- The implementation of the multiplier: `put` starts an iteration that the rules run. -/
def ImplModule : Bluespec.Module Rule Method where
  State := ReachingStar.MultiplierImpl.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierImpl.meth_put
        ReachingStar.MultiplierImpl.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getA
        ReachingStar.MultiplierImpl.meth_RDY_getA
    | .getV => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getV
        ReachingStar.MultiplierImpl.meth_RDY_getV
  rules
    | .mulStep => ofRule ReachingStar.MultiplierImpl.rule_mulStep
    | .mulStepFast => ofRule ReachingStar.MultiplierImpl.rule_mulStepFast

/-! ## Inversion lemmas -/

/-- Inversion on methods: a method step is a `put` with two arguments, a `getA` or a `getV`.

Arguments:
* `i`, `i'`: the start and end states.
* `e`: the label.

Proof: By cases on the method name. -/
@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_),
      e.1 = .put ∧ e.2 = Footprint.arg2 v1 v2 v) ∨
    (∃ (v : unit_), e.1 = .getA ∧ e.2 = Footprint.arg0 v) ∨
    (∃ (v : Nat), e.1 = .getV ∧ e.2 = Footprint.arg0 v) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;>
    (dsimp [ImplModule, Module.getMethod, ofAVMethod0, ofAVMethod2] at *; grind)

/-- Inversion on rules: a rule step fires `mulStep` or `mulStepFast`.

Arguments:
* `i`, `i'`: the start and end states.

Proof: By cases on the rule name. -/
@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .mulStep i i' ∨ ImplModule.getRule .mulStepFast i i' := by
  intro h
  obtain ⟨r, hr⟩ := h
  cases r
  · exact Or.inl hr
  · exact Or.inr hr

/-! ## Local confluence: two rule firings can always be rejoined -/

/-- Two `mulStep` steps from one state rejoin.

Arguments:
* `a`: the common start state.
* `b`, `c`: the two end states.

Proof: The rule is deterministic, so `b = c`. -/
@[local grind →] theorem commutes_mulStep_mulStep {a b c : ImplModule.State} :
  ImplModule.getRule .mulStep a c →
  ImplModule.getRule .mulStep a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧
    Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hcb : c = b := by
    dsimp [ImplModule, Module.getRule, ofRule,
      ReachingStar.MultiplierImpl.rule_mulStep] at hc hb
    split at hc
    · split at hb
      · injection hc with _ hc'
        injection hb with _ hb'
        rw [← hc', ← hb']
      · contradiction
    · simp at hc
  subst b
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- Two `mulStepFast` steps from one state rejoin.

Arguments:
* `a`: the common start state.
* `b`, `c`: the two end states.

Proof: The rule is deterministic, so `b = c`. -/
@[local grind →] theorem commutes_mulStepFast_mulStepFast {a b c : ImplModule.State} :
  ImplModule.getRule .mulStepFast a c →
  ImplModule.getRule .mulStepFast a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧
    Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hcb : c = b := by
    dsimp [ImplModule, Module.getRule, ofRule,
      ReachingStar.MultiplierImpl.rule_mulStepFast] at hc hb
    split at hc
    · split at hb
      · injection hc with _ hc'
        injection hb with _ hb'
        rw [← hc', ← hb']
      · contradiction
    · simp at hc
  subst b
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- `mulStep` and `mulStepFast` from one state rejoin.

Arguments:
* `a`: the common start state.
* `b`, `c`: the two end states.

Proof: Their guards need `a ≠ 0` and `a = 0`, so they are never both enabled. -/
@[local grind →] theorem commutes_mulStep_mulStepFast {a b c : ImplModule.State} :
  ImplModule.getRule .mulStep a c →
  ImplModule.getRule .mulStepFast a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧
    Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule,
    ReachingStar.MultiplierImpl.rule_mulStep,
    ReachingStar.MultiplierImpl.rule_mulStepFast] at hc hb
  split at hc
  · rename_i hn
    split at hb
    · rename_i hf
      exact (hn.2.1 hf.2.1).elim
    · simp_all
  · simp_all

/-- `mulStepFast` and `mulStep` from one state rejoin.

Arguments:
* `a`: the common start state.
* `b`, `c`: the two end states.

Proof: Their guards need `a = 0` and `a ≠ 0`, so they are never both enabled. -/
@[local grind →] theorem commutes_mulStepFast_mulStep {a b c : ImplModule.State} :
  ImplModule.getRule .mulStepFast a c →
  ImplModule.getRule .mulStep a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧
    Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule,
    ReachingStar.MultiplierImpl.rule_mulStepFast,
    ReachingStar.MultiplierImpl.rule_mulStep] at hc hb
  split at hc
  · rename_i hf
    split at hb
    · rename_i hn
      exact (hn.2.1 hf.2.1).elim
    · simp_all
  · simp_all

/-! ## Reconvergence: the order of a rule and a method does not matter -/

/-- `mulStep` and `put` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v1`, `v2`: the operands of `put`.
* `v`: its return value.

Proof: A rule needs `busy` and `put` needs not `busy`, so they are never both enabled. -/
@[local grind →] theorem reconverge_mulStep_put
    (s s' s'' : ImplModule.State)
    (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.put, Footprint.arg2 v1 v2 v⟩ s''' ∧
    ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod2,
    ReachingStar.MultiplierImpl.rule_mulStep,
    ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, -, -, hready⟩ := hm
    simp [hcond.1] at hready
  · simp_all

/-- `mulStep` and `getA` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v`: the return value of the method.

Proof: A rule needs `step < width` and `getA` needs `step = width`, so they are never both
enabled. -/
@[local grind →] theorem reconverge_mulStep_getA
    (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getA, Footprint.arg0 v⟩ s''' ∧
    ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStep,
    ReachingStar.MultiplierImpl.meth_getA,
    ReachingStar.MultiplierImpl.meth_RDY_getA] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, hready⟩ := hm
    have hne : s.step ≠ ReachingStar.MultiplierImpl.width := by omega
    simp [hcond.1, hne] at hready
  · simp_all

/-- `mulStep` and `getV` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v`: the return value of the method.

Proof: A rule needs `step < width` and `getV` needs `step = width`, so they are never both
enabled. -/
@[local grind →] theorem reconverge_mulStep_getV
    (s s' s'' : ImplModule.State) (v : Nat) :
  ImplModule.getRule .mulStep s s' →
  ImplModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getV, Footprint.arg0 v⟩ s''' ∧
    ImplModule.getRule .mulStep s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStep,
    ReachingStar.MultiplierImpl.meth_getV,
    ReachingStar.MultiplierImpl.meth_RDY_getV] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, hready⟩ := hm
    have hne : s.step ≠ ReachingStar.MultiplierImpl.width := by omega
    simp [hcond.1, hne] at hready
  · simp_all

/-- `mulStepFast` and `put` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v1`, `v2`: the operands of `put`.
* `v`: its return value.

Proof: A rule needs `busy` and `put` needs not `busy`, so they are never both enabled. -/
@[local grind →] theorem reconverge_mulStepFast_put
    (s s' s'' : ImplModule.State)
    (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.put, Footprint.arg2 v1 v2 v⟩ s''' ∧
    ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod2,
    ReachingStar.MultiplierImpl.rule_mulStepFast,
    ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, -, -, hready⟩ := hm
    simp [hcond.1] at hready
  · simp_all

/-- `mulStepFast` and `getA` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v`: the return value of the method.

Proof: A rule needs `step < width` and `getA` needs `step = width`, so they are never both
enabled. -/
@[local grind →] theorem reconverge_mulStepFast_getA
    (s s' s'' : ImplModule.State) (v : unit_) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getA, Footprint.arg0 v⟩ s''' ∧
    ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStepFast,
    ReachingStar.MultiplierImpl.meth_getA,
    ReachingStar.MultiplierImpl.meth_RDY_getA] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, hready⟩ := hm
    have hne : s.step ≠ ReachingStar.MultiplierImpl.width := by omega
    simp [hcond.1, hne] at hready
  · simp_all

/-- `mulStepFast` and `getV` from one state commute.

Arguments:
* `s`: the common start state.
* `s'`: the end state of the rule.
* `s''`: the end state of the method.
* `v`: the return value of the method.

Proof: A rule needs `step < width` and `getV` needs `step = width`, so they are never both
enabled. -/
@[local grind →] theorem reconverge_mulStepFast_getV
    (s s' s'' : ImplModule.State) (v : Nat) :
  ImplModule.getRule .mulStepFast s s' →
  ImplModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.getV, Footprint.arg0 v⟩ s''' ∧
    ImplModule.getRule .mulStepFast s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0,
    ReachingStar.MultiplierImpl.rule_mulStepFast,
    ReachingStar.MultiplierImpl.meth_getV,
    ReachingStar.MultiplierImpl.meth_RDY_getV] at hr hm
  split at hr
  · rename_i hcond
    obtain ⟨-, -, -, hready⟩ := hm
    have hne : s.step ≠ ReachingStar.MultiplierImpl.width := by omega
    simp [hcond.1, hne] at hready
  · simp_all

/-- The refinement relation: an implementation state corresponds to a specification state when, once
busy, it has finished its computation and `prod` is the result.

Arguments:
* first argument: the implementation state.
* second argument: the specification state. -/
inductive flush : ImplModule.State → SpecModule.State → Prop where
/-- Relates a finished implementation state to the specification state with `result := prod` and the
same `busy`.

Arguments:
* `a`, `b`, `prod`, `carry`, `step`, `busy`: the fields of the implementation state. -/
| intro {a b prod carry step busy} :
    (busy = true → step = ReachingStar.MultiplierImpl.width) →
    flush
      { a := a, b := b, prod := prod, carry := carry, step := step, busy := busy }
      { result := prod, busy := busy }

/-! ## Indistinguishability -/

/-- From related states, a `put` of the implementation is a `put` of the specification.

Arguments:
* `i`, `i'`: the implementation states.
* `s`: the specification state.
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: The two guards agree on `busy`. -/
@[local grind →] theorem flush_indistinguishable_put
    (i i' : ImplModule.State) (s : SpecModule.State)
    (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.put, Footprint.arg2 v1 v2 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod2,
    ReachingStar.MultiplierSpec.meth_put,
    ReachingStar.MultiplierSpec.meth_RDY_put,
    ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hm ⊢
  cases v
  first
    | (obtain ⟨-, -, -, -, -, hrdy⟩ := hm
       exact ⟨_, v1, v2, Unit_, rfl, rfl, hrdy⟩)
    | grind

/-- From related states, a `getA` of the implementation is a `getA` of the specification.

Arguments:
* `i`, `i'`: the implementation states.
* `s`: the specification state.
* `v`: the return value.

Proof: The guards agree, because a busy flushed state is finished. -/
@[local grind →] theorem flush_indistinguishable_getA
    (i i' : ImplModule.State) (s : SpecModule.State) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.getA, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.MultiplierSpec.meth_getA,
    ReachingStar.MultiplierSpec.meth_RDY_getA,
    ReachingStar.MultiplierImpl.meth_getA,
    ReachingStar.MultiplierImpl.meth_RDY_getA] at hm ⊢
  cases v
  grind

/-- From related states, a `getV` of the implementation is a `getV` of the specification.

Arguments:
* `i`, `i'`: the implementation states.
* `s`: the specification state.
* `v`: the return value.

Proof: The guards agree and `prod` is the result. -/
@[local grind →] theorem flush_indistinguishable_getV
    (i i' : ImplModule.State) (s : SpecModule.State) (v : Nat) :
  flush i s →
  ImplModule.getMethod i ⟨.getV, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s' := by
  intro hf hm
  cases hf
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
    ReachingStar.MultiplierSpec.meth_getV,
    ReachingStar.MultiplierSpec.meth_RDY_getV,
    ReachingStar.MultiplierImpl.meth_getV,
    ReachingStar.MultiplierImpl.meth_RDY_getV] at hm ⊢
  grind

/-- The loop invariant of the iteration: `prod` holds the low part `lo` already computed, and `lo`
with what is left gives the result.

Arguments:
* `result`: the expected final product.
* `s`: the current implementation state. -/
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

/-- `topPlace` is the weight `base ^ (width - 1)` of the most significant digit.

Proof: By computation. -/
private theorem topPlace_eq_pow :
    ReachingStar.MultiplierImpl.topPlace =
      ReachingStar.MultiplierImpl.base ^
        (ReachingStar.MultiplierImpl.width - 1) := by
  rfl

/-- One `mulStep` preserves the value `lo + base^k * (carry + a * b)` still to be accumulated.

Arguments:
* `a`, `b`, `carry`: the fields of the state.
* `lo`: the low part already computed.
* `k`: the current step.

Proof: Split `a * b` and the carry into their digit and quotient, then rearrange. -/
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

/-- Shifting `prod` right and adding the new top digit keeps `prod = lo * base^(width - k)`.

Arguments:
* `lo`: the low part.
* `digit`: the new digit.
* `k`: the current step.
* `hk`: `k < width`.

Proof: Rewrite the powers of `base`, cancel the division by `base`, and rearrange. -/
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
    simp [ReachingStar.MultiplierImpl.base,
      ReachingStar.MultiplierParams.base]
  rw [hcancel]
  ring

/-- Adding a digit at position `k` keeps the low part below `base^(k + 1)`.

Arguments:
* `lo`: the low part.
* `digit`: the new digit.
* `k`: the position.
* `hlo`: `lo < base^k`.
* `hdigit`: `digit < base`.

Proof: By cases on the digit. -/
private theorem radix_lo_bound (lo digit k : Nat)
    (hlo : lo < ReachingStar.MultiplierImpl.base ^ k)
    (hdigit : digit < ReachingStar.MultiplierImpl.base) :
    lo + digit * ReachingStar.MultiplierImpl.base ^ k <
      ReachingStar.MultiplierImpl.base ^ (k + 1) := by
  simp only [ReachingStar.MultiplierImpl.base,
    ReachingStar.MultiplierParams.base] at hlo hdigit ⊢
  interval_cases digit <;> simp_all [pow_succ] <;> omega

/-- The loop invariant holds right after `put(v1, v2)`, for the result `v1 * v2 mod base^width`.

Arguments:
* `v1`, `v2`: the operands, as numbers.

Proof: Take `lo = 0`. -/
private theorem mulInv_initial (v1 v2 : Nat) :
    mulInv ((v1 * v2) % ReachingStar.MultiplierImpl.modulus)
      { a := v1, b := v2, prod := 0, carry := 0, step := 0, busy := true } := by
  refine ⟨0, rfl, by simp, ?_, by simp [ReachingStar.MultiplierImpl.base], ?_, ?_⟩
  · simp
  · simp [ReachingStar.MultiplierImpl.base]
  · intro h
    exact ⟨rfl, rfl⟩

/-- When the loop is done, the invariant gives `prod = result`.

Arguments:
* `hi`: the invariant.
* `hdone`: `step = width`.

Proof: At `step = width` the invariant reduces to `prod = lo = result`. -/
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

/-- While the loop is not done, some rule fires and preserves the invariant.

Arguments:
* `hi`: the invariant.
* `hlt`: `step < width`.

Proof: If `a = 0` then `mulStepFast` fires and everything stays `0`; otherwise `mulStep` fires,
and the `radix_*` lemmas give the invariant for the next state. -/
private theorem mulInv_step {result : Nat} {s : ImplModule.State}
    (hi : mulInv result s)
    (hlt : s.step < ReachingStar.MultiplierImpl.width) :
    ∃ s', ImplModule.getARule s s' ∧ mulInv result s' := by
  obtain ⟨lo, hbusy, hle, hprod, hlo, hresult, hzero⟩ := hi
  by_cases ha : s.a = 0

  · let s' : ImplModule.State :=
      (ReachingStar.MultiplierImpl.rule_mulStepFast s).2

    have hs_a : s'.a = s.a := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]
    have hs_prod : s'.prod = s.a := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]
    have hs_carry : s'.carry = s.carry := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]
    have hs_step : s'.step = ReachingStar.MultiplierImpl.width := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]
    have hs_busy : s'.busy = s.busy := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]

    refine ⟨s', ?_, ?_⟩

    · refine ⟨.mulStepFast, ?_⟩
      dsimp [ImplModule, Module.getRule, ofRule, s']
      simp [ReachingStar.MultiplierImpl.rule_mulStepFast,
        hbusy, ha, hlt]

    · obtain ⟨hlo0, hcarry0⟩ := hzero ha
      have hresult0 : result = 0 := by
        simpa [ha, hlo0, hcarry0] using hresult

      refine ⟨0, ?_, ?_, ?_, ?_, ?_, ?_⟩

      · rw [hs_busy]
        exact hbusy
      · rw [hs_step]
      · rw [hs_prod, hs_step, ha]
        simp
      · rw [hs_step]
        norm_num [ReachingStar.MultiplierImpl.base,
          ReachingStar.MultiplierImpl.width,
          ReachingStar.MultiplierParams.base,
          ReachingStar.MultiplierParams.width]
      · rw [hresult0, hs_step, hs_carry, hs_a, ha]
        simp [hcarry0]
      · intro _
        constructor
        · rfl
        · rw [hs_carry]
          exact hcarry0

  · let digit := ReachingStar.MultiplierImpl.stepSum s %
      ReachingStar.MultiplierImpl.base
    let lo' := lo + digit * ReachingStar.MultiplierImpl.base ^ s.step
    let s' : ImplModule.State :=
      (ReachingStar.MultiplierImpl.rule_mulStep s).2

    have hs_a : s'.a = s.a := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]
    have hs_b : s'.b = s.b / ReachingStar.MultiplierImpl.base := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]
    have hs_prod :
        s'.prod =
          (ReachingStar.MultiplierImpl.stepSum s %
              ReachingStar.MultiplierImpl.base) *
              ReachingStar.MultiplierImpl.topPlace +
            s.prod / ReachingStar.MultiplierImpl.base := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]
    have hs_carry :
        s'.carry = ReachingStar.MultiplierImpl.stepSum s /
          ReachingStar.MultiplierImpl.base := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]
    have hs_step : s'.step = s.step + 1 := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]
    have hs_busy : s'.busy = s.busy := by
      simp [s', ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]

    refine ⟨s', ?_, ?_⟩

    · refine ⟨.mulStep, ?_⟩
      dsimp [ImplModule, Module.getRule, ofRule, s']
      simp [ReachingStar.MultiplierImpl.rule_mulStep,
        hbusy, ha, hlt]

    · refine ⟨lo', ?_, ?_, ?_, ?_, ?_, ?_⟩

      · rw [hs_busy]
        exact hbusy
      · rw [hs_step]
        omega
      · rw [hs_prod, hs_step]
        dsimp [lo', digit]
        rw [hprod]
        exact radix_prod_step lo
          (ReachingStar.MultiplierImpl.stepSum s %
            ReachingStar.MultiplierImpl.base)
          s.step hlt
      · rw [hs_step]
        dsimp [lo', digit]
        exact radix_lo_bound lo
          (ReachingStar.MultiplierImpl.stepSum s %
            ReachingStar.MultiplierImpl.base)
          s.step hlo
          (Nat.mod_lt _ (by
            norm_num [ReachingStar.MultiplierImpl.base,
              ReachingStar.MultiplierParams.base]))
      · rw [hs_a, hs_b, hs_carry, hs_step]
        dsimp [lo', digit]
        rw [hresult]
        apply congrArg
          (fun x => x % ReachingStar.MultiplierImpl.modulus)
        simpa [ReachingStar.MultiplierImpl.stepSum,
          ReachingStar.MultiplierImpl.selected,
          ReachingStar.MultiplierImpl.topPlace] using
          (radix_value_step s.a s.b s.carry lo s.step).symm
      · intro ha'
        rw [hs_a] at ha'
        exact (ha ha').elim

/-- Every rule strictly decreases `width - step`.

Arguments:
* `hr`: the rule step.

Proof: By cases on the rule, using its guard `step < width`. -/
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

/-- From a state with the invariant, rules reach a finished state that still has it.

Arguments:
* `hi`: the invariant.

Proof: By strong induction on `width - step`, firing `mulInv_step` until `step = width`. -/
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

/-! ## Reaching a flushed state again -/

/-- After a matched `put`, the implementation reaches a flushed state related to the new
specification state.

Arguments:
* `i`, `i'`: the implementation states.
* `s`, `s'`: the specification states.
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: Run the rules from the state after `put` with `mulInv_initial` and `mulInv_reaches_done`;
`mulInv_done` shows that `prod` is the product. -/
@[local grind →] theorem reach_flush_again_put
    (i i' : ImplModule.State) (s s' : SpecModule.State)
    (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.put, Footprint.arg2 v1 v2 v⟩ i' →
  SpecModule.getMethod s ⟨.put, Footprint.arg2 v1 v2 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf hm hs
  dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod2,
    ReachingStar.MultiplierSpec.meth_put,
    ReachingStar.MultiplierSpec.meth_RDY_put,
    ReachingStar.MultiplierImpl.meth_put,
    ReachingStar.MultiplierImpl.meth_RDY_put] at hm hs
  have key : ∀ x y : Nat, ∃ t,
      Relation.ReflTransGen ImplModule.getARule
        ({ a := x, b := y, prod := 0, carry := 0, step := 0, busy := true } :
          ReachingStar.MultiplierImpl.State) t ∧
      flush t
        ({ result := (x * y) % ReachingStar.MultiplierSpec.modulus, busy := true } :
          ReachingStar.MultiplierSpec.State) := by
    intro x y
    obtain ⟨t, hstar, hstep, hinv⟩ := mulInv_reaches_done (mulInv_initial x y)
    have hprod := mulInv_done hinv hstep
    refine ⟨t, hstar, ?_⟩
    have hbusy : t.busy = true := by
      obtain ⟨-, hb, -⟩ := hinv
      exact hb
    rw [show ReachingStar.MultiplierSpec.modulus =
      ReachingStar.MultiplierImpl.modulus by rfl]
    rw [← hprod, ← hbusy]
    exact flush.intro (by intro; exact hstep)
  obtain ⟨iw1, iw2, iv, hm_action, hm_fp, -⟩ := hm
  cases iv
  cases v
  cases hm_fp
  obtain ⟨sw1, sw2, sv, hs_action, hs_fp, -⟩ := hs
  cases sv
  cases hs_fp
  injection hm_action with _ hm_state
  injection hs_action with _ hs_state
  rw [← hm_state, ← hs_state]
  exact key _ _

/-- After a matched `getA`, the implementation is flushed again, related to the new specification
state.

Arguments:
* `i`, `i'`: the implementation states.
* `s`, `s'`: the specification states.
* `v`: the return value.

Proof: `getA` clears `busy` on both sides, so no rule is needed. -/
@[local grind →] theorem reach_flush_again_getA
    (i i' : ImplModule.State) (s s' : SpecModule.State) (v : unit_) :
  flush i s →
  ImplModule.getMethod i ⟨.getA, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.getA, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf hm hs
  cases hf with
  | intro hcond =>
      dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
        ReachingStar.MultiplierSpec.meth_getA,
        ReachingStar.MultiplierSpec.meth_RDY_getA,
        ReachingStar.MultiplierImpl.meth_getA,
        ReachingStar.MultiplierImpl.meth_RDY_getA] at hm hs
      obtain ⟨iv, hm_action, hm_fp, -⟩ := hm
      obtain ⟨sv, hs_action, hs_fp, -⟩ := hs
      cases iv
      cases sv
      cases v
      cases hm_fp
      cases hs_fp
      injection hm_action with _ hm_state
      injection hs_action with _ hs_state
      refine ⟨i', Relation.ReflTransGen.refl, ?_⟩
      rw [← hm_state, ← hs_state]
      exact flush.intro (by simp)

/-- After a matched `getV`, the implementation is flushed again, related to the new specification
state.

Arguments:
* `i`, `i'`: the implementation states.
* `s`, `s'`: the specification states.
* `v`: the return value.

Proof: `getV` changes neither state. -/
@[local grind →] theorem reach_flush_again_getV
    (i i' : ImplModule.State) (s s' : SpecModule.State) (v : Nat) :
  flush i s →
  ImplModule.getMethod i ⟨.getV, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.getV, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by
  intro hf hm hs
  cases hf with
  | intro hcond =>
      dsimp [SpecModule, ImplModule, Module.getMethod, ofAVMethod0,
        ReachingStar.MultiplierSpec.meth_getV,
        ReachingStar.MultiplierSpec.meth_RDY_getV,
        ReachingStar.MultiplierImpl.meth_getV,
        ReachingStar.MultiplierImpl.meth_RDY_getV] at hm hs
      obtain ⟨wm, hm_action, hm_fp, -⟩ := hm
      obtain ⟨ws, hs_action, hs_fp, -⟩ := hs
      cases hm_fp
      cases hs_fp
      injection hm_action with _ hm_state
      injection hs_action with _ hs_state
      refine ⟨i', Relation.ReflTransGen.refl, ?_⟩
      rw [← hm_state, ← hs_state]
      exact flush.intro hcond

/-- From a flushed state `mulStep` cannot fire, so `flush` is preserved.

Arguments:
* `i`, `i'`: the implementation states.
* `s`: the specification state.

Proof: A busy flushed state has `step = width`, against the guard. -/
@[local grind →] theorem flush_reaches_flush_mulStep
    (i i' : ImplModule.State) (s : SpecModule.State) :
  flush i s → ImplModule.getRule .mulStep i i' → flush i' s := by
  intro hf hr
  cases hf with
  | intro hdone =>
      dsimp [ImplModule, Module.getRule, ofRule,
        ReachingStar.MultiplierImpl.rule_mulStep] at hr
      split at hr
      · rename_i hcond
        have := hdone hcond.1
        omega
      · simp_all

/-- From a flushed state `mulStepFast` cannot fire, so `flush` is preserved.

Arguments:
* `i`, `i'`: the implementation states.
* `s`: the specification state.

Proof: A busy flushed state has `step = width`, against the guard. -/
@[local grind →] theorem flush_reaches_flush_mulStepFast
    (i i' : ImplModule.State) (s : SpecModule.State) :
  flush i s → ImplModule.getRule .mulStepFast i i' → flush i' s := by
  intro hf hr
  cases hf with
  | intro hdone =>
      dsimp [ImplModule, Module.getRule, ofRule,
        ReachingStar.MultiplierImpl.rule_mulStepFast] at hr
      split at hr
      · rename_i hcond
        have := hdone hcond.1
        omega
      · simp_all

/-- The rules of the implementation always terminate.

Proof: By strong induction on `width - step`, which every rule decreases. -/
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

/-- The multiplier as a structured refinement of `SpecModule` by `ImplModule`. -/
def multiplier_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := flush
  rules_strongly_normalising := rules_strongly_normalising

------------OKAY UNTIL HERE-------------------------

/-- The idle implementation state, the initial state. -/
private def idleI : ImplModule.State :=
  { a := 0, b := 0, prod := 0, carry := 0, step := 0, busy := false }

/-- The levels of the multiplier. Every method is a low transition: `put` has a `high` first operand
and a `low` second one, and `getA` and `getV` have a `low` result. Rules are internal. -/
noncomputable def mulLevels : TwoLevelPolicy Method := ⟨fun e =>
  match e.name with
  | .put  => some (EventLevels.ofList e.footprint [.high, .low] .low .low)
  | .getA => some (EventLevels.ofList e.footprint [] .low .low)
  | .getV => some (EventLevels.ofList e.footprint [] .low .low)⟩

open Classical in
/-- The encoding of the high inputs of a label as an index: the high operand of `put`.

Arguments:
* `h`: the high inputs of a label, a `mulLevels.highInputs` label. -/
noncomputable def mulG (h : Label Method) : BitVec ReachingStar.MultiplierImpl.width :=
  if hx : ∃ (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_),
      h = mulLevels.highInputs ⟨.put, Footprint.arg2 v1 v2 v⟩ then hx.choose else 0

/-- `idx_P` for the multiplier.

Arguments:
* the argument: the label. -/
noncomputable def mulIdx : Label Method → BitVec ReachingStar.MultiplierImpl.width :=
  mulLevels.idx mulG

/-- The security policy of the multiplier: its levels and the encoding of its high inputs. -/
noncomputable def mulPolicy : IndexedPolicy (BitVec ReachingStar.MultiplierImpl.width) Method :=
  { mulLevels with g := mulG }

/-- `put` carries a high input, its first operand.

Arguments:
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: By `ofList_arg2_fst`. -/
private theorem put_hasHigh (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    mulLevels.HasHighInput ⟨.put, Footprint.arg2 v1 v2 v⟩ :=
  ⟨(0 : Fin 2), EventLevels.ofList_arg2_fst v1 v2 v _ _ _ _⟩

/-- The first operand of `put` is `high`.

Arguments:
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: By `ofList_arg2_fst`. -/
private theorem argLevel_put0 (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    mulLevels.argLevel ⟨.put, Footprint.arg2 v1 v2 v⟩ (0 : Fin 2) = .high :=
  EventLevels.ofList_arg2_fst v1 v2 v _ _ _ _

/-- The index of `put(v1, v2)` is its high operand `v1`.

Arguments:
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: `put` has a high input, so its index is `mulG` of its high inputs; those keep `v1`, so the
`choose` in `mulG` picks a value equal to `v1`. -/
private theorem mulIdx_put (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    mulIdx ⟨.put, Footprint.arg2 v1 v2 v⟩ = v1 := by
  unfold mulIdx
  rw [TwoLevelPolicy.idx_of_hasHighInput _ _ (put_hasHigh v1 v2 v)]
  have hx : ∃ (w1 w2 : BitVec ReachingStar.MultiplierImpl.width) (w : unit_),
      mulLevels.highInputs ⟨.put, Footprint.arg2 v1 v2 v⟩ =
        mulLevels.highInputs ⟨.put, Footprint.arg2 w1 w2 w⟩ :=
    ⟨v1, v2, v, rfl⟩
  unfold mulG
  rw [dif_pos hx]
  obtain ⟨w2, w, hw⟩ := hx.choose_spec
  unfold TwoLevelPolicy.highInputs maskFootprint at hw
  injection hw with _ hfp
  obtain ⟨-, -, -, -, hargs, -⟩ := Footprint.mk.inj hfp
  injection eq_of_heq hargs with _ _ h1
  beta_reduce at h1
  rw [argLevel_put0, argLevel_put0] at h1
  exact (Option.some.inj h1).symm

/-- `put` has a `high` argument, so it is never `low_P`.

Arguments:
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: `low_P` would make its first argument `low`, against `ofList_arg2_fst`. -/
private theorem put_not_low (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    ¬ mulLevels.IsLow ⟨.put, Footprint.arg2 v1 v2 v⟩ := by
  rintro ⟨lv, hlv, hargs, -⟩
  have hlv' : some (EventLevels.ofList (Footprint.arg2 v1 v2 v) [.high, .low] .low .low) =
      some lv := hlv
  cases hlv'
  have := (EventLevels.ofList_arg2_fst v1 v2 v TwoLevel.high .low .low .low).symm.trans
    (hargs (0 : Fin 2))
  cases this

/-- In `⟦M⟧^{P_0}` every computation was started with high operand `0`, so a busy state has `a = 0`
and `prod = 0`.

Arguments:
* `s`: the implementation state. -/
private def P0Inv (s : ImplModule.State) : Prop := s.busy = true → s.a = 0 ∧ s.prod = 0

/-- Every transition kept in `T^{P_0}` preserves `P0Inv`.

Arguments:
* the first hypothesis: `P0Inv` holds at the start.
* the second hypothesis: the transition of `⟦M⟧_ORAAT`.
* the third hypothesis: it passes the filter.

Proof: By cases on the transition: with `a = 0` only `mulStepFast` fires and it keeps `prod = 0`,
a kept `put` has `v1 = 0`, `getA` clears `busy`, and `getV` keeps the state. -/
private theorem P0Inv_step {s s' : ImplModule.State} {l : LTSLabel (Label Method)} :
    P0Inv s → (ImplModule.oraat idleI).Step s l s' →
      (mulLevels.low l ∨ mulLevels.idxL mulG l = 0) → P0Inv s' := by
  intro hs hst hk
  cases l with
  | τ =>
      obtain ⟨r, hr⟩ := (Module.oraat_tau_iff (m := ImplModule)).mp hst
      cases r <;>
        dsimp [ImplModule, Module.getRule,
          ofRule, ReachingStar.MultiplierImpl.rule_mulStep,
          ReachingStar.MultiplierImpl.rule_mulStepFast] at hr <;>
        split at hr <;> (try simp at hr) <;> rename_i hcond
      · exact absurd (hs hcond.1).1 hcond.2.1
      · obtain ⟨-, rfl⟩ := hr
        intro hb
        exact ⟨(hs hb).1, (hs hb).1⟩
  | vis e =>
      obtain ⟨name, fp⟩ := e
      have hm := (Module.oraat_vis_iff (m := ImplModule)).mp hst
      cases name
      · dsimp [ImplModule, ofAVMethod2, ReachingStar.MultiplierImpl.meth_put] at hm
        obtain ⟨v1, v2, v, hact, rfl, -⟩ := hm
        injection hact with _ hact
        subst hact
        have hv1 : v1 = 0 := by
          rcases hk with hk | hk
          · exact absurd hk (put_not_low v1 v2 v)
          · have hk' : mulIdx ⟨.put, Footprint.arg2 v1 v2 v⟩ = 0 := hk
            rwa [mulIdx_put] at hk'
        intro _
        simp [hv1]
      · dsimp [ImplModule, ofAVMethod0, ReachingStar.MultiplierImpl.meth_getA] at hm
        obtain ⟨v, hact, -, -⟩ := hm
        injection hact with _ hact
        subst hact
        intro hb
        simp at hb
      · dsimp [ImplModule, ofAVMethod0, ReachingStar.MultiplierImpl.meth_getV] at hm
        obtain ⟨v, hact, -, -⟩ := hm
        injection hact with _ hact
        subst hact
        exact hs

/-- The method name of a visible label, and `none` for `τ`.

Arguments:
* the argument: the label. -/
private def labelName : LTSLabel (Label Method) → Option Method
  | .vis e => some e.name
  | .τ     => none

/-! ## Functional non-interference fails

`FNI_P(M) ≜ ∀ i, ⟦M⟧^P_ORAAT ≈ ⟦M⟧^{P_i}_ORAAT` fails at `i = 0`, through the concretization. -/

/-- `⟦M⟧^P`, the multiplier seen through the policy. -/
noncomputable abbrev Projected : LTS ImplModule.State (LTSLabel (Label Method)) :=
  mulLevels.semF ImplModule idleI

/-- Rule paths of `M` are `τ*` paths of `⟦M⟧^P`.

Arguments:
* `h`: the rule path.

Proof: Each rule step is a `τ` step. -/
private theorem tauStar_of_rules {s t : ImplModule.State}
    (h : Relation.ReflTransGen ImplModule.getARule s t) : Projected.TauStar s t :=
  h.mono fun _ _ h => LTS.map_step (f := mulLevels.projectF) (Module.oraat_tau_iff.mpr h)

/-! The proof goes through the module `M_0`: it shows that the `getV` of `M_0` only returns `0`, and
follows the single trace `put(1, 1) · getV ↦ 1`. -/

/-- `M_0`, the multiplier concretized at high operand `0`. -/
noncomputable abbrev M0 : Bluespec.Module Rule Method :=
  mulLevels.concretize mulG 0 ImplModule

/-- Every step of `⟦M_0⟧_ORAAT` preserves `P0Inv`.

Arguments:
* `hs`: `P0Inv` holds at the start.
* `h`: the step.

Proof: `concretize_step` turns it into a kept transition of `M`, covered by `P0Inv_step`. -/
private theorem P0Inv_M0 {s s' : ImplModule.State} {l : LTSLabel (Label Method)}
    (hs : P0Inv s) (h : (M0.oraat idleI).Step s l s') : P0Inv s' :=
  let ⟨h₁, h₂⟩ := TwoLevelPolicy.concretize_step.mp h
  P0Inv_step hs h₁ h₂

/-- The multiplier is not weakly bisimilar to `M_0`, through the policy.

Proof: `⟦M⟧^P` has the trace `put(1, 1) · getV ↦ 1`, while `P0Inv` makes every `getV` of
`⟦M_0⟧^P` return `0`. -/
theorem mul_not_weaklyBisimilar_M0 :
    ¬ LTS.WeaklyBisimilar (mulPolicy.semF ImplModule idleI) (mulPolicy.semF M0 idleI) := by
  rintro ⟨R, hR, hinit⟩
  let one : BitVec ReachingStar.MultiplierImpl.width := 1
  let s1 : ImplModule.State :=
    { a := one.toNat, b := one.toNat, prod := 0, carry := 0, step := 0, busy := true }
  -- `⟦M⟧^P` fires `put(1, 1)`
  have hput : (mulLevels.semF ImplModule idleI).Step idleI
      (mulLevels.projectF (.vis ⟨.put, Footprint.arg2 one one Unit_⟩)) s1 :=
    LTS.map_step (Module.oraat_vis_iff.mpr ⟨one, one, Unit_, rfl, rfl, rfl⟩)
  obtain ⟨b1, hb1, hR1⟩ := (hR _ _ hinit _).1 s1 hput
  -- then runs its rules until the product `1` is computed
  obtain ⟨t, hstar, hstep, hinv⟩ := mulInv_reaches_done (mulInv_initial one.toNat one.toNat)
  have hprod : t.prod = 1 := by
    rw [mulInv_done hinv hstep]
    decide
  have hbusy : t.busy = true := hinv.choose_spec.1
  obtain ⟨b2, hb2, hR2⟩ := hR.tauStar_left hR1 (tauStar_of_rules hstar)
  -- and fires `getV ↦ 1`
  have hgetV : (mulLevels.semF ImplModule idleI).Step t
      (mulLevels.projectF (.vis ⟨.getV, Footprint.arg0 t.prod⟩)) t :=
    LTS.map_step (Module.oraat_vis_iff.mpr ⟨t.prod, rfl, rfl, by
      simp [ReachingStar.MultiplierImpl.meth_RDY_getV, hbusy, hstep]⟩)
  obtain ⟨b3, hb3, -⟩ := (hR _ _ hR2 _).1 t hgetV
  -- `⟦M_0⟧^P` must match it, but its `getV` returns `0`
  have hInv : ∀ s l s', P0Inv s → (mulLevels.semF M0 idleI).Step s l s' → P0Inv s' :=
    LTS.map_invariant fun _ _ _ => P0Inv_M0
  have hidle : P0Inv idleI := fun h => by simp [idleI] at h
  have hI2 : P0Inv b2 :=
    LTS.TauStar.invariant hInv hb2 (LTS.WeakStep.invariant hInv hb1 hidle)
  obtain ⟨x, y, hx, hxy, -⟩ := hb3
  have hIx : P0Inv x := LTS.TauStar.invariant hInv hx hI2
  obtain ⟨l, hl, hC⟩ := hxy
  cases l with
  | τ =>
      have h : (none : Option Method) = some .getV := congrArg labelName hl
      cases h
  | vis e =>
      obtain ⟨name, fp⟩ := e
      obtain ⟨hm, -⟩ := (Module.oraat_vis_iff (m := M0)).mp hC
      cases name
      · have h : (some Method.put : Option Method) = some .getV := congrArg labelName hl
        cases h
      · have h : (some Method.getA : Option Method) = some .getV := congrArg labelName hl
        cases h
      · dsimp [ImplModule, ofAVMethod0, ReachingStar.MultiplierImpl.meth_getV,
          ReachingStar.MultiplierImpl.meth_RDY_getV] at hm
        obtain ⟨v, hact, rfl, hrdy⟩ := hm
        injection hact with hv _
        have hxbusy : x.busy = true := by
          by_contra hb
          simp [hb] at hrdy
        rw [← hv, (hIx hxbusy).2, hprod] at hl
        injection hl with he
        injection he with _ hfp
        injection hfp with _ _ _ _ _ hret
        have h01 : (some 0 : Option Nat) = some 1 := hret
        exact absurd (Option.some.inj h01) (by decide)

/-- Definition 3 fails for the multiplier.

Proof: `FNI_iff_concretize` at index `0` contradicts `mul_not_weaklyBisimilar_M0`. -/
theorem mul_not_FNI : ¬ FNI mulPolicy ImplModule idleI :=
  fun hFNI => mul_not_weaklyBisimilar_M0 ((FNI_iff_concretize mulPolicy ImplModule idleI).mp hFNI 0)

/-! ## The transitions kept in `T^{P_i}`

`T^{P_i}` keeps the low transitions (`getA`, `getV`, all rules) and only the `put`s whose high
operand is `i`. -/

/-- A `put(v1, v2)` passes the filter of `T^{P_i}` iff its high operand is `i`.

Arguments:
* `i`: the index.
* `v1`, `v2`: the operands.
* `v`: the return value.

Proof: `put` is never `low_P`, and its index is `v1`. -/
theorem keep_put_iff (i v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    (mulLevels.low (.vis ⟨.put, Footprint.arg2 v1 v2 v⟩) ∨
      mulLevels.idxL mulG (.vis ⟨.put, Footprint.arg2 v1 v2 v⟩) = i) ↔ v1 = i := by
  constructor
  · rintro (hk | hk)
    · exact absurd hk (put_not_low v1 v2 v)
    · have hk' : mulIdx ⟨.put, Footprint.arg2 v1 v2 v⟩ = i := hk
      rwa [mulIdx_put] at hk'
  · rintro rfl
    exact .inr (mulIdx_put v1 v2 v)

/-- `getV` has no argument and a low result, so it is a low transition.

Arguments:
* `fp`: the footprint.

Proof: By definition of `mulLevels`. -/
theorem getV_isLow (fp : Footprint) : mulLevels.IsLow ⟨.getV, fp⟩ :=
  ⟨_, rfl, fun _ => rfl, rfl⟩

/-- The operands of the multiplier. -/
private abbrev Word := BitVec ReachingStar.MultiplierImpl.width

/-! ## NFI of the multiplier -/

/-- The label of a `put` does not see the high operand: `put(v1, v2) ↓F_P` only depends on `v2`.

Arguments:
* `v1`, `w`: two high operands.
* `v2`: the low operand.
* `v`: the return value.

Proof: Both masked footprints mask the first argument to `none` and keep `v2`. -/
private theorem projectF_put (v1 w v2 : Word) (v : unit_) :
    mulLevels.projectF (.vis ⟨.put, Footprint.arg2 v1 v2 v⟩) =
      mulLevels.projectF (.vis ⟨.put, Footprint.arg2 w v2 v⟩) := by
  have key : ∀ x : Word,
      maskFootprint (Footprint.arg2 x v2 v)
        (EventLevels.ofList (Footprint.arg2 x v2 v) [.high, .low] .low .low).args .low =
      maskFootprint (Footprint.arg2 w v2 v)
        (EventLevels.ofList (Footprint.arg2 w v2 v) [.high, .low] .low .low).args .low := by
    intro x
    have h1 := EventLevels.ofList_arg2_fst x v2 v TwoLevel.high .low .low .low
    have h2 := EventLevels.ofList_arg2_snd x v2 v TwoLevel.high .low .low .low
    have h3 := EventLevels.ofList_arg2_fst w v2 v TwoLevel.high .low .low .low
    have h4 := EventLevels.ofList_arg2_snd w v2 v TwoLevel.high .low .low .low
    let F : Fin 2 → Type := fun k => Option ((Footprint.arg2 (0 : Word) (0 : Word) Unit_).f k)
    let G : Option Word → Option Word → Footprint := fun p q =>
      @Footprint.mk (Option unit_) (Fin 2) F [0, 1]
        (@HVector.cons _ F [1] 0 p (@HVector.cons _ F [] 1 q .nil)) (maskOpt .low v)
    have hx : ∀ z : Word, maskFootprint (Footprint.arg2 z v2 v)
        (EventLevels.ofList (Footprint.arg2 z v2 v) [.high, .low] .low .low).args .low =
        G (maskOpt ((EventLevels.ofList (Footprint.arg2 z v2 v) [.high, .low] .low .low).args
            (0 : Fin 2)) z)
          (maskOpt ((EventLevels.ofList (Footprint.arg2 z v2 v) [.high, .low] .low .low).args
            (1 : Fin 2)) v2) := fun _ => rfl
    rw [hx x, hx w, h1, h2, h3, h4]
    rfl
  exact congrArg (fun fp => LTSLabel.vis (Event.mk Method.put fp)) (key v1)

/-- The overwriting of the multiplier at index `i`: `put(v1, v2)` runs as `put(i, v2)`, and the
other methods run as themselves.

Arguments:
* `i`: the value of the high operand.
* `e`, `e'`: the label called and the label run. -/
def mulFix (i : Word) (e e' : Label Method) : Prop :=
  (∃ (v1 v2 : Word) (v : unit_), e = ⟨.put, Footprint.arg2 v1 v2 v⟩ ∧
    e' = ⟨.put, Footprint.arg2 i v2 v⟩) ∨
  (e.name ≠ .put ∧ e' = e)

/-- `mulFix i` is a well-behaved overwriting.

Arguments:
* `i`: the index.

Proof: `projectF_put` hides the change, `keep_put_iff` shows that `put(i, v2)` is kept, and a
kept real `put` already has `v1 = i`. -/
theorem mulFix_fixes (i : Word) : Fixes mulPolicy i ImplModule (mulFix i) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro e e' (⟨v1, v2, v, rfl, rfl⟩ | ⟨-, rfl⟩)
    · exact projectF_put i v1 v2 v
    · rfl
  · rintro e e' (⟨-, v2, v, -, rfl⟩ | ⟨hn, rfl⟩)
    · exact (keep_put_iff i i v2 v).mpr rfl
    · obtain ⟨name, fp⟩ := e'
      cases name with
      | put => exact absurd rfl hn
      | getA => exact .inl ⟨_, rfl, fun _ => rfl, rfl⟩
      | getV => exact .inl (getV_isLow fp)
  · rintro ⟨name, fp⟩ ⟨s, s', hm⟩ hk
    cases name with
    | put =>
        obtain ⟨v1, v2, v, -, rfl, -⟩ := hm
        have hv : v1 = i := (keep_put_iff i v1 v2 v).mp hk
        subst hv
        exact .inl ⟨v1, v2, v, rfl, rfl⟩
    | getA => exact .inr ⟨(fun h => by cases h), rfl⟩
    | getV => exact .inr ⟨(fun h => by cases h), rfl⟩

/-- For the multiplier, FNI and NFI are equivalent.

Proof: `FNI_iff_NFI`, with `mulFix` as the overwriting of each index. -/
theorem mul_FNI_iff_NFI :
    FNI mulPolicy ImplModule idleI ↔ NFI mulPolicy ImplModule idleI :=
  FNI_iff_NFI _ _ _ fun i => ⟨mulFix i, mulFix_fixes i⟩

/-- The multiplier is not NFI.

Proof: `mul_not_FNI` carried across `mul_FNI_iff_NFI`. -/
theorem mul_not_NFI : ¬ NFI mulPolicy ImplModule idleI :=
  fun h => mul_not_FNI (mul_FNI_iff_NFI.mpr h)

end ReachingStar.Bluespec.Multiplier
