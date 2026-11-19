import Multiplier
import NFI

open ReachingStar.Security
open BluespecPrelude
open ReachingStar.MultiplierImpl

namespace ReachingStar.Security.TrackedStateScratch

/-- `MultiplierImpl.State` instrumented with a security level per field. Every real transition is
mirrored here so it carries the taint of each component. -/
structure TrackedState where
  a : Nat
  a_L : TwoLevel
  b : Nat
  b_L : TwoLevel
  prod : Nat
  prod_L : TwoLevel
  carry : Nat
  carry_L : TwoLevel
  step : Nat
  step_L : TwoLevel
  busy : Bool
  busy_L : TwoLevel

/-- Erase the levels: project a tracked state back to the real `MultiplierImpl.State`. -/
def TrackedState.val (t : TrackedState) : State :=
  { a := t.a, b := t.b, prod := t.prod, carry := t.carry, step := t.step, busy := t.busy }

/-! ## Instrumented transitions

Each one reuses the real transition for the *values* and computes the new *levels* alongside, as the
join `⊔` of the levels of the fields/args each result depends on. -/

/-- `put v1 v2`: operands take the argument levels; everything else resets to `low`. -/
def put_t (v1 v2 : BitVec width) (v1_L v2_L : TwoLevel) : TrackedState :=
  let s := init_state v1 v2
  { a := s.a, a_L := v1_L, b := s.b, b_L := v2_L,
    prod := s.prod, prod_L := .low, carry := s.carry, carry_L := .low,
    step := s.step, step_L := .low, busy := s.busy, busy_L := .low }

/-- `rule_mulStep`: `prod ← f(a,b,carry,prod)`, `carry ← f(a,b,carry)`; `a`, `busy`, `step`'s level,
`b`'s level unchanged. -/
def mulStep_t (t : TrackedState) : t_bool × TrackedState :=
  if t.busy ∧ t.a ≠ 0 ∧ t.step < width then
    let s := (rule_mulStep t.val).2
    (BTrue Unit_,
      { a := s.a, a_L := t.a_L, b := s.b, b_L := t.b_L,
        prod := s.prod, prod_L := t.a_L ⊔ t.b_L ⊔ t.carry_L ⊔ t.prod_L,
        carry := s.carry, carry_L := t.a_L ⊔ t.b_L ⊔ t.carry_L,
        step := s.step, step_L := t.step_L, busy := s.busy, busy_L := t.busy_L })
  else (BFalse Unit_, t)

/-- `rule_mulStepFast`: `prod ← a`, `step ← width` (constant). -/
def mulStepFast_t (t : TrackedState) : t_bool × TrackedState :=
  if t.busy ∧ t.a = 0 ∧ t.step < width then
    let s := (rule_mulStepFast t.val).2
    (BTrue Unit_,
      { a := s.a, a_L := t.a_L, b := s.b, b_L := t.b_L,
        prod := s.prod, prod_L := t.a_L, carry := s.carry, carry_L := t.carry_L,
        step := s.step, step_L := .low, busy := s.busy, busy_L := t.busy_L })
  else (BFalse Unit_, t)

/-- `getA`: clears `busy` (a constant). -/
def getA_t (t : TrackedState) : TrackedState := { t with busy := false, busy_L := .low }

/-- `getV` returns `prod` together with its level. -/
def getV_t (t : TrackedState) : Nat × TwoLevel := (t.prod, t.prod_L)

/-! ## The instrumentation erases to the original (values unchanged) -/

theorem put_t_erase (v1 v2 : BitVec width) (l1 l2 : TwoLevel) :
    (put_t v1 v2 l1 l2).val = init_state v1 v2 := rfl

theorem mulStep_t_erase (t : TrackedState) :
    (mulStep_t t).2.val = (rule_mulStep t.val).2 := by
  by_cases h : t.busy ∧ t.a ≠ 0 ∧ t.step < width <;>
    simp [mulStep_t, rule_mulStep, TrackedState.val, h]

theorem getV_t_erase (t : TrackedState) : (getV_t t).1 = (meth_getV t.val).avValue_ := rfl

/-! ## The product carries the operand's taint -/

/-- After `put(high, low)` the product starts `low`… -/
example : (put_t (3 : BitVec width) 4 .high .low).prod_L = .low := by decide

/-- …and one `mulStep` taints it `high` (it reads `a`, which is `high`). -/
example : (mulStep_t (put_t (3 : BitVec width) 4 .high .low)).2.prod_L = .high := by decide

/-- So `getV` hands out a `high` value after `put(high, _)` — the leak, now carried by the state. -/
example : (getV_t (mulStep_t (put_t (3 : BitVec width) 4 .high .low)).2).2 = .high := by decide

/-- A `low` first operand keeps the product `low`. -/
example : (getV_t (mulStep_t (put_t (3 : BitVec width) 4 .low .low)).2).2 = .low := by decide

end ReachingStar.Security.TrackedStateScratch
