import Multiplier
import NFI

open ReachingStar.Security

namespace ReachingStar.Security.StateTaintScratch

/-- A shadow of `MultiplierImpl.State`: one security level per field. -/
structure State_Security_Level where
  a_L     : TwoLevel
  b_L     : TwoLevel
  prod_L  : TwoLevel
  carry_L : TwoLevel
  step_L  : TwoLevel
  busy_L  : TwoLevel
deriving DecidableEq

-- put = init_state v1 v2: a:=v1, b:=v2, rest constant
def put_L (v1_L v2_L : TwoLevel) : State_Security_Level :=
  { a_L := v1_L, b_L := v2_L, prod_L := .low, carry_L := .low, step_L := .low, busy_L := .low }

-- rule_mulStep: prod' = f(a,b,carry,prod), carry' = f(a,b,carry), b'=b/base, step'=step+1
def mulStep_L (L : State_Security_Level) : State_Security_Level :=
  { L with prod_L  := L.a_L ⊔ L.b_L ⊔ L.carry_L ⊔ L.prod_L
           carry_L := L.a_L ⊔ L.b_L ⊔ L.carry_L }

-- rule_mulStepFast: prod' = a, step' = width(const)
def mulStepFast_L (L : State_Security_Level) : State_Security_Level :=
  { L with prod_L := L.a_L, step_L := .low }

-- getA: clears busy (a constant)
def getA_L (L : State_Security_Level) : State_Security_Level := { L with busy_L := .low }

def getV_L (L : State_Security_Level) : TwoLevel := L.prod_L   -- getV returns prod

/-! ## Running the iteration and the leak -/

-- `high` is the top level: joining anything onto it stays `high`
theorem high_sup (x : TwoLevel) : TwoLevel.high ⊔ x = .high := by cases x <;> decide

-- a step never changes the operand's level
theorem mulStep_L_aL (L : State_Security_Level) : (mulStep_L L).a_L = L.a_L := rfl

-- …so any number of steps preserves it
theorem iterate_aL (n : Nat) (L : State_Security_Level) : (mulStep_L^[n] L).a_L = L.a_L := by
  induction n generalizing L with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply, mulStep_L_aL]; exact ih L

-- if the first operand is high, one step taints the product high
theorem mulStep_L_prod_high (L : State_Security_Level) (h : L.a_L = .high) :
    (mulStep_L L).prod_L = .high := by
  show L.a_L ⊔ L.b_L ⊔ L.carry_L ⊔ L.prod_L = .high
  rw [h]; simp [high_sup]

/-- After `put(high, _)`, the product `getV` returns is `high` for any number (≥1) of steps —
the leak, carried through the whole iteration. -/
theorem getV_leaks (n : Nat) (lo : TwoLevel) :
    getV_L (mulStep_L^[n + 1] (put_L .high lo)) = .high := by
  rw [Function.iterate_succ', Function.comp_apply]
  exact mulStep_L_prod_high _ (by simp [iterate_aL, put_L])

/-- `put(low, low)` is a fixpoint of a step, so the product stays `low`: no leak. -/
theorem lowlow_fixed : mulStep_L (put_L .low .low) = put_L .low .low := rfl

theorem getV_safe (n : Nat) : getV_L (mulStep_L^[n] (put_L .low .low)) = .low := by
  rw [Function.iterate_fixed lowlow_fixed]; rfl

end ReachingStar.Security.StateTaintScratch
