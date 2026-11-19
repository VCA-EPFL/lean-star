import Multiplier

open ReachingStar.Security
open BluespecPrelude
open ReachingStar.MultiplierImpl
open ReachingStar.Bluespec.Multiplier (ImplModule)

namespace ReachingStar.Security.FixScratch

/-- A shadow State  one security level per field. -/
structure State_Security_Level where
  a_L : TwoLevel
  b_L : TwoLevel
  prod_L : TwoLevel
  carry_L : TwoLevel
  step_L : TwoLevel
  busy_L : TwoLevel


def rule_mulStepFast_State (s : State_Security_Level) : State_Security_Level :=
  let guard_L := s.busy_L ⊔ s.a_L ⊔ s.step_L
  { s with prod_L := s.a_L ⊔ guard_L, step_L := guard_L }

def rule_mulStep_State (s : State_Security_Level) : State_Security_Level :=
  let guard_L := s.busy_L ⊔ s.a_L ⊔ s.step_L
  { s with
      b_L     := s.b_L ⊔ guard_L
      prod_L  := s.a_L ⊔ s.b_L ⊔ s.carry_L ⊔ s.prod_L ⊔ guard_L
      carry_L := s.a_L ⊔ s.b_L ⊔ s.carry_L ⊔ guard_L
      step_L  := s.step_L ⊔ guard_L }

def meth_put_State (s : State_Security_Level) (v1_L v2_L : TwoLevel) : State_Security_Level :=
  let guard_L := s.busy_L
  { a_L := v1_L ⊔ guard_L, b_L := v2_L ⊔ guard_L,
    prod_L := guard_L, carry_L := guard_L, step_L := guard_L, busy_L := guard_L }

def meth_getV_State (s : State_Security_Level) : TwoLevel × State_Security_Level :=
  let guard_L := s.busy_L ⊔ s.step_L
  (s.prod_L ⊔ guard_L, s)

def meth_getA_State (s : State_Security_Level) : State_Security_Level :=
  let guard_L := s.busy_L ⊔ s.step_L
  { s with busy_L := guard_L }

-- A config is a State combined with a State_Security_Level 
abbrev Config := State × State_Security_Level

def call_mulStep (c : Config) : Config :=
  let (fired, s') := rule_mulStep c.1
  ite_bsv fired (s', rule_mulStep_State c.2) c

def call_mulStepFast (c : Config) : Config :=
  let (fired, s') := rule_mulStepFast c.1
  ite_bsv fired (s', rule_mulStepFast_State c.2) c

def call : ReachingStar.Bluespec.Multiplier.Rule → Config → Config
  | .mulStep     => call_mulStep
  | .mulStepFast => call_mulStepFast

def call_put (c : Config) (v1 v2 : BitVec width) (v1_L v2_L : TwoLevel) : Config :=
  ((meth_put c.1 v1 v2).avAction_, meth_put_State c.2 v1_L v2_L)

def call_getA (c : Config) : Config :=
  ((meth_getA c.1).avAction_, meth_getA_State c.2)

def getV_obs (c : Config) : Nat × TwoLevel :=
  ((meth_getV c.1).avValue_, (meth_getV_State c.2).1)


def init_State_level : State_Security_Level :=
  { a_L := .low, b_L := .low, prod_L := .low, carry_L := .low, step_L := .low, busy_L := .low }

def start : Config :=
  (def_state, init_State_level)

def callEnabled (c : Config) : Config := call_mulStep (call_mulStepFast c)

/-- hacky way to run the rules mutliples times  -/
def settle (c : Config) : Config := (callEnabled)^[width + 1] c



def multRule : ReachingStar.Bluespec.Multiplier.Method → Option (List TwoLevel × TwoLevel)
  | .put  => some ([.high, .low], .high)   -- put's result is high, but should still be low
  | .getA => some ([], .low)
  | .getV => some ([], .low)

noncomputable def multPolicy : TwoLevelPolicy ReachingStar.Bluespec.Multiplier.Method :=
  ImplModule.twoLevelPolicy multRule


-- helper to prevent copypaste and have the security policy directly wired into the taint tracking logic
def putArgLevels : List TwoLevel := ((multRule .put).getD ([], .low)).1

/-- The session, with `put`'s operand levels taken from the policy instead of hardcoded. -/
def programP (v1 v2 : BitVec width) : (Nat × TwoLevel) × Config :=
  let c   := call_put start v1 v2 (putArgLevels.getD 0 .low) (putArgLevels.getD 1 .low)
  let c   := settle c
  let out := getV_obs c
  (out, call_getA c)


--according to the previous policy the output is always tainted 
example : (programP (3 : BitVec width) 4).1 = (12, .high) := by native_decide
example : (programP (3 : BitVec width) 0).1 = (0,  .high) := by native_decide
example : (programP (0 : BitVec width) 3).1 = (0,  .high) := by native_decide



end ReachingStar.Security.FixScratch
