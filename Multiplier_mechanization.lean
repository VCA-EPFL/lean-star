/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import NFI
import Multiplier

open BluespecPrelude
open BluespecVerification
open ReachingStar.Security
open ReachingStar.Bluespec
open ReachingStar.Bluespec.Multiplier

namespace ReachingStar.MultiplierParams


-- declare a constant method returnign always 0
def meth_getV (s : ReachingStar.MultiplierImpl.State) :
    t_actionvalue_ Nat ReachingStar.MultiplierImpl.State :=
  { avValue_ := 0
  , avAction_ := s }

def meth_getV_app (s : State) : t_actionvalue_ Nat State :=

  { avValue_ := 0
  , avAction_ := s }

def SpecModule : Bluespec.Module Empty ReachingStar.Bluespec.Multiplier.Method where
  State := ReachingStar.MultiplierSpec.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierSpec.meth_put
        ReachingStar.MultiplierSpec.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierSpec.meth_getA
        ReachingStar.MultiplierSpec.meth_RDY_getA
    | .getV => ofAVMethod0  meth_getV_app
        ReachingStar.MultiplierSpec.meth_RDY_getV
  rules := Empty.casesOn _
  init := fun s => s = { result := 0, busy := false }
-- constant module

def ConstantModule : Bluespec.Module ReachingStar.Bluespec.Multiplier.Rule ReachingStar.Bluespec.Multiplier.Method where
  State := ReachingStar.MultiplierImpl.State
  methods
    | .put  => ofAVMethod2 ReachingStar.MultiplierImpl.meth_put
        ReachingStar.MultiplierImpl.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getA
        ReachingStar.MultiplierImpl.meth_RDY_getA
    | .getV => ofAVMethod0 meth_getV
        ReachingStar.MultiplierImpl.meth_RDY_getV
  rules
    | .mulStep => ofRule ReachingStar.MultiplierImpl.rule_mulStep
    | .mulStepFast => ofRule ReachingStar.MultiplierImpl.rule_mulStepFast
  init := fun s => s = { a := 0, b := 0, prod := 0, carry := 0, step := 0, busy := false }

theorem weakBisimu :
    equivalence ConstantModule SpecModule := by
  -- equivalence is two ways implication
  constructor
  · refine ⟨fun (i : ConstantModule.State) (s : SpecModule.State) =>
      -- either the spec and the implementation are busy, either they are finished with the result being the prod
      i.busy = s.busy ∧ (i.busy = false → s.result = i.prod), ?_⟩
      -- decomposition into initial state, internal rules and external rules (methods)
    refine ⟨?initial, ?internal, ?external⟩
    · intro i hi
      subst hi
      simp
      exact ⟨{ result := 0, busy := false }, rfl, rfl, fun _ => rfl⟩
    · intro s hstep hbusy hinv
      simp 
      


    · intro s hstep 
  · refine ⟨fun (s : SpecModule.State) (i : ConstantModule.State) =>
      i.busy = s.busy ∧ (i.busy = false → s.result = i.prod), ?_⟩
    refine ⟨?initial', ?internal', ?external'⟩
    · sorry
    · sorry
    · sorry
