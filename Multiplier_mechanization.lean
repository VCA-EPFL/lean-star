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

def rel (i:ReachingStar.MultiplierImpl.State) (s : ReachingStar.MultiplierSpec.State) : Prop :=
  i.busy = s.busy

def backRel (s : ReachingStar.MultiplierSpec.State) (i:ReachingStar.MultiplierImpl.State) :  Prop :=
  i.busy = s.busy ∧ ( i.busy = true → i.step = ReachingStar.MultiplierImpl.width )

def init_state : ReachingStar.MultiplierSpec.State :=
  { result := 0, busy := false }



-- proof that any state i that is busy and has exactly n steps left before step reaches width
theorem drain : ∀ n (i : ReachingStar.MultiplierImpl.State), i.busy = true →
    i.step + n = ReachingStar.MultiplierImpl.width →
    ∃ i'', Relation.ReflTransGen ConstantModule.getARule i i'' ∧ i''.busy = true ∧
      i''.step = ReachingStar.MultiplierImpl.width := by
  intro n
  -- proof by induction 
  induction n with
  -- base case 
  | zero =>
    intros i hb hs
    exists i
  -- induction step 
  | succ n ih =>
    intros i hb hs
    by_cases ha : i.a = 0
    -- mulStepFast case 
    · exists { i with prod := i.a, step := ReachingStar.MultiplierImpl.width }
      constructor
      · apply Relation.ReflTransGen.single
        exists .mulStepFast
        unfold ConstantModule Module.getRule ofRule MultiplierImpl.rule_mulStepFast
        simp_all
        omega
      · simp_all
    -- mulstep  case 
    · have hnext := ih
        { i with b := i.b / MultiplierImpl.base
                 prod := (MultiplierImpl.stepSum i % MultiplierImpl.base)
                   * MultiplierImpl.topPlace + i.prod / MultiplierImpl.base
                 carry := MultiplierImpl.stepSum i / MultiplierImpl.base
                 step := i.step + 1 } hb (by simp; omega)
      rcases hnext with ⟨i'', hr, hb'', hs''⟩
      exists i''
      constructor
      · apply Relation.ReflTransGen.head _ hr
        exists .mulStep
        unfold ConstantModule Module.getRule ofRule MultiplierImpl.rule_mulStep
        simp_all
        omega
      · exact ⟨hb'', hs''⟩

theorem weakBisimu :
    equivalence ConstantModule SpecModule := by
  -- equivalence is two ways implication
  constructor

  -- Breaking simulation into both directions 
  · unfold simulation
     -- introducing the relation 
    exists rel   
    constructor
    --proving the three properties of simulation
    -- starting states must be related
    · intros i h
      -- there exists a init state 
      exists init_state
      constructor 
      constructor
      unfold ConstantModule  at h 
      simp at h
      rw [ h]
      unfold rel init_state
      simp_all

    -- internal cases :  pairs of intenal states going through a rule should still be connected 
    · intros i i' s hi R 
      rcases hi with  ⟨ r,h⟩ 
      cases r
      -- rule is mulStep
      · unfold ConstantModule at h
        unfold Module.getRule  at h
        simp_all
        unfold ofRule at h
        unfold MultiplierImpl.rule_mulStep at h
        simp_all
        unfold rel 
        exists s
        constructor 
        · exact Relation.ReflTransGen.refl
        · split at h 
          · simp_all
            rw [← h ]
            unfold rel at R
            simp_all
          · simp at h
      -- rule is mulStepFast
      · unfold ConstantModule at h
        unfold Module.getRule  at h
        simp_all
        unfold ofRule at h
        unfold MultiplierImpl.rule_mulStepFast at h
        simp_all
        exists s
        constructor
        · exact Relation.ReflTransGen.refl
        · split at h
          · simp at h
            rw [← h]
            unfold rel at R
            unfold rel
            simp_all
          · simp at  h
    -- external cases 
    · intros i m i' s hm R
      rcases m with ⟨name, fp⟩
      cases name
      -- methods (externals rules), the follow the following sturcture
      -- Unfolding the ConstantModule def 
      -- isntantiating the two linked states
      -- unfolding wih the proposed relation 
      -- proving the relative transitive closure and the relation between the two starting, linked states
      · -- put
        unfold ConstantModule Module.getMethod ofAVMethod2 at hm
        simp at hm
        rcases hm with ⟨v1, v2, v, hput, hfp, hrdy⟩
        exists { result := (v1.toNat * v2.toNat) % MultiplierSpec.modulus, busy := true }
        exists { result := (v1.toNat * v2.toNat) % MultiplierSpec.modulus, busy := true }
        constructor
        · unfold SpecModule Module.getMethod ofAVMethod2
          exists v1, v2, v
          unfold rel at R
          simp_all [MultiplierImpl.meth_RDY_put, MultiplierSpec.meth_RDY_put, MultiplierSpec.meth_put]
          exact ⟨rfl, rfl⟩
        · constructor
          · exact Relation.ReflTransGen.refl
          · unfold MultiplierImpl.meth_put at hput
            simp at hput
            rw [← hput]
            unfold rel
            rfl
      · -- getA 
        unfold ConstantModule Module.getMethod ofAVMethod0 at hm
        simp at hm
        rcases hm with ⟨v, hgetA, hfp, hrdy⟩
        exists { s with busy := false }
        exists { s with busy := false }
        constructor
        · unfold SpecModule Module.getMethod ofAVMethod0
          exists v
          unfold rel at R
          simp_all [MultiplierImpl.meth_RDY_getA, MultiplierSpec.meth_RDY_getA, MultiplierSpec.meth_getA]
        · constructor
          · exact Relation.ReflTransGen.refl
          · unfold MultiplierImpl.meth_getA at hgetA
            simp at hgetA
            rw [← hgetA]
            unfold rel
            rfl
      · --getV
        unfold ConstantModule Module.getMethod ofAVMethod0 at hm
        simp at hm
        rcases hm with ⟨v, hgetV, hfp, hrdy⟩
        exists s
        exists s
        constructor
        · unfold SpecModule Module.getMethod ofAVMethod0
          exists v
          unfold rel at R
          unfold meth_getV at hgetV
          simp_all [meth_getV_app, MultiplierImpl.meth_RDY_getV, MultiplierSpec.meth_RDY_getV]
        · constructor
          · exact Relation.ReflTransGen.refl
          · unfold meth_getV at hgetV
            simp at hgetV
            rw [← hgetV.2]
            exact R
    -- Second implication
  · unfold simulation
    exists backRel
    constructor
    -- startign state     
    · intros s h
      exists { a := 0, b := 0, prod := 0, carry := 0, step := 0, busy := false }
      constructor
      · rfl
      · unfold SpecModule at h
        simp at h
        rw [h]
        unfold backRel
        simp_all
    -- internal state 
    · intros s s' i hs R
      rcases hs with ⟨r, h⟩
      cases r
    -- external states
    -- mainly follow the logic from the first implication except for the put function with the special drain function   
    · intros s m s' i hm R
      rcases m with ⟨name, fp⟩
      cases name
      -- put 
      ·
        unfold SpecModule Module.getMethod ofAVMethod2 at hm
        simp at hm
        rcases hm with ⟨v1, v2, v, hput, hfp, hrdy⟩
        have hdrain := drain MultiplierImpl.width (MultiplierImpl.init_state v1 v2) rfl
          (by unfold MultiplierImpl.init_state; simp)
        rcases hdrain with ⟨i'', hr, hb'', hs''⟩
        exists MultiplierImpl.init_state v1 v2
        exists i''
        constructor
        · unfold ConstantModule Module.getMethod ofAVMethod2
          exists v1, v2, v
          unfold backRel at R
          simp_all [MultiplierImpl.meth_RDY_put, MultiplierSpec.meth_RDY_put, MultiplierImpl.meth_put]
          exact ⟨rfl, rfl⟩
        · constructor
          · exact hr
          · unfold MultiplierSpec.meth_put at hput
            simp at hput
            rw [← hput]
            unfold backRel
            simp_all
      -- getA
      ·
        unfold SpecModule Module.getMethod ofAVMethod0 at hm
        simp at hm
        rcases hm with ⟨v, hgetA, hfp, hrdy⟩
        exists { i with busy := false }
        exists { i with busy := false }
        constructor
        · unfold ConstantModule Module.getMethod ofAVMethod0
          exists v
          unfold backRel at R
          simp_all [MultiplierImpl.meth_RDY_getA, MultiplierSpec.meth_RDY_getA, MultiplierImpl.meth_getA]
        · constructor
          · exact Relation.ReflTransGen.refl
          · unfold MultiplierSpec.meth_getA at hgetA
            simp at hgetA
            rw [← hgetA]
            unfold backRel
            simp
      -- getV 
      ·
        unfold SpecModule Module.getMethod ofAVMethod0 at hm
        simp at hm
        rcases hm with ⟨v, hgetV, hfp, hrdy⟩
        exists i
        exists i
        constructor
        · unfold ConstantModule Module.getMethod ofAVMethod0
          exists v
          unfold backRel at R
          unfold meth_getV_app at hgetV
          simp_all [meth_getV, MultiplierImpl.meth_RDY_getV, MultiplierSpec.meth_RDY_getV]
        · constructor
          · exact Relation.ReflTransGen.refl
          · unfold meth_getV_app at hgetV
            simp at hgetV
            rw [← hgetV.2]
            exact R



