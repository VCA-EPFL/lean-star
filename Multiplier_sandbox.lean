/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiplier
import Batteries.Tactic.OpenPrivate

/-!
# The multiplier with its high operand hardcoded

`ConcreteImpl` hardcodes the high operand of `put` to `0`. It behaves differently from `ImplModule`:
they are not weakly bisimilar (`concreteImpl_not_weaklyBisimilar`).
-/

open BluespecPrelude
open BluespecVerification
open ReachingStar.Security

namespace ReachingStar.Bluespec.Multiplier.Sandbox

open private idleI from Multiplier

/-- The operands of the multiplier. -/
abbrev Word := BitVec ReachingStar.MultiplierImpl.width

/-! ## The concretized `put` -/

/-- `meth_put` with its high operand hardcoded to `0`.

Arguments:
* `_`: the current state, ignored.
* `_v1`: the high operand, ignored.
* `v2`: the low operand. -/
def meth_put_concrete (_ : ReachingStar.MultiplierImpl.State) (_v1 v2 : Word) :
    t_actionvalue_ unit_ ReachingStar.MultiplierImpl.State :=
  { avValue_ := Unit_
  , avAction_ :=
      { a := 0
      , b := v2.toNat
      , prod := 0
      , carry := 0
      , step := 0
      , busy := true } }

/-! ## The concretized model -/

/-- The multiplier whose `put` is `meth_put_concrete`. -/
def ConcreteImpl : Bluespec.Module Rule Method where
  State := ReachingStar.MultiplierImpl.State
  methods
    | .put  => ofAVMethod2 meth_put_concrete ReachingStar.MultiplierImpl.meth_RDY_put
    | .getA => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getA
        ReachingStar.MultiplierImpl.meth_RDY_getA
    | .getV => ofAVMethod0 ReachingStar.MultiplierImpl.meth_getV
        ReachingStar.MultiplierImpl.meth_RDY_getV
  rules
    | .mulStep => ofRule ReachingStar.MultiplierImpl.rule_mulStep
    | .mulStepFast => ofRule ReachingStar.MultiplierImpl.rule_mulStepFast
  init := fun s => s = { a := 0, b := 0, prod := 0, carry := 0, step := 0, busy := false }

/-! ## The concretization is not the multiplier -/

/-- `ConcreteImpl` is the multiplier overwritten by `mulFix 0`.

Proof: The two have the same rules. For the methods, `put(v1, v2)` hardcoded to `0` is
`put(0, v2)`, which is what `mulFix 0` runs, and `getA` and `getV` run as themselves. -/
theorem concreteImpl_eq : ConcreteImpl = overwrite (mulFix 0) ImplModule := by
  have hr : ConcreteImpl.rules = (overwrite (mulFix 0) ImplModule).rules := by
    funext r
    cases r <;> rfl
  have hm : ConcreteImpl.methods = (overwrite (mulFix 0) ImplModule).methods := by
    funext n f s s'
    refine propext ?_
    cases n with
    | put =>
        constructor
        · rintro ⟨v1, v2, v, ha, rfl, r⟩
          exact ⟨⟨.put, Footprint.arg2 0 v2 v⟩, .inl ⟨v1, v2, v, rfl, rfl⟩, 0, v2, v, ha, rfl, r⟩
        · rintro ⟨e', (⟨v1, v2, v, he, rfl⟩ | ⟨hn, -⟩), hm⟩
          · injection he with _ hf
            subst hf
            obtain ⟨a1, a2, v', ha, hfp, r⟩ := hm
            injection hfp with _ _ _ _ hargs hret
            injection hargs with _ _ h0 ht
            injection ht with _ _ h1 _
            have e0 : (0 : Word) = a1 := h0
            have e2 : v2 = a2 := h1
            subst e0 e2
            cases v
            cases v'
            exact ⟨v1, v2, Unit_, ha, rfl, r⟩
          · exact absurd rfl hn
    | getA =>
        constructor
        · exact fun h => ⟨_, .inr ⟨(fun h => by cases h), rfl⟩, h⟩
        · rintro ⟨e', (⟨_, _, _, he, -⟩ | ⟨-, rfl⟩), hm⟩
          · cases he
          · exact hm
    | getV =>
        constructor
        · exact fun h => ⟨_, .inr ⟨(fun h => by cases h), rfl⟩, h⟩
        · rintro ⟨e', (⟨_, _, _, he, -⟩ | ⟨-, rfl⟩), hm⟩
          · cases he
          · exact hm
  have hi : ConcreteImpl.init = (overwrite (mulFix 0) ImplModule).init := rfl
  show Bluespec.Module.mk ReachingStar.MultiplierImpl.State _ _ _ =
    Bluespec.Module.mk ReachingStar.MultiplierImpl.State _ _ _
  exact congr(Bluespec.Module.mk ReachingStar.MultiplierImpl.State $hr $hm $hi)

/-- A module equal to the overwriting by `mulFix 0` is not weakly bisimilar to the multiplier.

Arguments:
* `h`: the module is the overwriting.
* `i`: its initial state.
* `hi`: `i` is `idleI`.

Proof: By `semF_overwrite` and `semF_concretize` the overwriting is `⟦M_0⟧^P`, so
`mul_not_weaklyBisimilar_M0` applies. -/
private theorem not_weaklyBisimilar_of_eq {m : Bluespec.Module Rule Method}
    (h : m = overwrite (mulFix 0) ImplModule) {i : m.State} (hi : HEq i idleI) :
    ¬ LTS.WeaklyBisimilar (mulPolicy.semF ImplModule idleI) (mulPolicy.semF m i) := by
  subst h
  cases hi
  rw [semF_overwrite (mulFix_fixes 0), ← TwoLevelPolicy.semF_concretize]
  exact mul_not_weaklyBisimilar_M0

/-- The hardcoded multiplier is not weakly bisimilar to the multiplier, through the policy.

Proof: `ConcreteImpl` is the overwriting by `mulFix 0`, which is `⟦M_0⟧^P`, so this is
`mul_not_weaklyBisimilar_M0`. -/
theorem concreteImpl_not_weaklyBisimilar :
    ¬ LTS.WeaklyBisimilar (mulPolicy.semF ImplModule idleI)
      (mulPolicy.semF ConcreteImpl idleI) :=
  not_weaklyBisimilar_of_eq concreteImpl_eq HEq.rfl

end ReachingStar.Bluespec.Multiplier.Sandbox
