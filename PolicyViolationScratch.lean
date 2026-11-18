import Multiplier
import NFI

open ReachingStar.Bluespec ReachingStar.Security
open ReachingStar.Bluespec.Multiplier
open BluespecPrelude

namespace ReachingStar.Security.PolicyViolationScratch

abbrev W := ReachingStar.MultiplierSpec.width
abbrev Mod := ReachingStar.MultiplierSpec.modulus

/-! ## A concrete interference witness: the multiplier does not respect `multPolicy`

`multPolicy` classifies the **first** operand of `put` as `high`. Non-interference ("respecting the
policy") demands that the low-observable behaviour not depend on any `high` input. We exhibit two
runs that differ **only** in that high first operand — `put(3,4)` vs `put(5,4)` — are therefore
indistinguishable to the policy there, yet the subsequent **low** `getV` returns different results
(12 vs 20). A low output that changes with a high input is interference, so the policy is violated. -/
theorem spec_leaks_high_operand :
    -- the differing operand (position 0 of `put`) is classified `high`
    multPolicy.argLevel ⟨.put, Footprint.arg2 (3 : BitVec W) (4 : BitVec W) Unit_⟩ (0 : Fin 2)
      = .high ∧
    -- run A: put(3,4) then getV, reading result `rA`
    (∃ (s0 sA : ReachingStar.MultiplierSpec.State) (rA : Nat),
        s0.busy = false ∧
        SpecModule.getMethod s0 ⟨.put, Footprint.arg2 (3 : BitVec W) (4 : BitVec W) Unit_⟩ sA ∧
        SpecModule.getMethod sA ⟨.getV, Footprint.arg0 rA⟩ sA ∧
    -- run B: put(5,4) then getV, reading result `rB`
      ∃ (sB : ReachingStar.MultiplierSpec.State) (rB : Nat),
        SpecModule.getMethod s0 ⟨.put, Footprint.arg2 (5 : BitVec W) (4 : BitVec W) Unit_⟩ sB ∧
        SpecModule.getMethod sB ⟨.getV, Footprint.arg0 rB⟩ sB ∧
    -- same low input (second operand 4), but different low outputs
        rA ≠ rB) := by
  refine ⟨EventLevels.ofList_arg2_fst (3 : BitVec W) (4 : BitVec W) Unit_
            TwoLevel.high TwoLevel.low TwoLevel.low TwoLevel.low, ?_⟩
  refine ⟨⟨0, false⟩,
          ⟨(3 : BitVec W).toNat * (4 : BitVec W).toNat % Mod, true⟩, _, rfl,
          ⟨3, 4, Unit_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
          ⟨(5 : BitVec W).toNat * (4 : BitVec W).toNat % Mod, true⟩, _,
          ⟨5, 4, Unit_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ?_⟩
  decide

end ReachingStar.Security.PolicyViolationScratch
