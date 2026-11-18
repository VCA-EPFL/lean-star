import Multiplier
import NFI

open ReachingStar.Bluespec ReachingStar.Security
open ReachingStar.Bluespec.Multiplier

namespace ReachingStar.Security.HardcodedPolicyScratch

abbrev M := ReachingStar.Bluespec.Multiplier.Method

/-! ## A security policy hardcoded directly (no helper)

Instead of calling `Module.twoLevelPolicy`, the classification is written straight into the `levels`
field: match the label's method name and return the per-argument levels for that method. The
per-position levels are still read off the concrete footprint with `EventLevels.ofList`, which is
what keeps the policy total over every label. -/
noncomputable def multPolicyHardcoded : TwoLevelPolicy M where
  levels e := match e.name with
    | .put  => some (EventLevels.ofList e.footprint [.high, .low] .low .low)
    | .getA => some (EventLevels.ofList e.footprint []            .low .low)
    | .getV => some (EventLevels.ofList e.footprint []            .low .low)

/-! ## Worked example: it classifies a concrete `put` label -/

/-- On a `put(v1, v2)` label the policy returns the level list `[high, low]`. -/
example (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    multPolicyHardcoded.levels ⟨.put, Footprint.arg2 v1 v2 v⟩
      = some (EventLevels.ofList (Footprint.arg2 v1 v2 v) [.high, .low] .low .low) := rfl

/-- First operand of `put` is `high`. -/
example (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    (EventLevels.ofList (Footprint.arg2 v1 v2 v) [TwoLevel.high, .low] .low .low).args (0 : Fin 2)
      = .high :=
  EventLevels.ofList_arg2_fst v1 v2 v TwoLevel.high TwoLevel.low TwoLevel.low TwoLevel.low

/-- Second operand of `put` is `low`. -/
example (v1 v2 : BitVec ReachingStar.MultiplierImpl.width) (v : unit_) :
    (EventLevels.ofList (Footprint.arg2 v1 v2 v) [TwoLevel.high, .low] .low .low).args (1 : Fin 2)
      = .low :=
  EventLevels.ofList_arg2_snd v1 v2 v TwoLevel.high TwoLevel.low TwoLevel.low TwoLevel.low

/-- `getV` is a fully-low transition (it has no arguments). -/
example (v : Nat) :
    multPolicyHardcoded.levels ⟨.getV, Footprint.arg0 v⟩
      = some (EventLevels.ofList (Footprint.arg0 v) [] .low .low) := rfl

end ReachingStar.Security.HardcodedPolicyScratch
