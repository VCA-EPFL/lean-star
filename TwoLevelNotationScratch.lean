import SecurityPolicy

open ReachingStar.Security

namespace ReachingStar.Security

/-- Shorthand for `TwoLevel.sup` (join / least upper bound). -/
scoped infixl:65 " ⊔ᵗ " => TwoLevel.sup

/-- Shorthand for `TwoLevel.inf` (meet / greatest lower bound). -/
scoped infixl:70 " ⊓ᵗ " => TwoLevel.inf

-- checks (reduce by rfl, unlike the typeclass ⊔ / ⊓)
example : TwoLevel.high ⊔ᵗ .low = .high := rfl
example : TwoLevel.low  ⊔ᵗ .low = .low  := rfl
example : TwoLevel.high ⊓ᵗ .low = .low  := rfl
example : TwoLevel.high ⊓ᵗ .high = .high := rfl

end ReachingStar.Security
