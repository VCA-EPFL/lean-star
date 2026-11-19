import Star.Bluespec.Basic

open ReachingStar.Bluespec

namespace ReachingStar.Bluespec

/-- Every argument of a footprint, each paired with its position: a list of dependent pairs
`⟨position, value⟩`. The arguments have different types, so they are returned as `Sigma`s, not a
plain `List` of one type. -/
def Footprint.argList (fp : Footprint) : List (Σ a : fp.α, fp.f a) :=
  fp.args.foldr (fun a x acc => ⟨a, x⟩ :: acc) []

/-- Every argument of a method call (an `Event`). -/
def Event.argList {M : Type _} (e : Event M) : List (Σ a : e.footprint.α, e.footprint.f a) :=
  e.footprint.argList

/-- Every argument of a method-or-rule: the method's arguments (each tagged with its footprint), or
`[]` for a rule, which carries no arguments. -/
def MethodOrRule.argList {R M : Type} :
    MethodOrRule R M → List (Σ fp : Footprint, Σ a : fp.α, fp.f a)
  | .rule _      => []
  | .method _ fp => fp.argList.map fun p => ⟨fp, p⟩

/-! ## Checks -/

/-- A two-argument method has two arguments. -/
example : (Footprint.arg2 (3 : BitVec 8) (4 : BitVec 8) ()).argList.length = 2 := rfl

/-- …and they are `3` at position 0 and `4` at position 1. -/
example : (Footprint.arg2 (3 : BitVec 8) (4 : BitVec 8) ()).argList
    = [⟨(0 : Fin 2), (3 : BitVec 8)⟩, ⟨(1 : Fin 2), (4 : BitVec 8)⟩] := rfl

/-- A zero-argument method has no arguments. -/
example : (Footprint.arg0 (5 : Nat)).argList.length = 0 := rfl

/-- A rule has no arguments. -/
example {R M : Type} (r : R) : (MethodOrRule.rule (M := M) r).argList = [] := rfl

/-- A method-or-rule carrying a `put(3,4)` footprint lists both operands. -/
example {R : Type} :
    (MethodOrRule.method (R := R) 0 (Footprint.arg2 (3 : BitVec 8) (4 : BitVec 8) ())).argList.length
      = 2 := rfl

end ReachingStar.Bluespec
