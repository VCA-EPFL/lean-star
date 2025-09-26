/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Star

structure ARS (I : Type _) where
  A : Type _
  rules : I → A → A → Prop

inductive ARS.red_seq {I} (ars : ARS I) (i : I) : ars.A → ars.A → Prop where
| step {a b c} : ars.rules i a b → ars.red_seq i b c → ars.red_seq i a c
| refl {a} : ars.red_seq i a a

inductive ARS.indexed_red_seq {I} (ars : ARS I) : List I → ars.A → ars.A → Prop where
| step {i is a b c} : ars.rules i a b → ars.indexed_red_seq is b c → ars.indexed_red_seq (i :: is) a c
| refl {a} : ars.indexed_red_seq [] a a

-- Should union be an ∧ or an ∨?
def union {A} (α β : A → A → Prop) (s e : A) : Prop := α s e ∨ β s e
def inv {A} (α : A → A → Prop) (s e : A) : Prop := α e s
def symm {A} (α : A → A → Prop) : A → A → Prop := union α (inv α)

namespace Example

inductive xor : Bool → Bool → Bool → Prop where
| t_rule {b} : xor true b (¬ b)
| f_rule {b} : xor false b b

def ars : ARS Bool where
  A := Bool
  rules := xor

example : ARS.indexed_red_seq ars [true, false, true] true true := by repeat constructor

end Example

end Star
