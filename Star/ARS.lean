/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Star

structure ARS (I : Type _) where
  A : Type _
  rules : I → A → A → Prop

inductive trans {A} (rule : A → A → Prop) : A → A → Prop where
| step {a b c} : rule a b → trans rule b c → trans rule a c
| refl {a b} : rule a b → trans rule a b

def refl {A} (rule : A → A → Prop) (s e : A) : Prop :=
  rule s e ∨ s = e

inductive trans_refl {A} (rule : A → A → Prop) : A → A → Prop where
| step {a b c} : rule a b → trans_refl rule b c → trans_refl rule a c
| refl {a} : trans_refl rule a a

def ARS.red_seq {I} (ars : ARS I) (i : I) : ars.A → ars.A → Prop := trans_refl (ars.rules i)

inductive ARS.indexed_red_seq {I} (ars : ARS I) : List I → ars.A → ars.A → Prop where
| step {i is a b c} : ars.rules i a b → ars.indexed_red_seq is b c → ars.indexed_red_seq (i :: is) a c
| refl {a} : ars.indexed_red_seq [] a a

-- Should union be an ∧ or an ∨ (pretty sure it is ∨, but then `symm` seems a bit weird)?
def union {A} (α β : A → A → Prop) (s e : A) : Prop := α s e ∨ β s e
def inv {A} (α : A → A → Prop) (s e : A) : Prop := α e s
def symm {A} (α : A → A → Prop) : A → A → Prop := union α (inv α)
def compose {A} (α β : A → A → Prop) (s e : A) : Prop := ∃ s', α s s' ∧ β s' e

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
