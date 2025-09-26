/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Star

@[simp] abbrev Rule (A : Type _) := A → A → Prop

structure ARS (I : Type _) where
  A : Type _
  rules : I → Rule A

inductive trans {A} (rule : Rule A) : Rule A where
| step {a b c} : rule a b → trans rule b c → trans rule a c
| refl {a b} : rule a b → trans rule a b

def refl {A} (rule : Rule A) (s e : A) : Prop :=
  rule s e ∨ s = e

inductive trans_refl {A} (rule : Rule A) : Rule A where
| step {a b c} : rule a b → trans_refl rule b c → trans_refl rule a c
| refl {a} : trans_refl rule a a

inductive counted_trans_refl {A} (rule : Rule A) : A → A → Nat → Prop where
| step {a b c n} : rule a b → counted_trans_refl rule b c n → counted_trans_refl rule a c (n+1)
| refl {a} : counted_trans_refl rule a a 0

def ARS.red_seq {I} (ars : ARS I) (i : I) : Rule ars.A := trans_refl (ars.rules i)

inductive ARS.indexed_red_seq {I} (ars : ARS I) : List I → Rule ars.A where
| step {i is a b c} : ars.rules i a b → ars.indexed_red_seq is b c → ars.indexed_red_seq (i :: is) a c
| refl {a} : ars.indexed_red_seq [] a a

def union {A} (α β : Rule A) (s e : A) : Prop := α s e ∨ β s e
def inv {A} (α : Rule A) (s e : A) : Prop := α e s
def symm {A} (α : Rule A) : Rule A := union α (inv α)
def compose {A} (α β : Rule A) (s e : A) : Prop := ∃ s', α s s' ∧ β s' e

def commutes_weakly {A} (α β : Rule A) :=
  ∀ {a b c : A}, β a c → α a b → ∃ d, trans_refl α c d ∧ trans_refl β b d

def commutes {A} (α β : Rule A) := commutes_weakly (trans_refl α) (trans_refl β)

def weakly_confluent {A} (α : Rule A) := commutes_weakly α α

def is_subcommutative {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, refl α c d ∧ refl α b d

def has_diamond_property {A} (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d, α c d ∧ α b d

def is_confluent {A} (α : Rule A) := commutes α α

def is_nf {A} (α : Rule A) (a : A) : Prop :=
  ∀ b, ¬ α a b

def has_nf {A} (α : Rule A) (b : A) : Prop :=
  ∃ a, trans_refl α b a ∧ is_nf α a

def weakly_normalising {A} (α : Rule A) := ∀ a, has_nf α a

inductive strongly_normalising' {A} (α : Rule A) : A → Prop where
| step {a} : (∀ b, α a b → strongly_normalising' α b) → strongly_normalising' α a

def strongly_normalising {A} (α : Rule A) := ∀ a, strongly_normalising' α a

def is_inductive {A} (α : Rule A) :=
  ∀ a b n, counted_trans_refl α a b n → ∃ a', trans_refl α b a'

def is_increasing {A} (sz : A → Nat) (α : Rule A) :=
  ∀ a b, α a b → sz a < sz b

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
