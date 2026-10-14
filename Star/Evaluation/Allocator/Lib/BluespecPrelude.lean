-- BluespecPrelude.lean - Standard operations for Bluespec Lean 4 translation
-- This file should be imported by all generated Lean 4 modules
import Lean

register_simp_attr bsv_rules
register_simp_attr bsv_methods
register_simp_attr bitvec_simp
register_simp_attr bool_simp

namespace BluespecPrelude


-- Typeclass for converting various types to Nat (for use in bit operations)
class ToNatBits (α : Type) where
  toNatBits : α → Nat

instance : ToNatBits Nat where
  toNatBits := id

instance : ToNatBits Int where
  toNatBits n := n.toNat

instance {n : Nat} : ToNatBits (BitVec n) where
  toNatBits := BitVec.toNat

-- Bitwise operations on BitVec
-- These use Lean 4's built-in BitVec type

def bit_and {n : Nat} (a b : BitVec n) : BitVec n := a &&& b
def bit_or  {n : Nat} (a b : BitVec n) : BitVec n := a ||| b
def bit_xor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b
def bit_not {n : Nat} (a : BitVec n) : BitVec n := ~~~ a

-- Shift operations (accept any type for shift amount via ToNatBits)
def shift_left {n : Nat} {α : Type} [ToNatBits α] (a : BitVec n) (k : α) : BitVec n :=
  a <<< (ToNatBits.toNatBits k)
def shift_right_logical {n : Nat} {α : Type} [ToNatBits α] (a : BitVec n) (k : α) : BitVec n :=
  a >>> (ToNatBits.toNatBits k)
def shift_right_arith {n : Nat} {α : Type} [ToNatBits α] (a : BitVec n) (k : α) : BitVec n :=
  BitVec.sshiftRight a (ToNatBits.toNatBits k)

-- BSV UInt#(n): unsigned integer of n bits. Same representation as BitVec n
-- but a distinct BSV type (used e.g. by countZerosMSB).
def BsvUInt (n : Nat) := BitVec n
instance : Inhabited (BsvUInt n) := ⟨(0 : BitVec n)⟩

-- Count leading zeros (MSB side). Returns the number of zero bits
-- above the highest set bit. For a zero input, returns n.
-- BSV type: Bit#(n) → UInt#(TLog(n+1))
def countZerosMSB {n : Nat} (x : BitVec n) : BsvUInt n :=
  (BitVec.ofNat n (n - x.toNat.log2 - (if x.toNat == 0 then 0 else 1)) : BitVec n)

-- BSV Bits typeclass: pack/unpack between a type and its bit representation.
class BsvBits (α : Type) (n : outParam Nat) where
  bsv_pack   : α → BitVec n
  bsv_unpack : BitVec n → α

-- BitVec n is trivially packable to itself
instance : BsvBits (BitVec n) n where
  bsv_pack x := x
  bsv_unpack x := x

-- UInt#(n) packs to Bit#(n)
instance : BsvBits (BsvUInt n) n where
  bsv_pack (x : BsvUInt n) := (x : BitVec n)
  bsv_unpack (x : BitVec n) := (x : BsvUInt n)

-- BSV truncate: reduces bit width (keeps low bits).
def bsv_truncate {n m : Nat} (x : BitVec n) : BitVec m := x.setWidth m


-- Bit extraction: extracts bits [high:low] from value
-- Uses ToNatBits for the value so it works with BitVec, Nat, and Int
def extract_bits {α : Type} [ToNatBits α] (value : α) (high low : Nat) : BitVec (high - low + 1) :=
  BitVec.ofNat (high - low + 1) (ToNatBits.toNatBits value >>> low)

-- Single-bit extraction: extract bit at position idx (returns BitVec 1)
-- Used when the index is a runtime value (avoids dependent type issues with extract_bits)
def extract_bit {α : Type} [ToNatBits α] (value : α) (idx : Nat) : BitVec 1 :=
  BitVec.ofNat 1 (ToNatBits.toNatBits value >>> idx)

-- Bit concatenation: concatenates hi and lo bit vectors
-- The explicit n parameter (width of lo) is placed before lo so that
-- Lean's type checker can resolve all metavariables during elaboration
def concat_bits {m : Nat} (hi : BitVec m) (n : Nat) (lo : BitVec n) : BitVec (m + n) :=
  hi ++ lo

-- Truncation/extension helpers
def truncate {n : Nat} (value : BitVec n) (width : Nat) : BitVec width :=
  BitVec.truncate width value

def sign_extend {n : Nat} {toWidth : Nat} (value : BitVec n) : BitVec toWidth :=
  BitVec.signExtend toWidth value

-- Alias for BSC-generated code
def signExtend {n : Nat} {toWidth : Nat} (value : BitVec n)  : BitVec toWidth :=
  BitVec.signExtend toWidth value

def zero_extend {n : Nat} (value : BitVec n) (toWidth : Nat) : BitVec toWidth :=
  BitVec.zeroExtend toWidth value

-- ActionValue type - represents an action that returns a value and new state
structure t_actionvalue_ (a s : Type) where
  avValue_ : a
  avAction_ : s
deriving BEq, Repr

-- ActionValue wrapper for extracting return values from ActionValue submodule methods.
-- The compiler generates: (ActionValue (submod.method state) world).avValue
-- where avValue extracts the method return value and avWorld tracks action ordering.
structure ActionValueResult (a : Type) where
  avValue : a
  avWorld : Nat

def ActionValue {a s : Type} (av : t_actionvalue_ a s) (world : Nat) : ActionValueResult a :=
  { avValue := av.avValue_, avWorld := world }

-- PrimPair type - BSC's internal pair type (Tuple2 in BSV)
structure t_primpair (a b : Type) where
  fst : a
  snd : b
deriving BEq, Repr, Inhabited

-- tuple2 constructor for PrimPair
def tuple2 {a b : Type} (x : a) (y : b) : t_primpair a b := ⟨x, y⟩

-- Unit type for Action methods that don't return a value
inductive unit_ where
  | Unit_
deriving DecidableEq, Repr, Inhabited

-- Unit value constant for Action methods
def unit_val : unit_ := unit_.Unit_

-- Maybe type - polymorphic option type for optional values
-- Invalid takes unit_ to match BSV's representation where constructors carry unit args
inductive t_maybe (a : Type) where
  | Invalid : unit_ → t_maybe a
  | Valid : a → t_maybe a
deriving BEq, Repr

instance : Inhabited (t_maybe a) where
  default := t_maybe.Invalid unit_.Unit_

-- Bool type - BSV Bool treated as enum for consistency
-- Use BTrue/BFalse to avoid conflict with Lean's built-in true/false
-- Constructors take unit_ to match BSV's representation
inductive t_bool where
  | BTrue : unit_ → t_bool
  | BFalse : unit_ → t_bool
deriving BEq, Repr

instance : Inhabited t_bool where
  default := t_bool.BFalse unit_.Unit_

-- Default value for Bool
def default_bool : t_bool := t_bool.BFalse unit_.Unit_

-- Boolean operations on t_bool. These are tagged [bool_simp] in
-- BluespecVerification.lean so `simp [bool_simp]` unfolds them.
def bool_and (a b : t_bool) : t_bool :=
  match a with
  | t_bool.BTrue _ => b
  | t_bool.BFalse _ => t_bool.BFalse unit_.Unit_

def bool_or (a b : t_bool) : t_bool :=
  match a with
  | t_bool.BTrue _ => t_bool.BTrue unit_.Unit_
  | t_bool.BFalse _ => b

def bool_not (a : t_bool) : t_bool :=
  match a with
  | t_bool.BTrue _ => t_bool.BFalse unit_.Unit_
  | t_bool.BFalse _ => t_bool.BTrue unit_.Unit_

-- BSV conditional: if-then-else with t_bool condition (no native Bool needed)
def ite_bsv {α : Type} (cond : t_bool) (t e : α) : α :=
  match cond with
  | t_bool.BTrue _ => t
  | t_bool.BFalse _ => e

-- Conversion helpers
def bool_to_int (a : t_bool) : Int :=
  match a with
  | t_bool.BTrue _ => 1
  | t_bool.BFalse _ => 0

def int_to_bool (a : Int) : t_bool :=
  if a == 0 then t_bool.BFalse unit_.Unit_ else t_bool.BTrue unit_.Unit_

-- Convert t_bool to BitVec 1 (for pack(Bool) in BSV)
def bool_to_bitvec1 (a : t_bool) : BitVec 1 :=
  match a with
  | t_bool.BTrue _ => 1
  | t_bool.BFalse _ => 0

-- Convert BitVec 1 to t_bool (for unpack(Bit#(1)) in BSV)
def bitvec1_to_bool (a : BitVec 1) : t_bool :=
  if a == 0 then t_bool.BFalse unit_.Unit_ else t_bool.BTrue unit_.Unit_

-- Roundtrip lemma: bitvec1_to_bool ∘ bool_to_bitvec1 = id
-- Used by termination proofs to simplify match discriminants in loop guards.
@[simp] theorem bitvec1_roundtrip (x : t_bool) :
    bitvec1_to_bool (bool_to_bitvec1 x) = x := by
  cases x <;> simp [bitvec1_to_bool, bool_to_bitvec1]

-- Array/Vector support using Lean's Array type
def arr_get {a : Type} [Inhabited a] (arr : Array a) (i : Nat) : a :=
  arr[i]!

def arr_set {a : Type} (arr : Array a) (i : Nat) (v : a) : Array a :=
  arr.set! i v

def arr_create {a : Type} (n : Nat) (default_val : a) : Array a :=
  Array.ofFn (fun _ : Fin n => default_val)

-- BSV Typeclasses
-- These correspond to BSV's typeclass system for polymorphic operations

-- Eq typeclass: equality comparison
-- The dictionary parameter is passed explicitly in generated code
structure t_eq (α : Type) where
  eq : α → α → t_bool

-- Equality operator using typeclass dictionary (passed explicitly)
-- Named eq_bsv to avoid conflicts with Lean's native ==
def eq_bsv {α : Type} (dict : t_eq α) (a b : α) : t_bool := dict.eq a b

-- SizedLiteral typeclass: conversion from integer literals to sized types
structure t_sizedliteral (α β : Type) where
  fromSizedInteger : Nat → α

-- PrimSelectable typeclass: bit selection operations
-- primSelect extracts a bit from a bitvector at a given index
-- The position parameter (first Nat) is an offset within a larger structure (often 0)
structure t_primselectable (α β : Type) where
  primSelectFn : Nat → α → Nat → β

-- Default Eq instances for BitVec
def t_eq_bitvec (n : Nat) : t_eq (BitVec n) where
  eq a b := if a == b then t_bool.BTrue unit_.Unit_ else t_bool.BFalse unit_.Unit_

-- Default SizedLiteral instances for BitVec
def t_sizedliteral_bitvec (n : Nat) : t_sizedliteral (BitVec n) (BitVec n) where
  fromSizedInteger x := BitVec.ofNat n x

-- Default PrimSelectable instances for BitVec
def t_primselectable_bitvec (n m : Nat) : t_primselectable (BitVec n) (BitVec m) where
  primSelectFn _pos bv idx := BitVec.ofNat m (bv.toNat >>> idx)

-- Ord typeclass: ordering operations (min, max)
-- The dictionary parameter is passed explicitly in generated code
structure t_ord (α : Type) where
  min : α → α → α
  max : α → α → α

-- Named bsv_min/bsv_max to provide the explicit-dict interface used in generated code
def min {α : Type} (dict : t_ord α) (a b : α) : α := dict.min a b
def max {α : Type} (dict : t_ord α) (a b : α) : α := dict.max a b

-- Export constructors so they are available unqualified when this namespace is opened
export unit_ (Unit_)
export t_bool (BTrue BFalse)
export t_maybe (Invalid Valid)

end BluespecPrelude

-- BSC typeclass dictionary instances
-- These follow BSC's naming convention: Prelude.<TypeClass>_Prelude.<Type>
namespace Prelude

namespace Eq_Prelude
-- Eq instance for BitVec n - polymorphic in n
def Bit_n : BluespecPrelude.t_eq (BitVec n) where
  eq a b := if a == b then BluespecPrelude.t_bool.BTrue BluespecPrelude.unit_.Unit_
            else BluespecPrelude.t_bool.BFalse BluespecPrelude.unit_.Unit_
end Eq_Prelude

namespace SizedLiteral_Prelude
-- SizedLiteral instance for BitVec n - polymorphic in n
def Bit_n_n : BluespecPrelude.t_sizedliteral (BitVec n) (BitVec n) where
  fromSizedInteger x := BitVec.ofNat n x
end SizedLiteral_Prelude

namespace PrimSelectable_Prelude
namespace Bit_n_Prelude
-- PrimSelectable instance for BitVec n to BitVec 1
def Bit_1 : BluespecPrelude.t_primselectable (BitVec n) (BitVec 1) where
  primSelectFn _pos bv idx := BitVec.ofNat 1 (bv.toNat >>> idx)
end Bit_n_Prelude
end PrimSelectable_Prelude

namespace Ord_Prelude
-- Ord instance for BitVec n - unsigned comparison (matches BSV Bit#(n) ordering)
def Bit_n {n : Nat} : BluespecPrelude.t_ord (BitVec n) where
  min a b := if a.toNat ≤ b.toNat then a else b
  max a b := if a.toNat ≥ b.toNat then a else b
end Ord_Prelude

end Prelude

-- Allow .toNat on Nat values (identity conversion, for uniformity with BitVec.toNat
-- in generated code where loop counters i : Nat appear as array indices)
namespace Nat
  def toNat (n : Nat) : Nat := n
end Nat
