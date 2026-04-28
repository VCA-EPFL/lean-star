-- mkSimpleBRAM2.lean - Formal spec for dual-port BRAM wrapper
-- Thin wrapper around mkBRAM2Server with flat putA/readA/putB/readB interface.
-- This is a hand-written opaque spec; the compiler treats mkSimpleBRAM2
-- as a black box and references this module.
--
-- ═══ Semantics ═══
-- Memory is a fixed-size 65536-slot array so that every `BitVec 16` address is
-- in bounds (matches BSV's typical 16-bit-addressed BRAM instantiation).
-- There is no explicit width parameter on `state`; clients pass a default-
-- initialized state and bounds are guaranteed structurally.
--
-- readResultA/B are `Option α` latches:
--   - `none` = no pending read result
--   - `some v` = previous port access latched value `v`
--
-- Port-access protocol:
--   - `meth_putA` requires `readResultA = none` (RDY_putA) — the latch must
--     be empty so the new read value has somewhere to land.
--   - `meth_readA` requires `readResultA = some _` (RDY_readA) — there must
--     be something to read; it returns the latched value and clears the latch.
--   - Symmetric for B.
--
-- This enforces the BSV BRAM "one outstanding read per port" discipline that
-- the previous constant-BTrue model silently violated.

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace M_mkSimpleBRAM2

-- Fixed-size 65536-slot dual-port BRAM. `readResultA/B` are Option latches
-- tracking whether a pending read is outstanding; RDY signals gate the
-- single-outstanding-read-per-port discipline.
structure state (α : Type) [Inhabited α] where
  memory : Array α := .mk (List.replicate 65536 default)
  readResultA : Option α := none
  readResultB : Option α := none
deriving Inhabited

-- putA: single-cycle port-A operation. With `write = BTrue`, performs a write
-- (memory[addr] := datain) and does NOT latch a read result — port A is doing
-- a write this cycle, no read in flight. With `write = BFalse`, issues a read
-- and latches memory[addr] into readResultA for consumption next cycle via
-- meth_readA.
--
-- Precondition (RDY_putA): readResultA must be `none` — we can't issue a new
-- read request while an unconsumed one is pending. (For writes this is trivially
-- satisfiable since writes don't populate the latch, but RDY is the same for
-- both modes to match BSV's single-method interface.)
def meth_putA [Inhabited α] (s : state α) (write : t_bool) (address : BitVec n)
    (datain : α) : t_actionvalue_ unit_ (state α) :=
  let idx := address.toNat
  match write with
  | BTrue _ =>
    -- Write: update memory, leave readResultA unchanged.
    { avValue_ := Unit_,
      avAction_ := { s with memory := s.memory.setIfInBounds idx datain } }
  | BFalse _ =>
    -- Read: latch memory[idx] into readResultA; memory unchanged.
    { avValue_ := Unit_,
      avAction_ := { s with readResultA := some (s.memory.getD idx default) } }

-- readA: return the latched port A value; clear the latch.
-- Precondition (encoded via RDY_readA): readResultA must be `some _`.
def meth_readA [Inhabited α] (s : state α) : t_actionvalue_ α (state α) :=
  { avValue_ := s.readResultA.getD default,
    avAction_ := { s with readResultA := none } }

-- putB: symmetric to putA.
def meth_putB [Inhabited α] (s : state α) (write : t_bool) (address : BitVec n)
    (datain : α) : t_actionvalue_ unit_ (state α) :=
  let idx := address.toNat
  match write with
  | BTrue _ =>
    { avValue_ := Unit_,
      avAction_ := { s with memory := s.memory.setIfInBounds idx datain } }
  | BFalse _ =>
    { avValue_ := Unit_,
      avAction_ := { s with readResultB := some (s.memory.getD idx default) } }

-- readB: symmetric to readA.
def meth_readB [Inhabited α] (s : state α) : t_actionvalue_ α (state α) :=
  { avValue_ := s.readResultB.getD default,
    avAction_ := { s with readResultB := none } }

-- RDY signals encode the latch discipline.
def meth_RDY_putA [Inhabited α] (s : state α) : t_bool :=
  match s.readResultA with | none => BTrue Unit_ | some _ => BFalse Unit_

def meth_RDY_readA [Inhabited α] (s : state α) : t_bool :=
  match s.readResultA with | some _ => BTrue Unit_ | none => BFalse Unit_

def meth_RDY_putB [Inhabited α] (s : state α) : t_bool :=
  match s.readResultB with | none => BTrue Unit_ | some _ => BFalse Unit_

def meth_RDY_readB [Inhabited α] (s : state α) : t_bool :=
  match s.readResultB with | some _ => BTrue Unit_ | none => BFalse Unit_

end M_mkSimpleBRAM2
