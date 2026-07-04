-- mkSimpleMem.lean - Formal spec for a simple, single, non-latching memory
-- array, used in place of Star.Bluespec.Lib.mkSimpleBRAM2's shared 2-port
-- BRAM model when instruction memory and data memory are split into two
-- separate arrays (see mktop_pipelined.lean).
--
-- Unlike mkSimpleBRAM2, this has no "outstanding read" latch/port state at
-- all: a read just returns `memory[addr]` directly (pure/combinational, no
-- RDY-gating needed), and a write just updates `memory[addr]` directly.
-- Splitting instruction/data memory into two of these (rather than two ports
-- into one shared mkSimpleBRAM2) also means a data write can never alias an
-- instruction read -- self-modifying code is not representable in this
-- model, by construction.
--
-- Memory is a fixed-size 65536-slot array so that every in-range address is
-- in bounds; out-of-bounds accesses are safely absorbed by `getD`/
-- `setIfInBounds` (read returns `default`, write is a no-op).

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace M_mkSimpleMem

def defaultMem [Inhabited α] : Array α := .mk (List.replicate 65536 default)

def read [Inhabited α] (mem : Array α) (address : BitVec n) : α :=
  mem.getD address.toNat default

def write [Inhabited α] (mem : Array α) (address : BitVec n) (datain : α) : Array α :=
  mem.setIfInBounds address.toNat datain

end M_mkSimpleMem
