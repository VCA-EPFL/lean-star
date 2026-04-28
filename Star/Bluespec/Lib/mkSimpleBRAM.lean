-- mkSimpleBRAM.lean - Formal spec for simple BRAM wrapper
-- Thin wrapper around mkBRAM1Server with flat put/read interface.
-- This is a hand-written opaque spec; the compiler treats mkSimpleBRAM
-- as a black box and references this module.

import BluespecPrelude
open BluespecPrelude

namespace M_mkSimpleBRAM

structure state (α : Type) [Inhabited α] where
  memory : Array α := .mk (List.replicate 8 default)  -- 8-word storage
  readResult : α := default                            -- latched read output
deriving Inhabited

-- put: latch the addressed word into readResult, then write if enabled
def meth_put [Inhabited α] (s : state α) (write : t_bool) (address : BitVec n) (datain : α) :
    t_actionvalue_ unit_ (state α) :=
  let idx := address.toNat
  let rdVal := s.memory.getD idx default
  let newMem := match write with
    | BTrue _ => s.memory.setIfInBounds idx datain
    | BFalse _ => s.memory
  { avValue_ := Unit_,
    avAction_ := { memory := newMem, readResult := rdVal } }

def meth_read [Inhabited α] (s : state α) : t_actionvalue_ α (state α) :=
  { avValue_ := s.readResult, avAction_ := s }

def meth_RDY_put [Inhabited α] (_ : state α) : t_bool :=
  BTrue Unit_

def meth_RDY_read [Inhabited α] (_ : state α) : t_bool :=
  BTrue Unit_

end M_mkSimpleBRAM
