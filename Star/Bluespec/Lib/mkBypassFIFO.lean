-- mkBypassFIFO.lean - Formal spec for single-element bypass FIFO
-- Bypass FIFO: enq and deq can happen in the same cycle.
-- This is a hand-written opaque spec; the compiler treats mkBypassFIFO
-- as a black box and references this module.

import BluespecPrelude
open BluespecPrelude

namespace M_mkBypassFIFO

structure state (α : Type) [Inhabited α] where
  hasElement : Bool := false
  element : α := default
deriving Inhabited

-- Action methods (return t_actionvalue_ with updated state)

def meth_enq [Inhabited α] (s : state α) (x : α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { hasElement := true, element := x } }

def meth_deq [Inhabited α] (s : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { s with hasElement := false } }

def meth_clear [Inhabited α] (s : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := default }

-- Value methods

def meth_first [Inhabited α] (s : state α) : α :=
  s.element

-- Ready signals

def meth_RDY_enq [Inhabited α] (s : state α) : t_bool :=
  if s.hasElement then BFalse Unit_ else BTrue Unit_

def meth_RDY_deq [Inhabited α] (s : state α) : t_bool :=
  if s.hasElement then BTrue Unit_ else BFalse Unit_

def meth_RDY_first [Inhabited α] (s : state α) : t_bool :=
  if s.hasElement then BTrue Unit_ else BFalse Unit_

def meth_RDY_clear [Inhabited α] (_ : state α) : t_bool :=
  BTrue Unit_

end M_mkBypassFIFO
