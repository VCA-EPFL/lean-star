-- mkFIFO.lean - Custom opaque spec for the standard one-element pipeline FIFO.
--
-- The pipelined core uses `mkFIFO` (from the FIFO package) for its f2d/d2e/e2w
-- pipeline registers.  Unlike `mkBypassFIFO`, a plain `mkFIFO` does NOT allow
-- enq and deq of the same slot in the same clock — but in the rule-atomic
-- lean-star semantics that this translation targets, each rule fires
-- atomically and there is no intra-clock concurrency to distinguish the two.
-- The observable single-element-buffer behaviour (enq when empty, first/deq when
-- full) is therefore the same here as the bypass FIFO, so this model mirrors
-- `Star.Bluespec.Lib.mkBypassFIFO`.  (The enq/deq scheduling difference shows up
-- only in the clock-level schedule, which is abstracted away — it is part of why
-- the pipelined core only refines an atomic spec on the observable trace.)
--
-- The compiler treats mkFIFO as a black box and references this module
-- (`M_mkFIFO.meth_*`, `M_mkFIFO.state`).  Placed locally in the refines dir so
-- the generated `import mkFIFO` resolves here rather than in lean-star.

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace M_mkFIFO

structure state (α : Type) [Inhabited α] where
  hasElement : Bool := false
  element : α := default
deriving Inhabited

-- Action methods

def meth_enq [Inhabited α] (s : state α) (x : α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { hasElement := true, element := x } }

def meth_deq [Inhabited α] (s : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { s with hasElement := false } }

def meth_clear [Inhabited α] (_ : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := default }

-- Value method

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

end M_mkFIFO
