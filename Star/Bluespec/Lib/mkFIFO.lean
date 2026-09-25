-- mkFIFO.lean - Custom opaque spec for `mkFIFO`, modelled as an unbounded FIFO.
--
-- The pipelined core uses `mkFIFO` (from the FIFO package) for its f2d/d2e/e2w
-- pipeline registers.  The hardware FIFO has a fixed depth, but here it is
-- abstracted as an unbounded queue: `enq` is always ready and appends to the
-- back, `first`/`deq` read/remove the front and are ready whenever the queue is
-- non-empty.  In the rule-atomic lean-star semantics each rule fires
-- atomically, so there is no intra-clock enq/deq concurrency to model.
--
-- The compiler treats mkFIFO as a black box and references this module
-- (`M_mkFIFO.meth_*`, `M_mkFIFO.state`).  Placed locally in the refines dir so
-- the generated `import mkFIFO` resolves here rather than in lean-star.

import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace M_mkFIFO

structure state (α : Type) [Inhabited α] where
  queue : List α := []
deriving Inhabited

-- Action methods

def meth_enq [Inhabited α] (s : state α) (x : α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { queue := s.queue ++ [x] } }

def meth_deq [Inhabited α] (s : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := { queue := s.queue.tail } }

def meth_clear [Inhabited α] (_ : state α) : t_actionvalue_ unit_ (state α) :=
  { avValue_ := Unit_, avAction_ := default }

-- Value method

def meth_first [Inhabited α] (s : state α) : α :=
  s.queue.headD default

-- Ready signals

def meth_RDY_enq [Inhabited α] (_ : state α) : t_bool :=
  BTrue Unit_

def meth_RDY_deq [Inhabited α] (s : state α) : t_bool :=
  if s.queue.isEmpty then BFalse Unit_ else BTrue Unit_

def meth_RDY_first [Inhabited α] (s : state α) : t_bool :=
  if s.queue.isEmpty then BFalse Unit_ else BTrue Unit_

def meth_RDY_clear [Inhabited α] (_ : state α) : t_bool :=
  BTrue Unit_

end M_mkFIFO
