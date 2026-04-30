import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace Bluealloc_types

inductive t_allocstate where
  | AL_PREFETCH : unit_ → t_allocstate
  | AL_WAIT : unit_ → t_allocstate
  | AL_READY : unit_ → t_allocstate
deriving BEq
open t_allocstate
export t_allocstate (AL_PREFETCH AL_WAIT AL_READY)
-- OfNat instances for integer comparisons
instance : OfNat t_allocstate 0 where
  ofNat := AL_PREFETCH default
instance : OfNat t_allocstate 1 where
  ofNat := AL_WAIT default
instance : OfNat t_allocstate 2 where
  ofNat := AL_READY default

inductive t_opstate where
  | OP_IDLE : unit_ → t_opstate
  | OP_READ_INDEX : unit_ → t_opstate
  | OP_READ_DATA : unit_ → t_opstate
  | OP_WRITE_INDEX : unit_ → t_opstate
  | OP_FREE_LOOKUP : unit_ → t_opstate
  | OP_FREE_READ : unit_ → t_opstate
  | OP_FREE_WRITE : unit_ → t_opstate
deriving DecidableEq
open t_opstate
export t_opstate (OP_IDLE OP_READ_INDEX OP_READ_DATA OP_WRITE_INDEX OP_FREE_LOOKUP OP_FREE_READ OP_FREE_WRITE)
-- OfNat instances for integer comparisons
instance : OfNat t_opstate 0 where
  ofNat := OP_IDLE default
instance : OfNat t_opstate 1 where
  ofNat := OP_READ_INDEX default
instance : OfNat t_opstate 2 where
  ofNat := OP_READ_DATA default
instance : OfNat t_opstate 3 where
  ofNat := OP_WRITE_INDEX default
instance : OfNat t_opstate 4 where
  ofNat := OP_FREE_LOOKUP default
instance : OfNat t_opstate 5 where
  ofNat := OP_FREE_READ default
instance : OfNat t_opstate 6 where
  ofNat := OP_FREE_WRITE default

def default_allocstate : t_allocstate := AL_PREFETCH Unit_
instance : Inhabited t_allocstate where
  default := AL_PREFETCH Unit_

def default_opstate : t_opstate := OP_IDLE Unit_
instance : Inhabited t_opstate where
  default := OP_IDLE Unit_



end Bluealloc_types
