-- Params_types.lean - Lean translation of Params.bsv's struct declarations,
-- shared between M_mkpipelined and M_mktop_pipelined.

import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.SimpleProcessor.RVUtil
open BluespecPrelude

namespace Params_types

structure t_mem where
  byte_en : BitVec 4
  addr : BitVec 32
  data : BitVec 32
deriving Inhabited, BEq

structure t_membusiness where
  isUnsigned : t_bool
  size : BitVec 2
  offset : BitVec 2
  mmio : t_bool
deriving Inhabited, BEq

structure t_f2d where
  pc : BitVec 32
  ppc : BitVec 32
  idEp : BitVec 1
  ieEp : BitVec 1
deriving Inhabited, BEq

structure t_d2e where
  dInst : RVUtil.DecodedInst
  pc : BitVec 32
  ppc : BitVec 32
  ieEp : BitVec 1
  rv1 : BitVec 32
  rv2 : BitVec 32
deriving Inhabited, BEq

structure t_e2w where
  memBusiness : t_membusiness
  data : BitVec 32
  dInst : RVUtil.DecodedInst
deriving Inhabited, BEq

-- function Bool isMMIO(Bit#(32) addr) from pipelined.bsv: word-aligned addresses
-- of the three MMIO registers (STDERR char/int write, sim exit).
def isMMIO (addr : BitVec 32) : t_bool :=
  if addr == (0xf000fff0 : BitVec 32) || addr == (0xf000fff4 : BitVec 32)
      || addr == (0xf000fff8 : BitVec 32)
  then BTrue Unit_ else BFalse Unit_

end Params_types
