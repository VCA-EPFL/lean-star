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
  pc : BitVec 32
deriving Inhabited, BEq

-- t_commit: the retirement/"commit" record pushed into the new commitQ FIFO
-- by rule_RL_writeback and read out by the external getCommit method, in
-- place of the old MMIO request/response interface (see mktop_pipelined.lean).
-- Reports exactly what the committing instruction did to architectural
-- state: the raw instruction word, which pc retired, and (if it writes a
-- destination register) which one and with what value.
structure t_commit where
  inst : BitVec 32
  pc : BitVec 32
  rdIdx : BitVec 5
  validRd : t_bool
  data : BitVec 32
deriving Inhabited, BEq

end Params_types
