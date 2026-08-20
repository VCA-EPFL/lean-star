import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.CompiledProcessor.RVUtil
open BluespecPrelude
open RVUtil

namespace Params_types

structure t_mem where
  byte_en : BitVec 4
  addr : BitVec 32
  data : BitVec 32
deriving Inhabited

structure t_commitinst where
  pc : BitVec 32
  inst : BitVec 32
  rd : BitVec 5
  data : BitVec 32
deriving Inhabited

structure t_f2d where
  pc : BitVec 32
  ppc : BitVec 32
  iEp : BitVec 1
deriving Inhabited

structure t_membusiness where
  isUnsigned : t_bool
  size : BitVec 2
  offset : BitVec 2
deriving Inhabited

structure t_d2e where
  dInst : t_decodedinst
  pc : BitVec 32
  ppc : BitVec 32
  iEp : BitVec 1
  rv1 : BitVec 32
  rv2 : BitVec 32
deriving Inhabited

structure t_e2w where
  memBusiness : t_membusiness
  pc : BitVec 32
  data : BitVec 32
  dInst : t_decodedinst
deriving Inhabited

def default_mem : t_mem := { byte_en := 0, addr := 0, data := 0 }
instance : Inhabited t_mem where
  default := { byte_en := 0, addr := 0, data := 0 }

def default_commitinst : t_commitinst := { pc := 0, inst := 0, rd := 0, data := 0 }
instance : Inhabited t_commitinst where
  default := { pc := 0, inst := 0, rd := 0, data := 0 }

def default_f2d : t_f2d := { pc := 0, ppc := 0, iEp := 0 }
instance : Inhabited t_f2d where
  default := { pc := 0, ppc := 0, iEp := 0 }

def default_membusiness : t_membusiness := { isUnsigned := BFalse Unit_, size := 0, offset := 0 }
instance : Inhabited t_membusiness where
  default := { isUnsigned := BFalse Unit_, size := 0, offset := 0 }

def default_d2e : t_d2e := { dInst := default_decodedinst, pc := 0, ppc := 0, iEp := 0, rv1 := 0, rv2 := 0 }
instance : Inhabited t_d2e where
  default := { dInst := default_decodedinst, pc := 0, ppc := 0, iEp := 0, rv1 := 0, rv2 := 0 }

def default_e2w : t_e2w := { memBusiness := default_membusiness, pc := 0, data := 0, dInst := default_decodedinst }
instance : Inhabited t_e2w where
  default := { memBusiness := default_membusiness, pc := 0, data := 0, dInst := default_decodedinst }

end Params_types
