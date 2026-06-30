import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Example.Bluealloc_types
import Star.Bluespec.Lib.mkSimpleBRAM2
open BluespecPrelude
open Bluealloc_types
open M_mkSimpleBRAM2

namespace M_mkBluealloc

structure state where
  bram_data : M_mkSimpleBRAM2.state (BitVec 32)
  bram_index : M_mkSimpleBRAM2.state (BitVec 16)
  bram_rever : M_mkSimpleBRAM2.state (BitVec 16)
  enqPtr : BitVec 16
  maxEver : BitVec 16
  opState : t_opstate
  opWriteData : BitVec 32
  freeStableAddr : BitVec 16
  freeUnstableAddr : BitVec 16
  freeLastStable : BitVec 16
  freeDataAtAddr : BitVec 32
  freeDataAtLast : BitVec 32
  allocState : t_allocstate
  allocNextStable : BitVec 16
deriving Inhabited

def rule_RL_do_read_index : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.opState == OP_READ_INDEX Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram_index) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_data)), { { { s with bram_index := (M_mkSimpleBRAM2.meth_readA s.bram_index).avAction_ } with bram_data := (M_mkSimpleBRAM2.meth_putA s.bram_data (BFalse Unit_) (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_index) 0).avValue default).avAction_ } with opState := OP_READ_DATA Unit_ })

def rule_RL_do_write_index : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.opState == OP_WRITE_INDEX Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram_index) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_data)), { { { s with bram_index := (M_mkSimpleBRAM2.meth_readA s.bram_index).avAction_ } with bram_data := (M_mkSimpleBRAM2.meth_putA s.bram_data (BTrue Unit_) (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_index) 0).avValue s.opWriteData).avAction_ } with opState := OP_IDLE Unit_ })

def rule_RL_do_free_lookup : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.opState == OP_FREE_LOOKUP Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram_index) (bool_and (M_mkSimpleBRAM2.meth_RDY_putA s.bram_data) (bool_and (M_mkSimpleBRAM2.meth_RDY_putB s.bram_data) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_rever)))), { { { { { s with bram_index := (M_mkSimpleBRAM2.meth_readA s.bram_index).avAction_ } with freeUnstableAddr := (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_index) 0).avValue } with bram_data := (M_mkSimpleBRAM2.meth_putB (M_mkSimpleBRAM2.meth_putA s.bram_data (BFalse Unit_) (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_index) 0).avValue default).avAction_ (BFalse Unit_) (s.enqPtr - (1 : BitVec 16)) default).avAction_ } with bram_rever := (M_mkSimpleBRAM2.meth_putA s.bram_rever (BFalse Unit_) (s.enqPtr - (1 : BitVec 16)) default).avAction_ } with opState := OP_FREE_READ Unit_ })

def rule_RL_do_free_read : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.opState == OP_FREE_READ Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram_data) (bool_and (M_mkSimpleBRAM2.meth_RDY_readB s.bram_data) (M_mkSimpleBRAM2.meth_RDY_readA s.bram_rever))), { { { { { { s with bram_data := (M_mkSimpleBRAM2.meth_readB (M_mkSimpleBRAM2.meth_readA s.bram_data).avAction_).avAction_ } with bram_rever := (M_mkSimpleBRAM2.meth_readA s.bram_rever).avAction_ } with freeDataAtAddr := (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_data) 0).avValue } with freeDataAtLast := (ActionValue (M_mkSimpleBRAM2.meth_readB s.bram_data) (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_data) 0).avWorld).avValue } with freeLastStable := (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_rever) (ActionValue (M_mkSimpleBRAM2.meth_readB s.bram_data) (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_data) 0).avWorld).avWorld).avValue } with opState := OP_FREE_WRITE Unit_ })

def rule_RL_do_free_write : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.opState == OP_FREE_WRITE Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_putA s.bram_data) (bool_and (M_mkSimpleBRAM2.meth_RDY_putB s.bram_data) (bool_and (M_mkSimpleBRAM2.meth_RDY_putA s.bram_rever) (bool_and (M_mkSimpleBRAM2.meth_RDY_putB s.bram_rever) (bool_and (M_mkSimpleBRAM2.meth_RDY_putA s.bram_index) (M_mkSimpleBRAM2.meth_RDY_putB s.bram_index)))))), { { { { { s with bram_data := (M_mkSimpleBRAM2.meth_putB (M_mkSimpleBRAM2.meth_putA s.bram_data (BTrue Unit_) s.freeUnstableAddr s.freeDataAtLast).avAction_ (BTrue Unit_) (s.enqPtr - (1 : BitVec 16)) s.freeDataAtAddr).avAction_ } with bram_rever := (M_mkSimpleBRAM2.meth_putB (M_mkSimpleBRAM2.meth_putA s.bram_rever (BTrue Unit_) s.freeUnstableAddr s.freeLastStable).avAction_ (BTrue Unit_) (s.enqPtr - (1 : BitVec 16)) s.freeStableAddr).avAction_ } with bram_index := (M_mkSimpleBRAM2.meth_putB (M_mkSimpleBRAM2.meth_putA s.bram_index (BTrue Unit_) s.freeLastStable s.freeUnstableAddr).avAction_ (BTrue Unit_) s.freeStableAddr (s.enqPtr - (1 : BitVec 16))).avAction_ } with enqPtr := (s.enqPtr - (1 : BitVec 16)) } with opState := OP_IDLE Unit_ })

def rule_RL_do_alloc_prefetch : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (bool_and (if ((s.allocState == AL_PREFETCH Unit_))
                           then BTrue Unit_
                           else BFalse Unit_) (if ((s.opState == OP_IDLE Unit_))
                                                 then BTrue Unit_
                                                 else BFalse Unit_)) (M_mkSimpleBRAM2.meth_RDY_putB s.bram_rever), match _ : (bool_not (if ((s.enqPtr < s.maxEver))
                                                                                                                                          then BTrue Unit_
                                                                                                                                          else BFalse Unit_)) with
                                                                                                                     | BTrue _ => { { s with allocNextStable := s.enqPtr } with allocState := AL_READY Unit_ }
                                                                                                                     | BFalse _ => { { s with bram_rever := (M_mkSimpleBRAM2.meth_putB s.bram_rever (BFalse Unit_) s.enqPtr default).avAction_ } with allocState := AL_WAIT Unit_ })

def rule_RL_do_alloc_wait : state → (t_bool × state) :=
  fun (s : state) =>
    (bool_and (if ((s.allocState == AL_WAIT Unit_))
                 then BTrue Unit_
                 else BFalse Unit_) (M_mkSimpleBRAM2.meth_RDY_readB s.bram_rever), { { { s with bram_rever := (M_mkSimpleBRAM2.meth_readB s.bram_rever).avAction_ } with allocNextStable := (ActionValue (M_mkSimpleBRAM2.meth_readB s.bram_rever) 0).avValue } with allocState := AL_READY Unit_ })

def meth_alloc : state → t_actionvalue_ (BitVec 16) state :=
  fun (s : state) =>
    { avValue_ := s.allocNextStable, avAction_ := { { { { { s with bram_index := match _ : (bool_not (if ((s.enqPtr < s.maxEver))
                                                                                                        then BTrue Unit_
                                                                                                        else BFalse Unit_)) with
                                                                                   | BTrue _ => (M_mkSimpleBRAM2.meth_putB s.bram_index (BTrue Unit_) s.enqPtr s.enqPtr).avAction_
                                                                                   | BFalse _ => s.bram_index } with bram_rever := match _ : (bool_not (if ((s.enqPtr < s.maxEver))
                                                                                                                                                          then BTrue Unit_
                                                                                                                                                          else BFalse Unit_)) with
                                                                                                                                     | BTrue _ => (M_mkSimpleBRAM2.meth_putB s.bram_rever (BTrue Unit_) s.enqPtr s.enqPtr).avAction_
                                                                                                                                     | BFalse _ => s.bram_rever } with maxEver := match _ : (bool_not (if ((s.enqPtr < s.maxEver))
                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                         else BFalse Unit_)) with
                                                                                                                                                                                    | BTrue _ => (s.enqPtr + (1 : BitVec 16))
                                                                                                                                                                                    | BFalse _ => s.maxEver } with enqPtr := (s.enqPtr + (1 : BitVec 16)) } with allocState := AL_PREFETCH Unit_ } }

def meth_RDY_alloc : state → t_bool :=
  fun (s : state) =>
    bool_and (bool_and (bool_and (if ((s.allocState == AL_READY Unit_))
                                    then BTrue Unit_
                                    else BFalse Unit_) (bool_not (if ((s.enqPtr == (65535 : BitVec 16)))
                                                                    then BTrue Unit_
                                                                    else BFalse Unit_))) (if ((s.opState == OP_IDLE Unit_))
                                                                                            then BTrue Unit_
                                                                                            else BFalse Unit_)) (bool_and (M_mkSimpleBRAM2.meth_RDY_putB s.bram_index) (M_mkSimpleBRAM2.meth_RDY_putB s.bram_rever))

def meth_free : state → BitVec 16 → t_actionvalue_ unit_ state :=
  fun (s : state) (free_f : BitVec 16) =>
    { avValue_ := default, avAction_ := { { { { s with freeStableAddr := free_f } with bram_index := (M_mkSimpleBRAM2.meth_putA s.bram_index (BFalse Unit_) free_f default).avAction_ } with opState := OP_FREE_LOOKUP Unit_ } with allocState := AL_PREFETCH Unit_ } }

def meth_RDY_free : state → t_bool :=
  fun (s : state) =>
    bool_and (bool_and (bool_and (if ((s.opState == OP_IDLE Unit_))
                                    then BTrue Unit_
                                    else BFalse Unit_) (if ((s.allocState == AL_READY Unit_))
                                                          then BTrue Unit_
                                                          else BFalse Unit_)) (bool_not (if ((s.enqPtr == (0 : BitVec 16)))
                                                                                           then BTrue Unit_
                                                                                           else BFalse Unit_))) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_index)

def meth_write_req : state → BitVec 16 → BitVec 32 → t_actionvalue_ unit_ state :=
  fun (s : state) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) =>
    { avValue_ := default, avAction_ := { { { s with opWriteData := write_req_data } with bram_index := (M_mkSimpleBRAM2.meth_putA s.bram_index (BFalse Unit_) write_req_addr default).avAction_ } with opState := OP_WRITE_INDEX Unit_ } }

def meth_RDY_write_req : state → t_bool :=
  fun (s : state) =>
    bool_and (bool_and (if ((s.opState == OP_IDLE Unit_))
                          then BTrue Unit_
                          else BFalse Unit_) (if ((s.allocState == AL_READY Unit_))
                                                then BTrue Unit_
                                                else BFalse Unit_)) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_index)

def meth_read_req : state → BitVec 16 → t_actionvalue_ unit_ state :=
  fun (s : state) (read_req_addr : BitVec 16) =>
    { avValue_ := default, avAction_ := { { s with bram_index := (M_mkSimpleBRAM2.meth_putA s.bram_index (BFalse Unit_) read_req_addr default).avAction_ } with opState := OP_READ_INDEX Unit_ } }

def meth_RDY_read_req : state → t_bool :=
  fun (s : state) =>
    bool_and (bool_and (if ((s.opState == OP_IDLE Unit_))
                          then BTrue Unit_
                          else BFalse Unit_) (if ((s.allocState == AL_READY Unit_))
                                                then BTrue Unit_
                                                else BFalse Unit_)) (M_mkSimpleBRAM2.meth_RDY_putA s.bram_index)

def meth_read_resp : state → t_actionvalue_ (BitVec 32) state :=
  fun (s : state) =>
    { avValue_ := (ActionValue (M_mkSimpleBRAM2.meth_readA s.bram_data) 0).avValue, avAction_ := { { s with bram_data := (M_mkSimpleBRAM2.meth_readA s.bram_data).avAction_ } with opState := OP_IDLE Unit_ } }

def meth_RDY_read_resp : state → t_bool :=
  fun (s : state) =>
    bool_and (if ((s.opState == OP_READ_DATA Unit_))
                then BTrue Unit_
                else BFalse Unit_) (bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram_data) (M_mkSimpleBRAM2.meth_RDY_readA s.bram_data))

end M_mkBluealloc
