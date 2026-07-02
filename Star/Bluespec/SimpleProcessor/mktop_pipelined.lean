-- mktop_pipelined.lean - Flattened Lean formalization of
-- Star/Bluespec/simple-processor/top_pipelined.bsv (module mktop_pipelined)
-- together with its instantiated pipelined RISC-V core
-- (Star/Bluespec/simple-processor/pipelined.bsv, module mkpipelined,
-- interface RVIfc). Rather than keeping `rvCore` as a nested
-- M_mkpipelined.state field reached through its RVIfc methods (as a
-- hierarchical/compositional spec would), this file inlines mkpipelined's
-- registers directly into `state` and its rules directly into this module's
-- rule set -- mirroring how a real Bluespec flattened synthesis merges every
-- instantiated submodule's rules into one scheduler. The standalone,
-- non-flattened spec of the core still lives in
-- Star.Bluespec.SimpleProcessor.mkpipelined (M_mkpipelined); it is not
-- imported here since nothing in this file goes through its interface
-- anymore.
--
-- Every `Queue`-module FIFO (toImem/fromImem/toDmem/fromDmem/toMMIO/
-- fromMMIO/f2d/d2e/e2w/dreq/mmioreq) is likewise flattened: instead of a
-- nested `M_mkBypassFIFO.state _` field reached through meth_enq/meth_deq/
-- meth_first/meth_RDY_*, each FIFO's own two fields (`hasElement : Bool`,
-- `element : α`, per Star.Bluespec.Lib.mkBypassFIFO) are lifted directly
-- into `state` under an instance-name prefix (e.g. `toImem_hasElement`/
-- `toImem_element`), and the enq/deq/first/RDY logic is inlined against
-- those two fields via the local `fifo_RDY_enq`/`fifo_RDY_deq` helpers
-- below (enq sets `hasElement := true, element := x`; deq only clears
-- `hasElement`, leaving `element` stale as mkBypassFIFO itself does; first
-- just reads `element`). `Star.Bluespec.Lib.mkBypassFIFO` is therefore no
-- longer imported either.
--
-- `bram` (BRAM2PortBE) is not a FIFO and is left as a nested
-- Star.Bluespec.Lib.mkSimpleBRAM2 submodule -- see the caveats on
-- putA_withResponse/putB_withResponse below for what that reuse loses.
--
-- `mktop_pipelined` implements the `Top` interface: MMIO handling is
-- external (there is no requestMMIO/responseMMIO rule -- those, and their
-- console-echo/PASS-FAIL/$finish side effects, existed only in an earlier
-- revision of the source); getMMIOReqA/getMMIOReqV directly expose the
-- core's toMMIO queue, and an external caller is expected to drive
-- getMMIOResp with the response. Note that `mmioreq` is declared in the
-- source but nothing enqueues into it (the rule that used to fill it is
-- gone), so meth_RDY_getMMIOResp below is unreachable (mmioreq never
-- becomes non-empty) -- this mirrors the source faithfully rather than
-- "fixing" it.

import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
open BluespecPrelude
open Params_types

namespace M_mktop_pipelined

structure state where
  -- pipelined.bsv (RVIfc core), flattened, FIFOs flattened to hasElement/element pairs
  toImem_hasElement : Bool := false
  toImem_element : t_mem := default
  fromImem_hasElement : Bool := false
  fromImem_element : t_mem := default
  toDmem_hasElement : Bool := false
  toDmem_element : t_mem := default
  fromDmem_hasElement : Bool := false
  fromDmem_element : t_mem := default
  toMMIO_hasElement : Bool := false
  toMMIO_element : t_mem := default
  fromMMIO_hasElement : Bool := false
  fromMMIO_element : t_mem := default
  f2d_hasElement : Bool := false
  f2d_element : t_f2d := default
  d2e_hasElement : Bool := false
  d2e_element : t_d2e := default
  e2w_hasElement : Bool := false
  e2w_element : t_e2w := default
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  sb : Array (BitVec 2) := .mk (List.replicate 32 default)
  dEp : BitVec 1
  eEp : BitVec 1
  -- top_pipelined.bsv itself
  bram : M_mkSimpleBRAM2.state (BitVec 32)
  ireq : t_mem
  dreq_hasElement : Bool := false
  dreq_element : t_mem := default
  mmioreq_hasElement : Bool := false
  mmioreq_element : t_mem := default
deriving Inhabited

-- Single-slot FIFO ready signals (Star.Bluespec.Lib.mkBypassFIFO's
-- meth_RDY_enq/meth_RDY_deq/meth_RDY_first, inlined: RDY_first uses the same
-- condition as RDY_deq).
def fifo_RDY_enq (hasElement : Bool) : t_bool := if hasElement then BFalse Unit_ else BTrue Unit_
def fifo_RDY_deq (hasElement : Bool) : t_bool := if hasElement then BTrue Unit_ else BFalse Unit_

-- function Bool isMMIO(Bit#(32) addr) from pipelined.bsv: word-aligned addresses
-- of the three MMIO registers (STDERR char/int write, sim exit).
def isMMIO (addr : BitVec 32) : t_bool :=
  if addr == (0xf000fff0 : BitVec 32) || addr == (0xf000fff4 : BitVec 32)
      || addr == (0xf000fff8 : BitVec 32)
  then BTrue Unit_ else BFalse Unit_

-- portA/B.request.put(BRAMRequestBE{writeen, responseOnWrite: True, address, datain})
-- with mkSimpleBRAM2 as the underlying model: `byte_en = 0` reads (latching a
-- response as usual); any nonzero `byte_en` is treated as a full-word write of
-- `datain`, and (since responseOnWrite is always True at both call sites in
-- top_pipelined.bsv) the written value is also latched as the response.
def putA_withResponse (bram : M_mkSimpleBRAM2.state (BitVec 32)) (byte_en : BitVec 4)
    (address : BitVec 20) (datain : BitVec 32) : M_mkSimpleBRAM2.state (BitVec 32) :=
  let isWrite := if byte_en == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
  let afterWrite := (M_mkSimpleBRAM2.meth_putA bram isWrite address datain).avAction_
  match _ : isWrite with
  | BTrue _ => { afterWrite with readResultA := some datain }
  | BFalse _ => afterWrite

def putB_withResponse (bram : M_mkSimpleBRAM2.state (BitVec 32)) (byte_en : BitVec 4)
    (address : BitVec 20) (datain : BitVec 32) : M_mkSimpleBRAM2.state (BitVec 32) :=
  let isWrite := if byte_en == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
  let afterWrite := (M_mkSimpleBRAM2.meth_putB bram isWrite address datain).avAction_
  match _ : isWrite with
  | BTrue _ => { afterWrite with readResultB := some datain }
  | BFalse _ => afterWrite

------------------------------------------------------------------------
-- pipelined.bsv rules (mkpipelined), inlined over the flat `state`
------------------------------------------------------------------------

-- rule fetch: always fires (subject to f2d/toImem being ready); no guard in source.
def rule_RL_fetch : state → (t_bool × state) :=
  fun (s : state) =>
    let ppc := s.pc + (4 : BitVec 32)
    let f2dEntry : t_f2d := { pc := s.pc, ppc := ppc, idEp := s.dEp, ieEp := s.eEp }
    let req : t_mem := { byte_en := 0, addr := s.pc, data := 0 }
    (bool_and (fifo_RDY_enq s.f2d_hasElement) (fifo_RDY_enq s.toImem_hasElement),
      { { { s with f2d_hasElement := true, f2d_element := f2dEntry }
            with pc := ppc }
        with toImem_hasElement := true, toImem_element := req })

-- rule decode: either squash (f2d/fromImem epoch stale w.r.t. dEp/eEp) or, once
-- operands clear the scoreboard, decode + issue into d2e and bump the scoreboard.
def rule_RL_decode : state → (t_bool × state) :=
  fun (s : state) =>
    let instr := s.fromImem_element.data
    let fromFetch := s.f2d_element
    let decodedInst := RVUtil.decodeInst instr
    let fields := RVUtil.getInstFields instr
    let rdIdx := fields.rd
    let rs1Idx := fields.rs1
    let rs2Idx := fields.rs2
    let epochMismatch :=
      bool_or (bool_not (if fromFetch.idEp == s.dEp then BTrue Unit_ else BFalse Unit_))
              (bool_not (if fromFetch.ieEp == s.eEp then BTrue Unit_ else BFalse Unit_))
    let rs1Ready :=
      bool_or (bool_and decodedInst.valid_rs1
                 (if arr_get s.sb rs1Idx.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
              (bool_not decodedInst.valid_rs1)
    let rs2Ready :=
      bool_or (bool_and decodedInst.valid_rs2
                 (if arr_get s.sb rs2Idx.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
              (bool_not decodedInst.valid_rs2)
    let operandsReady := bool_and rs1Ready rs2Ready

    -- squash branch: drop the stale fetched instruction, no issue into d2e
    let squashState : state :=
      { { s with f2d_hasElement := false }
          with fromImem_hasElement := false }

    -- decode branch: read rf (x0 hardwired to 0), resolve redirects, issue to d2e
    let rs1 := ite_bsv (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                 (0 : BitVec 32) (arr_get s.rf rs1Idx.toNat)
    let rs2 := ite_bsv (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
                 (0 : BitVec 32) (arr_get s.rf rs2Idx.toNat)
    let immVal := RVUtil.getImmediate decodedInst
    let ppcNew := ite_bsv (RVUtil.isJALR decodedInst)
                    (bit_and (rs1 + immVal) (bit_not (1 : BitVec 32)))
                    (fromFetch.pc + immVal)
    let isJump := bool_or (RVUtil.isJAL decodedInst) (RVUtil.isJALR decodedInst)
    let redirected :=
      bool_and isJump (bool_not (if fromFetch.ppc == ppcNew then BTrue Unit_ else BFalse Unit_))
    let d2eEntry : t_d2e :=
      { dInst := decodedInst, pc := fromFetch.pc,
        ppc := ite_bsv redirected ppcNew fromFetch.ppc,
        ieEp := fromFetch.ieEp, rv1 := rs1, rv2 := rs2 }
    let rdCond := bool_and decodedInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
    let decodeState : state :=
      { { { { { s with pc := ite_bsv redirected ppcNew s.pc }
                with dEp := s.dEp + ite_bsv redirected (1 : BitVec 1) (0 : BitVec 1) }
              with d2e_hasElement := true, d2e_element := d2eEntry }
            with sb := arr_set s.sb rdIdx.toNat
                         ((arr_get s.sb rdIdx.toNat) + ite_bsv rdCond (1 : BitVec 2) (0 : BitVec 2)) }
        with f2d_hasElement := false }
    let decodeState' : state := { decodeState with fromImem_hasElement := false }

    let fireGuard :=
      bool_and (fifo_RDY_deq s.fromImem_hasElement)
        (bool_and (fifo_RDY_deq s.f2d_hasElement)
          (bool_and (bool_or epochMismatch operandsReady)
            (bool_and (fifo_RDY_deq s.f2d_hasElement)
              (bool_and (fifo_RDY_deq s.fromImem_hasElement)
                (match _ : epochMismatch with
                  | BTrue _ => BTrue Unit_
                  | BFalse _ => fifo_RDY_enq s.d2e_hasElement)))))
    (fireGuard, match _ : epochMismatch with
      | BTrue _ => squashState
      | BFalse _ => decodeState')

-- rule execute: on a stale (squashed) instruction, just undo its scoreboard
-- reservation; otherwise run the ALU/branch-resolution/address-generation logic
-- and issue a memory (or MMIO) request, or update pc/eEp for a taken branch.
def rule_RL_execute : state → (t_bool × state) :=
  fun (s : state) =>
    let d2eEntry := s.d2e_element
    let dInst := d2eEntry.dInst
    let dPc := d2eEntry.pc
    let ppc := d2eEntry.ppc
    let ieEp := d2eEntry.ieEp
    let rv1 := d2eEntry.rv1
    let rv2 := d2eEntry.rv2
    let ieEpMismatch := bool_not (if ieEp == s.eEp then BTrue Unit_ else BFalse Unit_)

    -- squash branch: instruction was speculatively issued after a redirect
    -- that has since happened; just release its scoreboard reservation.
    let squashRdIdx := (RVUtil.getInstFields dInst.inst).rd
    let squashCond := bool_and dInst.valid_rd (bool_not (if squashRdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
    let squashState : state :=
      { { s with sb := arr_set s.sb squashRdIdx.toNat
                   ((arr_get s.sb squashRdIdx.toNat) + ite_bsv squashCond (-1 : BitVec 2) (0 : BitVec 2)) }
          with d2e_hasElement := false }

    -- normal branch
    let imm := RVUtil.getImmediate dInst
    let funct3 := (RVUtil.getInstFields dInst.inst).funct3
    let size := extract_bits funct3 1 0
    let addr0 := rv1 + imm
    let offset := extract_bits addr0 1 0
    let dataCtrl := ite_bsv (RVUtil.isControlInst dInst) (dPc + (4 : BitVec 32))
                      (RVUtil.execALU32 dInst.inst rv1 rv2 imm dPc)
    let isMemInst := RVUtil.isMemoryInst dInst

    -- memory-instruction sub-branch: build the byte-enabled request
    let shiftAmount := concat_bits offset 3 (0 : BitVec 3)
    let byteEn : BitVec 4 :=
      if size == (0b00 : BitVec 2) then shift_left (0b0001 : BitVec 4) offset
      else if size == (0b01 : BitVec 2) then shift_left (0b0011 : BitVec 4) offset
      else shift_left (0b1111 : BitVec 4) offset -- size = 0b10 (word); 0b11 unused by RV32I
    let dataMem := shift_left rv2 shiftAmount
    let addrMem := concat_bits (extract_bits addr0 31 2) 2 (0 : BitVec 2)
    let isUnsignedMem := extract_bit funct3 2
    let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_)
                     byteEn (0 : BitVec 4)
    let reqMem : t_mem := { byte_en := typeMem, addr := addrMem, data := dataMem }
    let mmioTarget := isMMIO addrMem

    -- non-memory (control/ALU) sub-branch: resolve the branch/jump target
    let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm dPc).nextPC
    let pcMismatch := bool_not (if nextPC == ppc then BTrue Unit_ else BFalse Unit_)

    let data := ite_bsv isMemInst dataMem dataCtrl
    let finalIsUnsigned := ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)
    let finalMmio := match _ : isMemInst with | BTrue _ => mmioTarget | BFalse _ => BFalse Unit_
    let memBusinessVal : t_membusiness :=
      { isUnsigned := bitvec1_to_bool finalIsUnsigned, size := size, offset := offset, mmio := finalMmio }
    let e2wVal : t_e2w := { memBusiness := memBusinessVal, data := data, dInst := dInst }

    let branchState : state :=
      match _ : isMemInst with
      | BTrue _ =>
        (match _ : mmioTarget with
          | BTrue _ => { s with toMMIO_hasElement := true, toMMIO_element := reqMem }
          | BFalse _ => { s with toDmem_hasElement := true, toDmem_element := reqMem })
      | BFalse _ =>
        { { s with eEp := s.eEp + ite_bsv pcMismatch (-1 : BitVec 1) (0 : BitVec 1) }
            with pc := ite_bsv pcMismatch nextPC s.pc }
    let normalState : state :=
      { { branchState with e2w_hasElement := true, e2w_element := e2wVal }
          with d2e_hasElement := false }

    let fireGuard :=
      bool_and (fifo_RDY_deq s.d2e_hasElement)
        (bool_and (fifo_RDY_deq s.d2e_hasElement)
          (match _ : ieEpMismatch with
            | BTrue _ => BTrue Unit_
            | BFalse _ =>
              bool_and (fifo_RDY_enq s.e2w_hasElement)
                (match _ : isMemInst with
                  | BTrue _ =>
                    (match _ : mmioTarget with
                      | BTrue _ => fifo_RDY_enq s.toMMIO_hasElement
                      | BFalse _ => fifo_RDY_enq s.toDmem_hasElement)
                  | BFalse _ => BTrue Unit_)))
    (fireGuard, match _ : ieEpMismatch with
      | BTrue _ => squashState
      | BFalse _ => normalState)

-- rule writeback: for memory instructions, collect the (Dmem or MMIO) response,
-- extract/extend the requested sub-word, then release the scoreboard and
-- commit the result to rf (skipping x0 / instructions with no destination).
def rule_RL_writeback : state → (t_bool × state) :=
  fun (s : state) =>
    let e2wEntry := s.e2w_element
    let memBusiness := e2wEntry.memBusiness
    let e2wData := e2wEntry.data
    let dInst := e2wEntry.dInst
    let isMemInst := RVUtil.isMemoryInst dInst

    let respData :=
      match _ : memBusiness.mmio with
      | BTrue _ => s.fromMMIO_element.data
      | BFalse _ => s.fromDmem_element.data
    let respState : state :=
      match _ : memBusiness.mmio with
      | BTrue _ => { s with fromMMIO_hasElement := false }
      | BFalse _ => { s with fromDmem_hasElement := false }

    let memDataShifted := shift_right_logical respData (concat_bits memBusiness.offset 3 (0 : BitVec 3))
    let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
    let dataSel : BitVec 32 :=
      if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
      else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
      else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
      else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
      else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

    let baseState : state := match _ : isMemInst with | BTrue _ => respState | BFalse _ => s
    let dataFinal : BitVec 32 := match _ : isMemInst with | BTrue _ => dataSel | BFalse _ => e2wData

    let fields := RVUtil.getInstFields dInst.inst
    let rdIdx := fields.rd
    let isValidRd := bool_and dInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
    let finalState : state :=
      { { { baseState with
              sb := arr_set baseState.sb rdIdx.toNat
                      ((arr_get baseState.sb rdIdx.toNat) + ite_bsv isValidRd (-1 : BitVec 2) (0 : BitVec 2)) }
            with rf := arr_set baseState.rf rdIdx.toNat (ite_bsv isValidRd dataFinal (arr_get baseState.rf rdIdx.toNat)) }
          with e2w_hasElement := false }

    let fireGuard :=
      bool_and (fifo_RDY_deq s.e2w_hasElement)
        (bool_and (fifo_RDY_deq s.e2w_hasElement)
          (match _ : isMemInst with
            | BTrue _ =>
              bool_and
                (match _ : memBusiness.mmio with
                  | BTrue _ => fifo_RDY_deq s.fromMMIO_hasElement
                  | BFalse _ => fifo_RDY_deq s.fromDmem_hasElement)
                (match _ : memBusiness.mmio with
                  | BTrue _ => fifo_RDY_deq s.fromMMIO_hasElement
                  | BFalse _ => fifo_RDY_deq s.fromDmem_hasElement)
            | BFalse _ => BTrue Unit_))
    (fireGuard, finalState)

------------------------------------------------------------------------
-- top_pipelined.bsv rules, with the former rvCore.getX* RVIfc method calls
-- inlined directly against the flat FIFO fields above.
------------------------------------------------------------------------

-- rule requestI: fetch request, routed to port B. (The `debug`-guarded
-- $display in the source is simulation-only console I/O; elided.)
def rule_RL_requestI : state → (t_bool × state) :=
  fun (s : state) =>
    let req := s.toImem_element
    let addrB := (truncate (shift_right_logical req.addr (2 : Nat)) 20 : BitVec 20)
    let fireGuard :=
      bool_and (fifo_RDY_deq s.toImem_hasElement)
        (bool_and (fifo_RDY_deq s.toImem_hasElement)
          (M_mkSimpleBRAM2.meth_RDY_putB s.bram))
    (fireGuard,
      { { { s with toImem_hasElement := false }
            with ireq := req }
        with bram := putB_withResponse s.bram req.byte_en addrB req.data })

-- rule responseI: latch port B's response into the core's instruction response.
def rule_RL_responseI : state → (t_bool × state) :=
  fun (s : state) =>
    let x := (M_mkSimpleBRAM2.meth_readB s.bram).avValue_
    let req := { s.ireq with data := x }
    let fireGuard :=
      bool_and (M_mkSimpleBRAM2.meth_RDY_readB s.bram) (fifo_RDY_enq s.fromImem_hasElement)
    (fireGuard,
      { { s with bram := (M_mkSimpleBRAM2.meth_readB s.bram).avAction_ }
          with fromImem_hasElement := true, fromImem_element := req })

-- rule requestD: data-memory request, routed to port A; also recorded in
-- `dreq` so responseD can recover the original request shape.
def rule_RL_requestD : state → (t_bool × state) :=
  fun (s : state) =>
    let req := s.toDmem_element
    let addrA := (truncate (shift_right_logical req.addr (2 : Nat)) 20 : BitVec 20)
    let fireGuard :=
      bool_and (fifo_RDY_deq s.toDmem_hasElement)
        (bool_and (fifo_RDY_deq s.toDmem_hasElement)
          (bool_and (fifo_RDY_enq s.dreq_hasElement) (M_mkSimpleBRAM2.meth_RDY_putA s.bram)))
    (fireGuard,
      { { { s with toDmem_hasElement := false }
            with dreq_hasElement := true, dreq_element := req }
        with bram := putA_withResponse s.bram req.byte_en addrA req.data })

-- rule responseD: latch port A's response into the core's data response.
def rule_RL_responseD : state → (t_bool × state) :=
  fun (s : state) =>
    let x := (M_mkSimpleBRAM2.meth_readA s.bram).avValue_
    let req := { s.dreq_element with data := x }
    let fireGuard :=
      bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram)
        (bool_and (fifo_RDY_deq s.dreq_hasElement)
          (bool_and (fifo_RDY_deq s.dreq_hasElement) (fifo_RDY_enq s.fromDmem_hasElement)))
    (fireGuard,
      { { { s with bram := (M_mkSimpleBRAM2.meth_readA s.bram).avAction_ }
            with dreq_hasElement := false }
        with fromDmem_hasElement := true, fromDmem_element := req })

------------------------------------------------------------------------
-- Top interface methods, inlined against the flat toMMIO/fromMMIO fields.
------------------------------------------------------------------------

-- method Action getMMIOReq(): forwarded straight through to the core's toMMIO queue.
def meth_getMMIOReq (s : state) : t_actionvalue_ t_mem state :=
  { avValue_ := s.toMMIO_element, avAction_ := { s with toMMIO_hasElement := false } }
def meth_RDY_getMMIOReq (s : state) : t_bool := fifo_RDY_deq s.toMMIO_hasElement

-- method Action getMMIOResp(Mem a): recover the pending request shape from
-- `mmioreq`, splice in the caller-supplied response data, and enqueue it into
-- the core's fromMMIO queue. (As noted above, nothing in this source
-- enqueues into `mmioreq` anymore, so this method's guard is in fact never
-- satisfiable.)
def meth_getMMIOResp (s : state) (a : t_mem) : t_actionvalue_ unit_ state :=
  let req := { s.mmioreq_element with data := a.data }
  { avValue_ := Unit_,
    avAction_ :=
      { { s with mmioreq_hasElement := false }
          with fromMMIO_hasElement := true, fromMMIO_element := req } }
def meth_RDY_getMMIOResp (s : state) : t_bool :=
  bool_and (fifo_RDY_deq s.mmioreq_hasElement)
    (bool_and (fifo_RDY_deq s.mmioreq_hasElement) (fifo_RDY_enq s.fromMMIO_hasElement))

end M_mktop_pipelined
