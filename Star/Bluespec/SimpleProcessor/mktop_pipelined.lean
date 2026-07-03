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
-- Every `Queue`-module FIFO (toImem/fromImem/toDmem/fromDmem/f2d/d2e/e2w/
-- dreq/commitQ) is likewise flattened: instead of a nested
-- `M_mkBypassFIFO.state _` field reached through meth_enq/meth_deq/
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
-- DEVIATION FROM top_pipelined.bsv: the source's MMIO request/response
-- interface (getMMIOReqA/getMMIOReqV/getMMIOResp, and the toMMIO/fromMMIO
-- routing in rule_RL_execute/rule_RL_writeback) has been replaced by a
-- retirement/"commit" interface. This is a deliberate modeling change (not
-- something top_pipelined.bsv itself does), taken because the free-running
-- fetch/decode/execute/writeback loop has no bounded termination argument
-- between external calls when the only external interface is MMIO: a
-- program that never touches MMIO (e.g. this formalization's default,
-- all-zero instruction memory, which decodes as a harmless repeated load)
-- runs forever without ever needing an external interaction, which breaks
-- the flush-point-based refinement technique (it requires the impl's
-- internal-rule-only relation to be well-founded). Requiring instead that
-- *every* retiring instruction be drained externally via getCommit bounds
-- how far the pipeline can run ahead of the last acknowledged commit (to
-- the depth of the single-slot FIFOs between fetch and commitQ), which
-- restores termination of the rule-only relation.
--
-- Mechanically: rule_RL_writeback is unchanged in spirit (still an
-- internal rule, still unconditionally commits to rf/sb as soon as data is
-- available) except it (a) no longer distinguishes MMIO vs. regular memory
-- responses (all loads/stores go through toDmem/fromDmem/bram uniformly),
-- and (b) additionally requires room in the new single-slot `commitQ` FIFO,
-- into which it pushes a t_commit record describing what retired. The new
-- external method getCommit drains commitQ. Since commitQ is the only way
-- e2w gets drained, and this cascades backward (execute blocks on e2w,
-- decode blocks on d2e, fetch/requestI/responseI eventually block on f2d/
-- fromImem/bram's port-B latch), the whole system reaches a rule-only dead
-- end within a bounded number of steps whenever getCommit isn't called,
-- instead of running forever.
--
-- SHAPE OF EACH RULE BELOW: every rule is split into a `_core` function and
-- a thin wrapper. `rule_RL_X_core` takes *only* the specific state fields
-- rule_RL_X reads (as plain arguments, including "pass-through" fields it
-- may leave untouched down some branch) and returns the guard plus the
-- specific fields it writes; `rule_RL_X` just plugs `_core`'s inputs/outputs
-- into/out of the full `State` record via `{ s with ... }`. This is
-- semantically identical to writing the whole thing directly against `s`
-- (as earlier revisions of this file did), but it makes the commuting
-- proofs in mktop_pipelined_spec.lean tractable: congruence over `_core`
-- ("same arguments in, same result out") is immediate function-argument
-- substitution, whereas congruence stated directly over `s`'s field
-- projections requires unfolding rule_RL_X's internal case-splits (on
-- decoded-instruction properties etc.) once per untouched field, which
-- blows up combinatorially for the larger rules.

import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
open BluespecPrelude
open Params_types

namespace M_mktop_pipelined

structure State where
  -- pipelined.bsv (RVIfc core), flattened, FIFOs flattened to hasElement/element pairs
  toImem_hasElement : Bool := false
  toImem_element : t_mem := default
  fromImem_hasElement : Bool := false
  fromImem_element : t_mem := default
  toDmem_hasElement : Bool := false
  toDmem_element : t_mem := default
  fromDmem_hasElement : Bool := false
  fromDmem_element : t_mem := default
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
  -- commit/retirement queue (replaces the old mmioreq field; see file header)
  commitQ_hasElement : Bool := false
  commitQ_element : t_commit := default
deriving Inhabited

-- Single-slot FIFO ready signals (Star.Bluespec.Lib.mkBypassFIFO's
-- meth_RDY_enq/meth_RDY_deq/meth_RDY_first, inlined: RDY_first uses the same
-- condition as RDY_deq).
def fifo_RDY_enq (hasElement : Bool) : t_bool := if hasElement then BFalse Unit_ else BTrue Unit_
def fifo_RDY_deq (hasElement : Bool) : t_bool := if hasElement then BTrue Unit_ else BFalse Unit_

-- portA/B.request.put(BRAMRequestBE{writeen, responseOnWrite: True, address, datain})
-- with mkSimpleBRAM2 as the underlying model: `byte_en = 0` reads (latching a
-- response as usual); any nonzero `byte_en` is treated as a full-word write of
-- `datain`, and (since responseOnWrite is always True at both call sites in
-- top_pipelined.bsv) the written value is also latched as the response.
def putA_withResponse (bram : M_mkSimpleBRAM2.state (BitVec 32)) (byte_en : BitVec 4)
    (address : BitVec 30) (datain : BitVec 32) : M_mkSimpleBRAM2.state (BitVec 32) :=
  let isWrite := if byte_en == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
  let afterWrite := (M_mkSimpleBRAM2.meth_putA bram isWrite address datain).avAction_
  match _ : isWrite with
  | BTrue _ => { afterWrite with readResultA := some datain }
  | BFalse _ => afterWrite

def putB_withResponse (bram : M_mkSimpleBRAM2.state (BitVec 32)) (byte_en : BitVec 4)
    (address : BitVec 30) (datain : BitVec 32) : M_mkSimpleBRAM2.state (BitVec 32) :=
  let isWrite := if byte_en == (0 : BitVec 4) then BFalse Unit_ else BTrue Unit_
  let afterWrite := (M_mkSimpleBRAM2.meth_putB bram isWrite address datain).avAction_
  match _ : isWrite with
  | BTrue _ => { afterWrite with readResultB := some datain }
  | BFalse _ => afterWrite

------------------------------------------------------------------------
-- pipelined.bsv rules (mkpipelined), inlined over the flat `state`
------------------------------------------------------------------------

-- rule fetch: always fires (subject to f2d/toImem being ready); no guard in source.
def rule_RL_fetch_core (pc : BitVec 32) (dEp eEp : BitVec 1) (f2dHasElement toImemHasElement : Bool) :
    t_bool × t_f2d × BitVec 32 × t_mem :=
  let ppc := pc + (4 : BitVec 32)
  let f2dEntry : t_f2d := { pc := pc, ppc := ppc, idEp := dEp, ieEp := eEp }
  let req : t_mem := { byte_en := 0, addr := pc, data := 0 }
  (bool_and (fifo_RDY_enq f2dHasElement) (fifo_RDY_enq toImemHasElement), f2dEntry, ppc, req)

def rule_RL_fetch (s : State) : t_bool × State :=
  let (g, f2dEntry, pc, req) := rule_RL_fetch_core s.pc s.dEp s.eEp s.f2d_hasElement s.toImem_hasElement
  (g, { s with f2d_hasElement := true, f2d_element := f2dEntry, pc := pc, toImem_hasElement := true, toImem_element := req })

-- rule decode: either squash (f2d/fromImem epoch stale w.r.t. dEp/eEp) or, once
-- operands clear the scoreboard, decode + issue into d2e and bump the scoreboard.
def rule_RL_decode_core (fromImemElement : t_mem) (f2dElement : t_f2d) (dEp eEp : BitVec 1)
    (sb : Array (BitVec 2)) (rf : Array (BitVec 32)) (pc : BitVec 32) (d2eElement : t_d2e)
    (fromImemHasElement f2dHasElement d2eHasElement : Bool) :
    t_bool × BitVec 32 × BitVec 1 × Bool × t_d2e × Array (BitVec 2) :=
  let instr := fromImemElement.data
  let fromFetch := f2dElement
  let decodedInst := RVUtil.decodeInst instr
  let fields := RVUtil.getInstFields instr
  let rdIdx := fields.rd
  let rs1Idx := fields.rs1
  let rs2Idx := fields.rs2
  let epochMismatch :=
    bool_or (bool_not (if fromFetch.idEp == dEp then BTrue Unit_ else BFalse Unit_))
            (bool_not (if fromFetch.ieEp == eEp then BTrue Unit_ else BFalse Unit_))
  let rs1Ready :=
    bool_or (bool_and decodedInst.valid_rs1
               (if arr_get sb rs1Idx.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
            (bool_not decodedInst.valid_rs1)
  let rs2Ready :=
    bool_or (bool_and decodedInst.valid_rs2
               (if arr_get sb rs2Idx.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
            (bool_not decodedInst.valid_rs2)
  let operandsReady := bool_and rs1Ready rs2Ready

  -- decode branch: read rf (x0 hardwired to 0), resolve redirects, issue to d2e
  let rs1 := ite_bsv (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
               (0 : BitVec 32) (arr_get rf rs1Idx.toNat)
  let rs2 := ite_bsv (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
               (0 : BitVec 32) (arr_get rf rs2Idx.toNat)
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
  let sbNormal := arr_set sb rdIdx.toNat ((arr_get sb rdIdx.toNat) + ite_bsv rdCond (1 : BitVec 2) (0 : BitVec 2))

  -- squash branch: everything below stays exactly as it was (pass-through)
  let newPc := match _ : epochMismatch with | BTrue _ => pc | BFalse _ => ite_bsv redirected ppcNew pc
  let newDEp := match _ : epochMismatch with
    | BTrue _ => dEp | BFalse _ => dEp + ite_bsv redirected (1 : BitVec 1) (0 : BitVec 1)
  let newD2eHasElement := match _ : epochMismatch with | BTrue _ => d2eHasElement | BFalse _ => true
  let newD2eElement := match _ : epochMismatch with | BTrue _ => d2eElement | BFalse _ => d2eEntry
  let newSb := match _ : epochMismatch with | BTrue _ => sb | BFalse _ => sbNormal

  let fireGuard :=
    bool_and (fifo_RDY_deq fromImemHasElement)
      (bool_and (fifo_RDY_deq f2dHasElement)
        (bool_and (bool_or epochMismatch operandsReady)
          (bool_and (fifo_RDY_deq f2dHasElement)
            (bool_and (fifo_RDY_deq fromImemHasElement)
              (match _ : epochMismatch with
                | BTrue _ => BTrue Unit_
                | BFalse _ => fifo_RDY_enq d2eHasElement)))))
  (fireGuard, newPc, newDEp, newD2eHasElement, newD2eElement, newSb)

def rule_RL_decode (s : State) : t_bool × State :=
  let (g, pc, dEp, d2eH, d2eE, sb) :=
    rule_RL_decode_core s.fromImem_element s.f2d_element s.dEp s.eEp s.sb s.rf s.pc s.d2e_element
      s.fromImem_hasElement s.f2d_hasElement s.d2e_hasElement
  (g, { s with f2d_hasElement := false, fromImem_hasElement := false, pc := pc, dEp := dEp, d2e_hasElement := d2eH, d2e_element := d2eE, sb := sb })

-- rule execute: on a stale (squashed) instruction, just undo its scoreboard
-- reservation; otherwise run the ALU/branch-resolution/address-generation logic
-- and issue a memory request, or update pc/eEp for a taken branch.
def rule_RL_execute_core (d2eElement : t_d2e) (eEp : BitVec 1) (sb : Array (BitVec 2))
    (pc : BitVec 32) (toDmemElement : t_mem) (e2wElement : t_e2w)
    (d2eHasElement e2wHasElement toDmemHasElement : Bool) :
    t_bool × Array (BitVec 2) × Bool × t_mem × BitVec 1 × BitVec 32 × Bool × t_e2w :=
  let dInst := d2eElement.dInst
  let dPc := d2eElement.pc
  let ppc := d2eElement.ppc
  let ieEp := d2eElement.ieEp
  let rv1 := d2eElement.rv1
  let rv2 := d2eElement.rv2
  let ieEpMismatch := bool_not (if ieEp == eEp then BTrue Unit_ else BFalse Unit_)

  -- squash branch: instruction was speculatively issued after a redirect
  -- that has since happened; just release its scoreboard reservation.
  let squashRdIdx := (RVUtil.getInstFields dInst.inst).rd
  let squashCond := bool_and dInst.valid_rd (bool_not (if squashRdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
  let squashSb := arr_set sb squashRdIdx.toNat
    ((arr_get sb squashRdIdx.toNat) + ite_bsv squashCond (-1 : BitVec 2) (0 : BitVec 2))

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

  -- non-memory (control/ALU) sub-branch: resolve the branch/jump target
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm dPc).nextPC
  let pcMismatch := bool_not (if nextPC == ppc then BTrue Unit_ else BFalse Unit_)

  let data := ite_bsv isMemInst dataMem dataCtrl
  let finalIsUnsigned := ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool finalIsUnsigned, size := size, offset := offset }
  let e2wVal : t_e2w := { memBusiness := memBusinessVal, data := data, dInst := dInst, pc := dPc }

  -- normal branch, pass-through when squashing
  let toDmemHasElementNormal := match _ : isMemInst with | BTrue _ => true | BFalse _ => toDmemHasElement
  let toDmemElementNormal := match _ : isMemInst with | BTrue _ => reqMem | BFalse _ => toDmemElement
  let eEpNormal := match _ : isMemInst with
    | BTrue _ => eEp | BFalse _ => eEp + ite_bsv pcMismatch (-1 : BitVec 1) (0 : BitVec 1)
  let pcNormal := match _ : isMemInst with | BTrue _ => pc | BFalse _ => ite_bsv pcMismatch nextPC pc

  let newSb := match _ : ieEpMismatch with | BTrue _ => squashSb | BFalse _ => sb
  let newToDmemHasElement := match _ : ieEpMismatch with | BTrue _ => toDmemHasElement | BFalse _ => toDmemHasElementNormal
  let newToDmemElement := match _ : ieEpMismatch with | BTrue _ => toDmemElement | BFalse _ => toDmemElementNormal
  let newEEp := match _ : ieEpMismatch with | BTrue _ => eEp | BFalse _ => eEpNormal
  let newPc := match _ : ieEpMismatch with | BTrue _ => pc | BFalse _ => pcNormal
  let newE2wHasElement := match _ : ieEpMismatch with | BTrue _ => e2wHasElement | BFalse _ => true
  let newE2wElement := match _ : ieEpMismatch with | BTrue _ => e2wElement | BFalse _ => e2wVal

  let fireGuard :=
    bool_and (fifo_RDY_deq d2eHasElement)
      (bool_and (fifo_RDY_deq d2eHasElement)
        (match _ : ieEpMismatch with
          | BTrue _ => BTrue Unit_
          | BFalse _ =>
            bool_and (fifo_RDY_enq e2wHasElement)
              (match _ : isMemInst with
                | BTrue _ => fifo_RDY_enq toDmemHasElement
                | BFalse _ => BTrue Unit_)))
  (fireGuard, newSb, newToDmemHasElement, newToDmemElement, newEEp, newPc, newE2wHasElement, newE2wElement)

def rule_RL_execute (s : State) : t_bool × State :=
  let (g, sb, toDmemH, toDmemE, eEp, pc, e2wH, e2wE) :=
    rule_RL_execute_core s.d2e_element s.eEp s.sb s.pc s.toDmem_element s.e2w_element
      s.d2e_hasElement s.e2w_hasElement s.toDmem_hasElement
  (g, { s with sb := sb, d2e_hasElement := false, toDmem_hasElement := toDmemH, toDmem_element := toDmemE, eEp := eEp, pc := pc, e2w_hasElement := e2wH, e2w_element := e2wE })

-- rule writeback: for memory instructions, collect the Dmem response, extract/
-- extend the requested sub-word, then release the scoreboard, commit the
-- result to rf (skipping x0 / instructions with no destination), and push a
-- retirement record into commitQ for the external getCommit method to drain.
def rule_RL_writeback_core (e2wElement : t_e2w) (fromDmemElement : t_mem)
    (sb : Array (BitVec 2)) (rf : Array (BitVec 32))
    (e2wHasElement fromDmemHasElement commitQHasElement : Bool) :
    t_bool × Bool × Array (BitVec 2) × Array (BitVec 32) × Bool × Bool × t_commit :=
  let e2wData := e2wElement.data
  let dInst := e2wElement.dInst
  let isMemInst := RVUtil.isMemoryInst dInst

  let respData := fromDmemElement.data
  let memBusiness := e2wElement.memBusiness
  let memDataShifted := shift_right_logical respData (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  let dataSel : BitVec 32 :=
    if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
    else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
    else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
    else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
    else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

  let newFromDmemHasElement := match _ : isMemInst with | BTrue _ => false | BFalse _ => fromDmemHasElement
  let dataFinal : BitVec 32 := match _ : isMemInst with | BTrue _ => dataSel | BFalse _ => e2wData

  let fields := RVUtil.getInstFields dInst.inst
  let rdIdx := fields.rd
  let isValidRd := bool_and dInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
  let commitEntry : t_commit :=
    { inst := dInst.inst, pc := e2wElement.pc, rdIdx := rdIdx, validRd := isValidRd, data := dataFinal }
  let newSb := arr_set sb rdIdx.toNat
    ((arr_get sb rdIdx.toNat) + ite_bsv isValidRd (-1 : BitVec 2) (0 : BitVec 2))
  let newRf := arr_set rf rdIdx.toNat (ite_bsv isValidRd dataFinal (arr_get rf rdIdx.toNat))

  let fireGuard :=
    bool_and (fifo_RDY_deq e2wHasElement)
      (bool_and (fifo_RDY_deq e2wHasElement)
        (bool_and (fifo_RDY_enq commitQHasElement)
          (match _ : isMemInst with
            | BTrue _ => bool_and (fifo_RDY_deq fromDmemHasElement) (fifo_RDY_deq fromDmemHasElement)
            | BFalse _ => BTrue Unit_)))
  (fireGuard, newFromDmemHasElement, newSb, newRf, false, true, commitEntry)

def rule_RL_writeback (s : State) : t_bool × State :=
  let (g, fromDmemH, sb, rf, e2wH, commitQH, commitQE) :=
    rule_RL_writeback_core s.e2w_element s.fromDmem_element s.sb s.rf
      s.e2w_hasElement s.fromDmem_hasElement s.commitQ_hasElement
  (g, { s with fromDmem_hasElement := fromDmemH, sb := sb, rf := rf, e2w_hasElement := e2wH, commitQ_hasElement := commitQH, commitQ_element := commitQE })

------------------------------------------------------------------------
-- top_pipelined.bsv rules, with the former rvCore.getX* RVIfc method calls
-- inlined directly against the flat FIFO fields above.
------------------------------------------------------------------------

-- rule requestI: fetch request, routed to port B. (The `debug`-guarded
-- $display in the source is simulation-only console I/O; elided.)
def rule_RL_requestI_core (toImemElement : t_mem) (toImemHasElement : Bool)
    (bram : M_mkSimpleBRAM2.state (BitVec 32)) : t_bool × t_mem × M_mkSimpleBRAM2.state (BitVec 32) :=
  let addrB := (truncate (shift_right_logical toImemElement.addr (2 : Nat)) 30 : BitVec 30)
  let fireGuard :=
    bool_and (fifo_RDY_deq toImemHasElement)
      (bool_and (fifo_RDY_deq toImemHasElement) (M_mkSimpleBRAM2.meth_RDY_putB bram))
  (fireGuard, toImemElement, putB_withResponse bram toImemElement.byte_en addrB toImemElement.data)

def rule_RL_requestI (s : State) : t_bool × State :=
  let (g, ireq, bram) := rule_RL_requestI_core s.toImem_element s.toImem_hasElement s.bram
  (g, { s with toImem_hasElement := false, ireq := ireq, bram := bram })

-- rule responseI: latch port B's response into the core's instruction response.
def rule_RL_responseI_core (bram : M_mkSimpleBRAM2.state (BitVec 32)) (ireq : t_mem)
    (fromImemHasElement : Bool) : t_bool × M_mkSimpleBRAM2.state (BitVec 32) × t_mem :=
  let x := (M_mkSimpleBRAM2.meth_readB bram).avValue_
  let req := { ireq with data := x }
  let fireGuard := bool_and (M_mkSimpleBRAM2.meth_RDY_readB bram) (fifo_RDY_enq fromImemHasElement)
  (fireGuard, (M_mkSimpleBRAM2.meth_readB bram).avAction_, req)

def rule_RL_responseI (s : State) : t_bool × State :=
  let (g, bram, req) := rule_RL_responseI_core s.bram s.ireq s.fromImem_hasElement
  (g, { s with bram := bram, fromImem_hasElement := true, fromImem_element := req })

-- rule requestD: data-memory request, routed to port A; also recorded in
-- `dreq` so responseD can recover the original request shape.
def rule_RL_requestD_core (toDmemElement : t_mem) (toDmemHasElement dreqHasElement : Bool)
    (bram : M_mkSimpleBRAM2.state (BitVec 32)) : t_bool × t_mem × M_mkSimpleBRAM2.state (BitVec 32) :=
  let addrA := (truncate (shift_right_logical toDmemElement.addr (2 : Nat)) 30 : BitVec 30)
  let fireGuard :=
    bool_and (fifo_RDY_deq toDmemHasElement)
      (bool_and (fifo_RDY_deq toDmemHasElement)
        (bool_and (fifo_RDY_enq dreqHasElement) (M_mkSimpleBRAM2.meth_RDY_putA bram)))
  (fireGuard, toDmemElement, putA_withResponse bram toDmemElement.byte_en addrA toDmemElement.data)

def rule_RL_requestD (s : State) : t_bool × State :=
  let (g, dreq, bram) := rule_RL_requestD_core s.toDmem_element s.toDmem_hasElement s.dreq_hasElement s.bram
  (g, { s with toDmem_hasElement := false, dreq_hasElement := true, dreq_element := dreq, bram := bram })

-- rule responseD: latch port A's response into the core's data response.
def rule_RL_responseD_core (bram : M_mkSimpleBRAM2.state (BitVec 32)) (dreqHasElement : Bool)
    (dreqElement : t_mem) (fromDmemHasElement : Bool) :
    t_bool × M_mkSimpleBRAM2.state (BitVec 32) × t_mem :=
  let x := (M_mkSimpleBRAM2.meth_readA bram).avValue_
  let req := { dreqElement with data := x }
  let fireGuard :=
    bool_and (M_mkSimpleBRAM2.meth_RDY_readA bram)
      (bool_and (fifo_RDY_deq dreqHasElement)
        (bool_and (fifo_RDY_deq dreqHasElement) (fifo_RDY_enq fromDmemHasElement)))
  (fireGuard, (M_mkSimpleBRAM2.meth_readA bram).avAction_, req)

def rule_RL_responseD (s : State) : t_bool × State :=
  let (g, bram, req) := rule_RL_responseD_core s.bram s.dreq_hasElement s.dreq_element s.fromDmem_hasElement
  (g, { s with bram := bram, dreq_hasElement := false, fromDmem_hasElement := true, fromDmem_element := req })

------------------------------------------------------------------------
-- External interface: retirement/commit (replaces the old Top MMIO methods)
------------------------------------------------------------------------

-- method t_commit getCommit(): drain the next retired instruction's commit
-- record. This is the only external interaction the redesigned module
-- exposes; see the file header for why it's needed for termination.
def meth_getCommit (s : State) : t_actionvalue_ t_commit State :=
  { avValue_ := s.commitQ_element, avAction_ := { s with commitQ_hasElement := false } }
def meth_RDY_getCommit (s : State) : t_bool := fifo_RDY_deq s.commitQ_hasElement

end M_mktop_pipelined
