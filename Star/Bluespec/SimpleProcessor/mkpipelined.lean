-- mkpipelined.lean - Lean formalization of Star/Bluespec/simple-processor/pipelined.bsv
-- (module mkpipelined, interface RVIfc). A 4-stage (fetch/decode/execute/writeback)
-- in-order RISC-V pipeline with a 2-bit-saturating scoreboard for RAW hazards and
-- a 1-bit epoch per redirect-causing stage (dEp/eEp) for squashing stale instructions
-- after a branch/jump misprediction.
--
-- All inter-stage FIFOs (toImem/fromImem/toDmem/fromDmem/toMMIO/fromMMIO/f2d/d2e/e2w)
-- are instances of the `Queue` module, modeled here by reusing
-- Star.Bluespec.Lib.mkBypassFIFO's single-slot FIFO spec. The register
-- file `rf` and scoreboard `sb` are Vector#(32, Reg#(_)) in the source, modeled here
-- as fixed-size 32-element Arrays (see Star.Bluespec.Lib.BluespecPrelude's
-- arr_get/arr_set). Instruction-set semantics (decodeInst, execALU32, execControl32,
-- etc.) live in the external RVUtil package and are treated as an uninterpreted
-- black box in Star.Bluespec.Lib.RVUtil, per the same "hand-written opaque spec"
-- convention used for submodules like mkSimpleBRAM2.

import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.mkBypassFIFO
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
open BluespecPrelude
open Params_types

namespace M_mkpipelined

structure state where
  toImem : M_mkBypassFIFO.state t_mem
  fromImem : M_mkBypassFIFO.state t_mem
  toDmem : M_mkBypassFIFO.state t_mem
  fromDmem : M_mkBypassFIFO.state t_mem
  toMMIO : M_mkBypassFIFO.state t_mem
  fromMMIO : M_mkBypassFIFO.state t_mem
  f2d : M_mkBypassFIFO.state t_f2d
  d2e : M_mkBypassFIFO.state t_d2e
  e2w : M_mkBypassFIFO.state t_e2w
  pc : BitVec 32
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  sb : Array (BitVec 2) := .mk (List.replicate 32 default)
  dEp : BitVec 1
  eEp : BitVec 1
deriving Inhabited

-- function Bool isMMIO(Bit#(32) addr) from pipelined.bsv: word-aligned addresses
-- of the three MMIO registers (STDERR char/int write, sim exit).
def isMMIO (addr : BitVec 32) : t_bool :=
  if addr == (0xf000fff0 : BitVec 32) || addr == (0xf000fff4 : BitVec 32)
      || addr == (0xf000fff8 : BitVec 32)
  then BTrue Unit_ else BFalse Unit_

-- rule fetch: always fires (subject to f2d/toImem being ready); no guard in source.
def rule_RL_fetch : state → (t_bool × state) :=
  fun (s : state) =>
    let ppc := s.pc + (4 : BitVec 32)
    let f2dEntry : t_f2d := { pc := s.pc, ppc := ppc, idEp := s.dEp, ieEp := s.eEp }
    let req : t_mem := { byte_en := 0, addr := s.pc, data := 0 }
    (bool_and (M_mkBypassFIFO.meth_RDY_enq s.f2d) (M_mkBypassFIFO.meth_RDY_enq s.toImem),
      { { { s with f2d := (M_mkBypassFIFO.meth_enq s.f2d f2dEntry).avAction_ }
            with pc := ppc }
        with toImem := (M_mkBypassFIFO.meth_enq s.toImem req).avAction_ })

-- rule decode: either squash (f2d/fromImem epoch stale w.r.t. dEp/eEp) or, once
-- operands clear the scoreboard, decode + issue into d2e and bump the scoreboard.
def rule_RL_decode : state → (t_bool × state) :=
  fun (s : state) =>
    let instr := (M_mkBypassFIFO.meth_first s.fromImem).data
    let fromFetch := M_mkBypassFIFO.meth_first s.f2d
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
      { { s with f2d := (M_mkBypassFIFO.meth_deq s.f2d).avAction_ }
          with fromImem := (M_mkBypassFIFO.meth_deq s.fromImem).avAction_ }

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
              with d2e := (M_mkBypassFIFO.meth_enq s.d2e d2eEntry).avAction_ }
            with sb := arr_set s.sb rdIdx.toNat
                         ((arr_get s.sb rdIdx.toNat) + ite_bsv rdCond (1 : BitVec 2) (0 : BitVec 2)) }
        with f2d := (M_mkBypassFIFO.meth_deq s.f2d).avAction_ }
    let decodeState' : state := { decodeState with fromImem := (M_mkBypassFIFO.meth_deq s.fromImem).avAction_ }

    let fireGuard :=
      bool_and (M_mkBypassFIFO.meth_RDY_first s.fromImem)
        (bool_and (M_mkBypassFIFO.meth_RDY_first s.f2d)
          (bool_and (bool_or epochMismatch operandsReady)
            (bool_and (M_mkBypassFIFO.meth_RDY_deq s.f2d)
              (bool_and (M_mkBypassFIFO.meth_RDY_deq s.fromImem)
                (match _ : epochMismatch with
                  | BTrue _ => BTrue Unit_
                  | BFalse _ => M_mkBypassFIFO.meth_RDY_enq s.d2e)))))
    (fireGuard, match _ : epochMismatch with
      | BTrue _ => squashState
      | BFalse _ => decodeState')

-- rule execute: on a stale (squashed) instruction, just undo its scoreboard
-- reservation; otherwise run the ALU/branch-resolution/address-generation logic
-- and issue a memory (or MMIO) request, or update pc/eEp for a taken branch.
def rule_RL_execute : state → (t_bool × state) :=
  fun (s : state) =>
    let d2eEntry := M_mkBypassFIFO.meth_first s.d2e
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
          with d2e := (M_mkBypassFIFO.meth_deq s.d2e).avAction_ }

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
          | BTrue _ => { s with toMMIO := (M_mkBypassFIFO.meth_enq s.toMMIO reqMem).avAction_ }
          | BFalse _ => { s with toDmem := (M_mkBypassFIFO.meth_enq s.toDmem reqMem).avAction_ })
      | BFalse _ =>
        { { s with eEp := s.eEp + ite_bsv pcMismatch (-1 : BitVec 1) (0 : BitVec 1) }
            with pc := ite_bsv pcMismatch nextPC s.pc }
    let normalState : state :=
      { { branchState with e2w := (M_mkBypassFIFO.meth_enq branchState.e2w e2wVal).avAction_ }
          with d2e := (M_mkBypassFIFO.meth_deq s.d2e).avAction_ }

    let fireGuard :=
      bool_and (M_mkBypassFIFO.meth_RDY_first s.d2e)
        (bool_and (M_mkBypassFIFO.meth_RDY_deq s.d2e)
          (match _ : ieEpMismatch with
            | BTrue _ => BTrue Unit_
            | BFalse _ =>
              bool_and (M_mkBypassFIFO.meth_RDY_enq s.e2w)
                (match _ : isMemInst with
                  | BTrue _ =>
                    (match _ : mmioTarget with
                      | BTrue _ => M_mkBypassFIFO.meth_RDY_enq s.toMMIO
                      | BFalse _ => M_mkBypassFIFO.meth_RDY_enq s.toDmem)
                  | BFalse _ => BTrue Unit_)))
    (fireGuard, match _ : ieEpMismatch with
      | BTrue _ => squashState
      | BFalse _ => normalState)

-- rule writeback: for memory instructions, collect the (Dmem or MMIO) response,
-- extract/extend the requested sub-word, then release the scoreboard and
-- commit the result to rf (skipping x0 / instructions with no destination).
def rule_RL_writeback : state → (t_bool × state) :=
  fun (s : state) =>
    let e2wEntry := M_mkBypassFIFO.meth_first s.e2w
    let memBusiness := e2wEntry.memBusiness
    let e2wData := e2wEntry.data
    let dInst := e2wEntry.dInst
    let isMemInst := RVUtil.isMemoryInst dInst

    let respData :=
      match _ : memBusiness.mmio with
      | BTrue _ => (M_mkBypassFIFO.meth_first s.fromMMIO).data
      | BFalse _ => (M_mkBypassFIFO.meth_first s.fromDmem).data
    let respState : state :=
      match _ : memBusiness.mmio with
      | BTrue _ => { s with fromMMIO := (M_mkBypassFIFO.meth_deq s.fromMMIO).avAction_ }
      | BFalse _ => { s with fromDmem := (M_mkBypassFIFO.meth_deq s.fromDmem).avAction_ }

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
          with e2w := (M_mkBypassFIFO.meth_deq baseState.e2w).avAction_ }

    let fireGuard :=
      bool_and (M_mkBypassFIFO.meth_RDY_first s.e2w)
        (bool_and (M_mkBypassFIFO.meth_RDY_deq s.e2w)
          (match _ : isMemInst with
            | BTrue _ =>
              bool_and
                (match _ : memBusiness.mmio with
                  | BTrue _ => M_mkBypassFIFO.meth_RDY_first s.fromMMIO
                  | BFalse _ => M_mkBypassFIFO.meth_RDY_first s.fromDmem)
                (match _ : memBusiness.mmio with
                  | BTrue _ => M_mkBypassFIFO.meth_RDY_deq s.fromMMIO
                  | BFalse _ => M_mkBypassFIFO.meth_RDY_deq s.fromDmem)
            | BFalse _ => BTrue Unit_))
    (fireGuard, finalState)

-- RVIfc methods: instruction-memory request/response

def meth_getIReqA (s : state) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with toImem := (M_mkBypassFIFO.meth_deq s.toImem).avAction_ } }
def meth_RDY_getIReqA (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_deq s.toImem

def meth_getIReqV (s : state) : t_mem := M_mkBypassFIFO.meth_first s.toImem
def meth_RDY_getIReqV (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_first s.toImem

def meth_getIResp (s : state) (a : t_mem) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with fromImem := (M_mkBypassFIFO.meth_enq s.fromImem a).avAction_ } }
def meth_RDY_getIResp (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_enq s.fromImem

-- RVIfc methods: data-memory request/response

def meth_getDReqA (s : state) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with toDmem := (M_mkBypassFIFO.meth_deq s.toDmem).avAction_ } }
def meth_RDY_getDReqA (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_deq s.toDmem

def meth_getDReqV (s : state) : t_mem := M_mkBypassFIFO.meth_first s.toDmem
def meth_RDY_getDReqV (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_first s.toDmem

def meth_getDResp (s : state) (a : t_mem) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with fromDmem := (M_mkBypassFIFO.meth_enq s.fromDmem a).avAction_ } }
def meth_RDY_getDResp (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_enq s.fromDmem

-- RVIfc methods: MMIO request/response

def meth_getMMIOReqA (s : state) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with toMMIO := (M_mkBypassFIFO.meth_deq s.toMMIO).avAction_ } }
def meth_RDY_getMMIOReqA (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_deq s.toMMIO

def meth_getMMIOReqV (s : state) : t_mem := M_mkBypassFIFO.meth_first s.toMMIO
def meth_RDY_getMMIOReqV (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_first s.toMMIO

def meth_getMMIOResp (s : state) (a : t_mem) : t_actionvalue_ unit_ state :=
  { avValue_ := Unit_, avAction_ := { s with fromMMIO := (M_mkBypassFIFO.meth_enq s.fromMMIO a).avAction_ } }
def meth_RDY_getMMIOResp (s : state) : t_bool := M_mkBypassFIFO.meth_RDY_enq s.fromMMIO

end M_mkpipelined
