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
-- Every `Queue`-module FIFO (f2d/d2e/e2w/commitQ) is likewise flattened:
-- instead of a nested `M_mkBypassFIFO.state _` field reached through
-- meth_enq/meth_deq/meth_first/meth_RDY_*, each FIFO's own two fields
-- (`hasElement : Bool`, `element : α`, per Star.Bluespec.Lib.mkBypassFIFO)
-- are lifted directly into `state` under an instance-name prefix (e.g.
-- `f2d_hasElement`/`f2d_element`), and the enq/deq/first/RDY logic is
-- inlined against those two fields via the local `fifo_RDY_enq`/
-- `fifo_RDY_deq` helpers below (enq sets `hasElement := true, element :=
-- x`; deq only clears `hasElement`, leaving `element` stale as
-- mkBypassFIFO itself does; first just reads `element`).
-- `Star.Bluespec.Lib.mkBypassFIFO` is therefore no longer imported either.
--
-- `bram` (BRAM2PortBE) is NOT modeled as a single shared 2-port memory here
-- (DEVIATION from top_pipelined.bsv, whose portA/portB both address one
-- `BRAM2PortBE` instance): it is split into two separate plain arrays,
-- `imem` and `dmem` (Star.Bluespec.Lib.mkSimpleMem). This is a deliberate
-- model restriction, not a translation of the source: routing instruction
-- fetches and data accesses through the *same* underlying memory makes
-- self-modifying code representable, and reasoning about the two sides'
-- rules commuting then depends on a reachability invariant ("no in-flight
-- instruction fetch ever aliases a concurrent data write") that this
-- codebase does not yet thread through the model. Splitting the memory in
-- two removes that hazard by construction.
--
-- DEVIATION FROM top_pipelined.bsv, part 2: the source's BRAM2PortBE also
-- models one cycle of request/response latency per port, via the separate
-- rule_RL_requestI/rule_RL_responseI (port B) and rule_RL_requestD/
-- rule_RL_responseD (port A) rules staging each access through an
-- `ireq`/`dreq` register. mkSimpleMem has no such latch (a read is
-- available the same "cycle" it's issued -- see mkSimpleMem.lean), so
-- there is nothing left for those four rules to stage: rule_RL_decode now
-- reads `imem` directly (using the pc rule_RL_fetch already computed) in
-- the same step it decodes, and rule_RL_execute reads/writes `dmem`
-- directly (doing the load-data extraction itself) in the same step it
-- computes the ALU/control result. This is a strictly-fewer-rules
-- restriction of the source's timing, not an unsound abstraction: it just
-- assumes memory has no latency, which was already true of the underlying
-- array model once the port latch was removed.
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
-- available) except it additionally requires room in the new single-slot
-- `commitQ` FIFO, into which it pushes a t_commit record describing what
-- retired. The new external method getCommit drains commitQ. Since commitQ
-- is the only way e2w gets drained, and this cascades backward (execute
-- blocks on e2w, decode blocks on d2e, fetch blocks on f2d), the whole
-- system reaches a rule-only dead end within a bounded number of steps
-- whenever getCommit isn't called, instead of running forever.
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
import Star.Bluespec.Lib.mkSimpleMem
import Star.Bluespec.SimpleProcessor.RVUtil
import Star.Bluespec.SimpleProcessor.Params_types
open BluespecPrelude
open Params_types

namespace M_mktop_pipelined

structure State where
  -- pipelined.bsv (RVIfc core), flattened, FIFOs flattened to hasElement/element pairs
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
  -- top_pipelined.bsv itself. Instruction memory and data memory are
  -- separate, plain, latency-free arrays -- see the file header for why.
  imem : Array (BitVec 32) := M_mkSimpleMem.defaultMem
  dmem : Array (BitVec 32) := M_mkSimpleMem.defaultMem
  -- commit/retirement queue (replaces the old mmioreq field; see file header)
  commitQ_hasElement : Bool := false
  commitQ_element : t_commit := default
deriving Inhabited

-- Single-slot FIFO ready signals (Star.Bluespec.Lib.mkBypassFIFO's
-- meth_RDY_enq/meth_RDY_deq/meth_RDY_first, inlined: RDY_first uses the same
-- condition as RDY_deq).
def fifo_RDY_enq (hasElement : Bool) : t_bool := if hasElement then BFalse Unit_ else BTrue Unit_
def fifo_RDY_deq (hasElement : Bool) : t_bool := if hasElement then BTrue Unit_ else BFalse Unit_

-- Sub-word load extraction: shift the response word down to the addressed
-- byte/halfword lane and sign/zero-extend per `funct3`. (Was writeback's
-- job when there was a separate response rule; now execute does it inline,
-- since it has synchronous access to `dmem`.)
def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

------------------------------------------------------------------------
-- pipelined.bsv rules (mkpipelined), inlined over the flat `state`
------------------------------------------------------------------------

-- rule fetch: always fires (subject to f2d being ready); no guard in source.
def rule_RL_fetch_core (pc : BitVec 32) (dEp eEp : BitVec 1) (f2dHasElement : Bool) :
    t_bool × t_f2d × BitVec 32 :=
  let ppc := pc + (4 : BitVec 32)
  let f2dEntry : t_f2d := { pc := pc, ppc := ppc, idEp := dEp, ieEp := eEp }
  (fifo_RDY_enq f2dHasElement, f2dEntry, ppc)

def rule_RL_fetch (s : State) : t_bool × State :=
  let (g, f2dEntry, pc) := rule_RL_fetch_core s.pc s.dEp s.eEp s.f2d_hasElement
  (g, { s with f2d_hasElement := true, f2d_element := f2dEntry, pc := pc })

-- rule decode: reads `imem` directly at the pc rule_RL_fetch staged in f2d
-- (no more separate request/response rules -- see file header), then either
-- squashes (f2d epoch stale w.r.t. dEp/eEp) or, once operands clear the
-- scoreboard, decodes + issues into d2e and bumps the scoreboard. Illegal
-- instructions are NOT special-cased in the squash-vs-issue decision: an
-- epoch-matching illegal instruction still issues into `d2e` exactly like a
-- legal one, and simply flows through the rest of the pipeline without ever
-- changing architectural state (`dInst.legal` rides along inside
-- `d2e`/`e2w` for `rule_RL_execute` (dmem write) and `rule_RL_writeback`
-- (rf write) to gate on). This is what makes decode's squash-vs-issue
-- decision purely epoch-based, which is exactly what the epoch invariant
-- `PipeInv` (mktop_pipelined_spec.lean) needs to make the decode/execute
-- commuting proof go through. The scoreboard reservation itself IS gated on
-- legality (`rdCond` below), so an illegal instruction never reserves `sb`
-- in the first place -- matching `rule_RL_writeback_core`'s release (also
-- gated on `.legal`) and `rule_RL_execute_core`'s squash-path release
-- (`squashCond`, also gated on `.legal`), so the reservation/release pair
-- stays balanced regardless of legality.
def rule_RL_decode_core (imem : Array (BitVec 32)) (f2dElement : t_f2d) (dEp eEp : BitVec 1)
    (sb : Array (BitVec 2)) (rf : Array (BitVec 32)) (pc : BitVec 32) (d2eElement : t_d2e)
    (f2dHasElement d2eHasElement : Bool) :
    t_bool × BitVec 32 × BitVec 1 × Bool × t_d2e × Array (BitVec 2) :=
  let fromFetch := f2dElement
  let instrAddr : BitVec 30 := truncate (shift_right_logical fromFetch.pc (2 : Nat)) 30
  let instr := M_mkSimpleMem.read imem instrAddr
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

  -- decode branch: read rf (x0 hardwired to 0, and any architecturally
  -- unused operand -- valid_rs1/valid_rs2 false -- forced to 0 too, so a
  -- concurrent in-flight write to that same register index, which decode
  -- never actually reads, can't make the resulting d2e entry depend on
  -- timing/ordering), resolve redirects, issue to d2e
  let rs1 := ite_bsv (bool_and decodedInst.valid_rs1
               (bool_not (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))
               (arr_get rf rs1Idx.toNat) (0 : BitVec 32)
  let rs2 := ite_bsv (bool_and decodedInst.valid_rs2
               (bool_not (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))
               (arr_get rf rs2Idx.toNat) (0 : BitVec 32)
  let immVal := RVUtil.getImmediate decodedInst
  let ppcNew := ite_bsv (RVUtil.isJALR decodedInst)
                  (bit_and (rs1 + immVal) (bit_not (1 : BitVec 32)))
                  (fromFetch.pc + immVal)
  let isJump := bool_or (RVUtil.isJAL decodedInst) (RVUtil.isJALR decodedInst)
  -- gated on `decodedInst.legal`: an illegal instruction never redirects
  -- `pc`/`dEp`, even if its bit pattern happens to look like a taken
  -- jump -- see rule_RL_execute_core's matching `pcMismatch` gate.
  let redirected :=
    bool_and decodedInst.legal
      (bool_and isJump (bool_not (if fromFetch.ppc == ppcNew then BTrue Unit_ else BFalse Unit_)))
  let d2eEntry : t_d2e :=
    { dInst := decodedInst, pc := fromFetch.pc,
      ppc := ite_bsv redirected ppcNew fromFetch.ppc,
      ieEp := fromFetch.ieEp, rv1 := rs1, rv2 := rs2 }
  let rdCond := bool_and decodedInst.legal
    (bool_and decodedInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))
  let sbNormal := arr_set sb rdIdx.toNat ((arr_get sb rdIdx.toNat) + ite_bsv rdCond (1 : BitVec 2) (0 : BitVec 2))

  -- squash branch: everything below stays exactly as it was (pass-through)
  let newPc := match _ : epochMismatch with | BTrue _ => pc | BFalse _ => ite_bsv redirected ppcNew pc
  let newDEp := match _ : epochMismatch with
    | BTrue _ => dEp | BFalse _ => dEp + ite_bsv redirected (1 : BitVec 1) (0 : BitVec 1)
  let newD2eHasElement := match _ : epochMismatch with | BTrue _ => d2eHasElement | BFalse _ => true
  let newD2eElement := match _ : epochMismatch with | BTrue _ => d2eElement | BFalse _ => d2eEntry
  let newSb := match _ : epochMismatch with | BTrue _ => sb | BFalse _ => sbNormal

  let fireGuard :=
    bool_and (fifo_RDY_deq f2dHasElement)
      (bool_and (bool_or epochMismatch operandsReady)
        (bool_and (fifo_RDY_deq f2dHasElement)
          (match _ : epochMismatch with
            | BTrue _ => BTrue Unit_
            | BFalse _ => fifo_RDY_enq d2eHasElement)))
  (fireGuard, newPc, newDEp, newD2eHasElement, newD2eElement, newSb)

def rule_RL_decode (s : State) : t_bool × State :=
  let (g, pc, dEp, d2eH, d2eE, sb) :=
    rule_RL_decode_core s.imem s.f2d_element s.dEp s.eEp s.sb s.rf s.pc s.d2e_element
      s.f2d_hasElement s.d2e_hasElement
  (g, { s with f2d_hasElement := false, pc := pc, dEp := dEp, d2e_hasElement := d2eH, d2e_element := d2eE, sb := sb })

-- rule execute: on a stale (squashed) instruction, just undo its scoreboard
-- reservation; otherwise run the ALU/branch-resolution/address-generation
-- logic, and for a memory instruction, read/write `dmem` directly (storing
-- the value for a store, then reading it back either way -- mirroring
-- BRAM's `responseOnWrite`) and extract the load-sized/signed result on the
-- spot, or update pc/eEp for a taken branch.
def rule_RL_execute_core (d2eElement : t_d2e) (eEp : BitVec 1) (sb : Array (BitVec 2))
    (pc : BitVec 32) (dmem : Array (BitVec 32)) (e2wElement : t_e2w)
    (d2eHasElement e2wHasElement : Bool) :
    t_bool × Array (BitVec 2) × Array (BitVec 32) × BitVec 1 × BitVec 32 × Bool × t_e2w :=
  let dInst := d2eElement.dInst
  let dPc := d2eElement.pc
  let ppc := d2eElement.ppc
  let ieEp := d2eElement.ieEp
  let rv1 := d2eElement.rv1
  let rv2 := d2eElement.rv2
  let ieEpMismatch := bool_not (if ieEp == eEp then BTrue Unit_ else BFalse Unit_)

  -- squash branch: instruction was speculatively issued after a redirect
  -- that has since happened; just release its scoreboard reservation
  -- (gated on `.legal` to match decode's `rdCond`, which never reserved in
  -- the first place for an illegal instruction).
  let squashRdIdx := (RVUtil.getInstFields dInst.inst).rd
  let squashCond := bool_and dInst.legal
    (bool_and dInst.valid_rd (bool_not (if squashRdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))
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

  -- memory-instruction sub-branch: write dmem (if a store), then read it
  -- back and extract the addressed sub-word.
  let shiftAmount := concat_bits offset 3 (0 : BitVec 3)
  let dataMem := shift_left rv2 shiftAmount
  let addrMemIdx : BitVec 30 := extract_bits addr0 31 2
  let isUnsignedMem := extract_bit funct3 2
  let isStore := if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool isUnsignedMem, size := size, offset := offset }

  -- non-memory (control/ALU) sub-branch: resolve the branch/jump target.
  -- `pcMismatch` is gated on `dInst.legal`: an illegal instruction never
  -- redirects `pc`/`eEp`, even if its bit pattern happens to look like a
  -- taken branch/jump -- matching decode's `redirected` (also gated on
  -- legality) so that neither pipeline stage ever changes control-flow
  -- state on behalf of an illegal instruction.
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm dPc).nextPC
  let pcMismatch := bool_and dInst.legal (bool_not (if nextPC == ppc then BTrue Unit_ else BFalse Unit_))

  -- normal branch, pass-through when squashing. The store write is also
  -- gated on `dInst.legal`: an illegal instruction flows through the
  -- pipeline exactly like a legal one (same epoch/pc/branch bookkeeping --
  -- see rule_RL_decode_core) but must never actually change architectural
  -- state, so it never writes `dmem` (nor, in rule_RL_writeback_core, `rf`)
  -- even if its bit pattern happens to look like a store.
  let dmemNormal := ite_bsv (bool_and isMemInst (bool_and isStore dInst.legal))
    (M_mkSimpleMem.write dmem addrMemIdx dataMem) dmem
  let dataFinal := ite_bsv isMemInst (processMem memBusinessVal (M_mkSimpleMem.read dmemNormal addrMemIdx)) dataCtrl
  let e2wVal : t_e2w := { data := dataFinal, dInst := dInst, pc := dPc }
  let eEpNormal := eEp + ite_bsv pcMismatch (-1 : BitVec 1) (0 : BitVec 1)
  let pcNormal := ite_bsv pcMismatch nextPC pc

  let newSb := match _ : ieEpMismatch with | BTrue _ => squashSb | BFalse _ => sb
  let newDmem := match _ : ieEpMismatch with | BTrue _ => dmem | BFalse _ => dmemNormal
  let newEEp := match _ : ieEpMismatch with | BTrue _ => eEp | BFalse _ => eEpNormal
  let newPc := match _ : ieEpMismatch with | BTrue _ => pc | BFalse _ => pcNormal
  let newE2wHasElement := match _ : ieEpMismatch with | BTrue _ => e2wHasElement | BFalse _ => true
  let newE2wElement := match _ : ieEpMismatch with | BTrue _ => e2wElement | BFalse _ => e2wVal

  let fireGuard :=
    bool_and (fifo_RDY_deq d2eHasElement)
      (bool_and (fifo_RDY_deq d2eHasElement)
        (match _ : ieEpMismatch with
          | BTrue _ => BTrue Unit_
          | BFalse _ => fifo_RDY_enq e2wHasElement))
  (fireGuard, newSb, newDmem, newEEp, newPc, newE2wHasElement, newE2wElement)

def rule_RL_execute (s : State) : t_bool × State :=
  let (g, sb, dmem, eEp, pc, e2wH, e2wE) :=
    rule_RL_execute_core s.d2e_element s.eEp s.sb s.pc s.dmem s.e2w_element
      s.d2e_hasElement s.e2w_hasElement
  (g, { s with sb := sb, d2e_hasElement := false, dmem := dmem, eEp := eEp, pc := pc, e2w_hasElement := e2wH, e2w_element := e2wE })

-- rule writeback: release the scoreboard, commit the result to rf (skipping
-- x0 / instructions with no destination), and push a retirement record
-- into commitQ for the external getCommit method to drain. (No more
-- memory-response handling here -- execute already extracted the final
-- load value into e2w_element.data.)
def rule_RL_writeback_core (e2wElement : t_e2w) (sb : Array (BitVec 2)) (rf : Array (BitVec 32))
    (e2wHasElement commitQHasElement : Bool) :
    t_bool × Array (BitVec 2) × Array (BitVec 32) × Bool × Bool × t_commit :=
  let dInst := e2wElement.dInst
  let fields := RVUtil.getInstFields dInst.inst
  let rdIdx := fields.rd
  let isValidRd := bool_and dInst.legal
    (bool_and dInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)))
  let commitEntry : t_commit :=
    { inst := dInst.inst, pc := e2wElement.pc, data := ite_bsv isValidRd (some e2wElement.data) none }
  let newSb := arr_set sb rdIdx.toNat
    ((arr_get sb rdIdx.toNat) + ite_bsv isValidRd (-1 : BitVec 2) (0 : BitVec 2))
  let newRf := arr_set rf rdIdx.toNat (ite_bsv isValidRd e2wElement.data (arr_get rf rdIdx.toNat))

  let fireGuard :=
    bool_and (fifo_RDY_deq e2wHasElement)
      (bool_and (fifo_RDY_deq e2wHasElement) (fifo_RDY_enq commitQHasElement))
  (fireGuard, newSb, newRf, false, true, commitEntry)

def rule_RL_writeback (s : State) : t_bool × State :=
  let (g, sb, rf, e2wH, commitQH, commitQE) :=
    rule_RL_writeback_core s.e2w_element s.sb s.rf s.e2w_hasElement s.commitQ_hasElement
  (g, { s with sb := sb, rf := rf, e2w_hasElement := e2wH, commitQ_hasElement := commitQH, commitQ_element := commitQE })

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
