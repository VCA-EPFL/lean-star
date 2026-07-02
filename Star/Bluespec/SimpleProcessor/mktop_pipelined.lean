-- mktop_pipelined.lean - Lean formalization of
-- Star/Bluespec/simple-processor/top_pipelined.bsv (module mktop_pipelined).
-- Wires the pipelined RISC-V core (M_mkpipelined, mkpipelined.bsv) to a single
-- dual-port byte-enabled BRAM (`BRAM2PortBE#(Bit#(20), Word, 4) bram <-
-- mkBRAM2ServerBE(cfg)`), port B carrying instruction fetches and port A
-- carrying data-memory traffic, plus a small MMIO request/response queue for
-- the memory-mapped console/exit registers.
--
-- Per the same "hand-written opaque submodule" convention used throughout
-- this development, `bram` is modeled by reusing the existing
-- Star.Bluespec.Lib.mkSimpleBRAM2 spec (putA/readA/putB/readB, one
-- outstanding request per port) rather than writing a new byte-enabled BRAM
-- model. Two consequences of that reuse, called out where relevant below:
--   * `req.byte_en` only distinguishes "no write" (0) from "write `req.data`"
--     (nonzero); partial-byte merging done by the real BRAM2PortBE hardware
--     is not modeled.
--   * top_pipelined.bsv always requests `responseOnWrite: True`, i.e. every
--     request (read or write) produces a response. mkSimpleBRAM2's putA/putB
--     only latch a response for reads, so the wrappers below additionally
--     latch the just-written value on writes to reproduce responseOnWrite.
--
-- `mktop_pipelined` is declared `module mktop_pipelined(Empty)` in the source
-- and every method of the (would-be) `Top` interface is commented out, so
-- this module exposes no methods, only rules.

import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.Lib.mkBypassFIFO
import Star.Bluespec.SimpleProcessor.Params_types
import Star.Bluespec.SimpleProcessor.mkpipelined
open BluespecPrelude
open Params_types

namespace M_mktop_pipelined

structure state where
  bram : M_mkSimpleBRAM2.state (BitVec 32)
  rvCore : M_mkpipelined.state
  ireq : t_mem
  dreq : M_mkBypassFIFO.state t_mem
  mmioreq : M_mkBypassFIFO.state t_mem
deriving Inhabited

-- portA.request.put(BRAMRequestBE{writeen, responseOnWrite: True, address, datain})
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

-- rule requestI: fetch request, routed to port B. (The `debug`-guarded
-- $display in the source is simulation-only console I/O; elided.)
def rule_RL_requestI : state → (t_bool × state) :=
  fun (s : state) =>
    let req := M_mkpipelined.meth_getIReqV s.rvCore
    let addrB := (truncate (shift_right_logical req.addr (2 : Nat)) 20 : BitVec 20)
    let fireGuard :=
      bool_and (M_mkpipelined.meth_RDY_getIReqV s.rvCore)
        (bool_and (M_mkpipelined.meth_RDY_getIReqA s.rvCore)
          (M_mkSimpleBRAM2.meth_RDY_putB s.bram))
    (fireGuard,
      { { { s with rvCore := (M_mkpipelined.meth_getIReqA s.rvCore).avAction_ }
            with ireq := req }
        with bram := putB_withResponse s.bram req.byte_en addrB req.data })

-- rule responseI: latch port B's response into the core's instruction response.
def rule_RL_responseI : state → (t_bool × state) :=
  fun (s : state) =>
    let x := (M_mkSimpleBRAM2.meth_readB s.bram).avValue_
    let req := { s.ireq with data := x }
    let fireGuard :=
      bool_and (M_mkSimpleBRAM2.meth_RDY_readB s.bram) (M_mkpipelined.meth_RDY_getIResp s.rvCore)
    (fireGuard,
      { { s with bram := (M_mkSimpleBRAM2.meth_readB s.bram).avAction_ }
          with rvCore := (M_mkpipelined.meth_getIResp s.rvCore req).avAction_ })

-- rule requestD: data-memory request, routed to port A; also recorded in
-- `dreq` so responseD can recover the original request shape.
def rule_RL_requestD : state → (t_bool × state) :=
  fun (s : state) =>
    let req := M_mkpipelined.meth_getDReqV s.rvCore
    let addrA := (truncate (shift_right_logical req.addr (2 : Nat)) 20 : BitVec 20)
    let fireGuard :=
      bool_and (M_mkpipelined.meth_RDY_getDReqV s.rvCore)
        (bool_and (M_mkpipelined.meth_RDY_getDReqA s.rvCore)
          (bool_and (M_mkBypassFIFO.meth_RDY_enq s.dreq) (M_mkSimpleBRAM2.meth_RDY_putA s.bram)))
    (fireGuard,
      { { { s with rvCore := (M_mkpipelined.meth_getDReqA s.rvCore).avAction_ }
            with dreq := (M_mkBypassFIFO.meth_enq s.dreq req).avAction_ }
        with bram := putA_withResponse s.bram req.byte_en addrA req.data })

-- rule responseD: latch port A's response into the core's data response.
def rule_RL_responseD : state → (t_bool × state) :=
  fun (s : state) =>
    let x := (M_mkSimpleBRAM2.meth_readA s.bram).avValue_
    let req := { (M_mkBypassFIFO.meth_first s.dreq) with data := x }
    let fireGuard :=
      bool_and (M_mkSimpleBRAM2.meth_RDY_readA s.bram)
        (bool_and (M_mkBypassFIFO.meth_RDY_first s.dreq)
          (bool_and (M_mkBypassFIFO.meth_RDY_deq s.dreq) (M_mkpipelined.meth_RDY_getDResp s.rvCore)))
    (fireGuard,
      { { { s with bram := (M_mkSimpleBRAM2.meth_readA s.bram).avAction_ }
            with dreq := (M_mkBypassFIFO.meth_deq s.dreq).avAction_ }
        with rvCore := (M_mkpipelined.meth_getDResp s.rvCore req).avAction_ })

-- rule requestMMIO: the $fwrite/$fdisplay/$fflush/$finish calls guarded on
-- req.addr/req.byte_en in the source are simulation-only console I/O and
-- simulator termination (STDERR char/int echo, PASS/FAIL reporting, exit on
-- 0xf000fff8) with no effect on the formalized hardware state; elided. The
-- only state-affecting action is always enqueuing the request.
def rule_RL_requestMMIO : state → (t_bool × state) :=
  fun (s : state) =>
    let req := M_mkpipelined.meth_getMMIOReqV s.rvCore
    let fireGuard :=
      bool_and (M_mkpipelined.meth_RDY_getMMIOReqV s.rvCore)
        (bool_and (M_mkpipelined.meth_RDY_getMMIOReqA s.rvCore) (M_mkBypassFIFO.meth_RDY_enq s.mmioreq))
    (fireGuard,
      { { s with rvCore := (M_mkpipelined.meth_getMMIOReqA s.rvCore).avAction_ }
          with mmioreq := (M_mkBypassFIFO.meth_enq s.mmioreq req).avAction_ })

-- rule responseMMIO: echo the (unmodified) MMIO request back as its response.
def rule_RL_responseMMIO : state → (t_bool × state) :=
  fun (s : state) =>
    let req := M_mkBypassFIFO.meth_first s.mmioreq
    let fireGuard :=
      bool_and (M_mkBypassFIFO.meth_RDY_first s.mmioreq)
        (bool_and (M_mkBypassFIFO.meth_RDY_deq s.mmioreq) (M_mkpipelined.meth_RDY_getMMIOResp s.rvCore))
    (fireGuard,
      { { s with mmioreq := (M_mkBypassFIFO.meth_deq s.mmioreq).avAction_ }
          with rvCore := (M_mkpipelined.meth_getMMIOResp s.rvCore req).avAction_ })

end M_mktop_pipelined
