import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.CompiledProcessor.Params_types
import Star.Bluespec.CompiledProcessor.RVUtil
import Star.Bluespec.Lib.mkSimpleBRAM
import Star.Bluespec.Lib.mkFIFO
import Star.Bluespec.CompiledProcessor.mktop_pipelined
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
open BluespecPrelude
open Params_types
open RVUtil
open BluespecVerification
open ReachingStar Bluespec

set_option maxHeartbeats 1000000

-- ═══ Specification (fill in State, methods, and phi0) ═══

namespace M_mktop_pipelined.Spec

structure State where
  pc : BitVec 32
  halted : BitVec 1
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  imem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  dmem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  output : List t_commitinst
deriving Inhabited

def processMem (memBusiness : t_membusiness) (data : BitVec 32) : BitVec 32 :=
  let memDataShifted := shift_right_logical data (concat_bits memBusiness.offset 3 (0 : BitVec 3))
  let combined : BitVec 3 := concat_bits (bool_to_bitvec1 memBusiness.isUnsigned) 2 memBusiness.size
  if combined == (0b000 : BitVec 3) then (sign_extend (extract_bits memDataShifted 7 0) : BitVec 32)
  else if combined == (0b001 : BitVec 3) then (sign_extend (extract_bits memDataShifted 15 0) : BitVec 32)
  else if combined == (0b100 : BitVec 3) then zero_extend (extract_bits memDataShifted 7 0) 32
  else if combined == (0b101 : BitVec 3) then zero_extend (extract_bits memDataShifted 15 0) 32
  else memDataShifted -- 3'b010 (word); other combinations unreachable given RV32I encoding

def stepOne (s : State) : State × t_commitinst :=
  let pc := s.pc
  let instr := s.imem.getD pc.toNat default
  let dInst := RVUtil.decodeInst instr
  let fields := RVUtil.getInstFields instr
  let rdIdx := fields.rd
  let isValidRd := bool_and dInst.valid_rd (bool_not (if rdIdx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))
  let rs1Idx := fields.rs1
  let rs2Idx := fields.rs2
  let rv1 := ite_bsv (if rs1Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
              (0 : BitVec 32) (arr_get s.rf rs1Idx.toNat)
  let rv2 := ite_bsv (if rs2Idx == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_)
              (0 : BitVec 32) (arr_get s.rf rs2Idx.toNat)
  let imm := RVUtil.getImmediate dInst
  let funct3 := fields.funct3
  let size := extract_bits funct3 1 0
  let addr0 := rv1 + imm
  let offset := extract_bits addr0 1 0
  let dataCtrl := ite_bsv (RVUtil.isControlInst dInst) (pc + (4 : BitVec 32))
                    (RVUtil.execALU32 dInst.inst rv1 rv2 imm pc)
  let isMemInst := RVUtil.isMemoryInst dInst
  let shiftAmount := concat_bits offset 3 (0 : BitVec 3)
  let byteEn : BitVec 4 :=
    if size == (0b00 : BitVec 2) then shift_left (0b0001 : BitVec 4) offset
    else if size == (0b01 : BitVec 2) then shift_left (0b0011 : BitVec 4) offset
    else shift_left (0b1111 : BitVec 4) offset -- size = 0b10 (word); 0b11 unused by RV32I
  let dataMem := shift_left rv2 shiftAmount
  let addrMem : BitVec 30 := extract_bits addr0 31 2
  let isUnsignedMem := extract_bit funct3 2
  let typeMem := ite_bsv (if extract_bit dInst.inst 5 == (1 : BitVec 1) then BTrue Unit_ else BFalse Unit_) byteEn (0 : BitVec 4)
  let isStore := if typeMem != (0 : BitVec 4) then BTrue Unit_ else BFalse Unit_
  let nextPC := (RVUtil.execControl32 dInst.inst rv1 rv2 imm pc).nextPC
  let memBusinessVal : t_membusiness :=
    { isUnsigned := bitvec1_to_bool (ite_bsv isMemInst isUnsignedMem (0 : BitVec 1)), size := size, offset := offset }
  let finalData : BitVec 32 :=
    match _ : isMemInst with
    | BTrue _ => processMem memBusinessVal (s.dmem.getD addrMem.toNat default)
    | BFalse _ => dataCtrl
  let newDmem : Array (BitVec 32) :=
    match _ : isMemInst with
    | BTrue _ => (match _ : isStore with
        | BTrue _ => s.dmem.setIfInBounds addrMem.toNat dataMem
        | BFalse _ => s.dmem)
    | BFalse _ => s.dmem
  let legalCommitInfo : t_commitinst := { inst := instr, pc := pc, rd := rdIdx, data := ite_bsv isValidRd finalData 0 }
  let legalNewState : State :=
    { s with
        rf := arr_set s.rf rdIdx.toNat (ite_bsv isValidRd finalData (arr_get s.rf rdIdx.toNat)),
        dmem := newDmem,
        pc := nextPC,
        output := legalCommitInfo :: s.output}
  let illegalCommitInfo : t_commitinst := { inst := instr, pc := pc, rd := rdIdx, data := 0 }
  let illegalNewState : State := { s with pc := pc + (4 : BitVec 32), halted := 1 }
  match _ : dInst.legal with
  | BTrue _ => (legalNewState, legalCommitInfo)
  | BFalse _ => (illegalNewState, illegalCommitInfo)

def meth_getCommit (s : State) : t_actionvalue_ t_commitinst State :=
  let (s', c) := stepOne s
  { avValue_ := c, avAction_ := s' }
def meth_RDY_getCommit (_ : State) : t_bool := BTrue Unit_

def initS : State := default

#eval ((stepOne (stepOne { initS with pc := 0, rf := .mk (List.replicate 32 0), imem := .mk (List.replicate 10 0x00108093) }).1).1).rf

end M_mktop_pipelined.Spec

namespace M_mktop_pipelined.Refines

@[grind cases]
inductive Method : Type where
| meth_getCommitInst

@[grind cases]
inductive Rule : Type where
| RL_requestI
| RL_responseI
| RL_requestD
| RL_responseD
| RL_fetch
| RL_decode
| RL_execute
| RL_writeback

def SpecModule : Bluespec.Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .meth_getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommit M_mktop_pipelined.Spec.meth_RDY_getCommit
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.state
  methods
    | .meth_getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules
    | .RL_requestI => ofRule M_mktop_pipelined.rule_RL_requestI
    | .RL_responseI => ofRule M_mktop_pipelined.rule_RL_responseI
    | .RL_requestD => ofRule M_mktop_pipelined.rule_RL_requestD
    | .RL_responseD => ofRule M_mktop_pipelined.rule_RL_responseD
    | .RL_fetch => ofRule M_mktop_pipelined.rule_RL_fetch
    | .RL_decode => ofRule M_mktop_pipelined.rule_RL_decode
    | .RL_execute => ofRule M_mktop_pipelined.rule_RL_execute
    | .RL_writeback => ofRule M_mktop_pipelined.rule_RL_writeback

-- ──────────────────────────────────────────────────────────────────────
-- Generic helpers for peeling apart `t_bool`/`bool_and`/`bool_or` conjunctions
-- (same role as the identically-named lemmas in mktop_pipelined_spec.lean).
@[simp] theorem bool_and_true_iff (p q : t_bool) :
    bool_and p q = BTrue Unit_ ↔ p = BTrue Unit_ ∧ q = BTrue Unit_ := by
  cases p <;> cases q <;> simp [bool_and]

@[simp] theorem bool_and_false_right (p : t_bool) : bool_and p (BFalse Unit_) = BFalse Unit_ := by
  cases p <;> rfl

@[simp] theorem bool_and_false_left (p : t_bool) : bool_and (BFalse Unit_) p = BFalse Unit_ := by
  rfl

@[simp] theorem bool_and_true_right (p : t_bool) : bool_and p (BTrue Unit_) = p := by
  cases p <;> rfl

@[simp] theorem tbool_match_same {α : Type} (x : t_bool) (y : α) :
    (match x with | BTrue _ => y | BFalse _ => y) = y := by
  cases x <;> rfl

-- `M_mkSimpleBRAM.meth_RDY_put`/`meth_RDY_read` are unconditionally `BTrue` --
-- the modelled BRAM never stalls -- so every guard clause mentioning them
-- collapses immediately.
@[simp] theorem mkSimpleBRAM_RDY_put_true [Inhabited α] (s : M_mkSimpleBRAM.state α) :
    M_mkSimpleBRAM.meth_RDY_put s = BTrue Unit_ := rfl

@[simp] theorem mkSimpleBRAM_RDY_read_true [Inhabited α] (s : M_mkSimpleBRAM.state α) :
    M_mkSimpleBRAM.meth_RDY_read s = BTrue Unit_ := rfl

-- `M_mkFIFO`'s single-element-buffer ready signals, spelled out in terms of
-- `hasElement` so guard equations reduce to plain `Bool` facts instead of
-- staying stuck as opaque `t_bool` values.
@[simp] theorem mkFIFO_RDY_enq_iff [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_enq s = BTrue Unit_ ↔ s.hasElement = false := by
  unfold M_mkFIFO.meth_RDY_enq; split <;> simp_all

@[simp] theorem mkFIFO_RDY_deq_iff [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_deq s = BTrue Unit_ ↔ s.hasElement = true := by
  unfold M_mkFIFO.meth_RDY_deq; split <;> simp_all

@[simp] theorem mkFIFO_RDY_first_iff [Inhabited α] (s : M_mkFIFO.state α) :
    M_mkFIFO.meth_RDY_first s = BTrue Unit_ ↔ s.hasElement = true := by
  unfold M_mkFIFO.meth_RDY_first; split <;> simp_all

theorem mkFIFO_deq_hasElement [Inhabited α] (s : M_mkFIFO.state α) :
    (M_mkFIFO.meth_deq s).avAction_.hasElement = false := rfl

theorem mkFIFO_enq_hasElement [Inhabited α] (s : M_mkFIFO.state α) (x : α) :
    (M_mkFIFO.meth_enq s x).avAction_.hasElement = true := rfl

-- The abstraction relation (the user's `phi0`); couples impl and spec state.
def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop := sorry

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  False := by
  sorry

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  False := by
  sorry

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .RL_requestI i i' ∨ ImplModule.getRule .RL_responseI i i' ∨ ImplModule.getRule .RL_requestD i i' ∨ ImplModule.getRule .RL_responseD i i' ∨ ImplModule.getRule .RL_fetch i i' ∨ ImplModule.getRule .RL_decode i i' ∨ ImplModule.getRule .RL_execute i i' ∨ ImplModule.getRule .RL_writeback i i' := by
  sorry

@[local grind →] theorem commutes_RL_requestI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

-- `ireq` is now a proper `M_mkFIFO` single-element buffer (mirroring the D-side's
-- `dreq`): `RL_requestI` requires `RDY_enq(ireq)` (empty) and `RL_responseI` requires
-- `RDY_deq(ireq)` (non-empty) -- mutually exclusive, so the two rules can never be
-- simultaneously enabled from the same state.
@[local grind →] theorem commutes_RL_requestI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_responseI] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.ireq.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_requestI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_responseD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestI_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_fetch] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.toImem.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_requestI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_decode] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_execute] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestI a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestI, M_mktop_pipelined.rule_RL_writeback] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

-- See `commutes_RL_requestI_RL_responseI` (the ordered-opposite of this pair): fully
-- proven via `ireq`'s FIFO mutual exclusion, ported here via the standard commute-swap
-- trick.
@[local grind →] theorem commutes_RL_responseI_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_requestI_RL_responseI hb hc
  exact ⟨d, hd2, hd1⟩

@[local grind →] theorem commutes_RL_responseI_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_responseI_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseI_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_responseD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseI_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_fetch] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseI_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_decode] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.fromImem.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_responseI_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_execute] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseI_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseI a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseI, M_mktop_pipelined.rule_RL_writeback] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_requestI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_responseI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_requestD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_responseD] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.dreq.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_requestD_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_fetch] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_requestD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_decode] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

-- `toDmem` is shared: `RL_requestD` dequeues it (needs `hasElement = true`) while
-- `RL_execute` conditionally enqueues into it (needs `hasElement = false`), but only
-- in its `¬squash ∧ isMemoryInst` branch. Given `RL_requestD`'s guard, that branch is
-- impossible, so `RL_execute` never actually touches `toDmem` when both fire together.
@[local grind →] theorem commutes_RL_requestD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_execute] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     clear hc hb;
     simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1;
     generalize hsq : (if ((M_mkFIFO.meth_first a.d2e).iEp == a.ep) = true then BTrue Unit_ else BFalse Unit_) = sq at hb1 ⊢;
     generalize hmem : (isMemoryInst (M_mkFIFO.meth_first a.d2e).dInst) = mem at hb1 ⊢;
     cases sq <;> cases mem <;>
       simp only [bool_not, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hb1 ⊢ <;>
       first
         | rfl
         | (exfalso; simp_all; done)
         | (simp_all; done))

@[local grind →] theorem commutes_RL_requestD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_requestD a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_requestD, M_mktop_pipelined.rule_RL_writeback] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseD_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_requestI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseD_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_responseI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseD_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_requestD] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.dreq.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_responseD_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_responseD_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_fetch c).2, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_fetch] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseD_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_decode c).2, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_decode] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_responseD_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_execute c).2, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_execute] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

-- `fromDmem` is shared: `RL_responseD` enqueues it unconditionally; `RL_writeback`
-- dequeues it only in its `isMemoryInst` branch. Given both guards, that branch is
-- provably excluded (`RL_writeback`'s `isMemoryInst` branch would need `fromDmem` empty,
-- contradicting `RL_responseD`'s enqueue-readiness), so `RL_writeback` must be in its
-- non-memory branch, which never touches `fromDmem`.
@[local grind →] theorem commutes_RL_responseD_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_responseD a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_responseD, M_mktop_pipelined.rule_RL_writeback] at hc hb
  obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  have hfromDmem_empty : a.fromDmem.hasElement = false := by
    have hc1' := hc1
    simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hc1'
    tauto
  have hnotmem : isMemoryInst (M_mkFIFO.meth_first a.e2w).dInst = BFalse Unit_ := by
    by_contra hne
    have hmem : isMemoryInst (M_mkFIFO.meth_first a.e2w).dInst = BTrue Unit_ := by
      cases h : isMemoryInst (M_mkFIFO.meth_first a.e2w).dInst with
      | BTrue u => cases u; rfl
      | BFalse u => cases u; exact absurd h hne
    have hb1' := hb1
    rw [hmem] at hb1'
    simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hb1'
    have hfromDmem_full : a.fromDmem.hasElement = true := by tauto
    rw [hfromDmem_empty] at hfromDmem_full
    exact absurd hfromDmem_full (by decide)
  rw [hnotmem] at hb1 hb2
  -- fields of c untouched by responseD
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_toImem : c.toImem = a.toImem := by rw [← hc2]
  have hc_fromImem : c.fromImem = a.fromImem := by rw [← hc2]
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_f2d : c.f2d = a.f2d := by rw [← hc2]
  have hc_d2e : c.d2e = a.d2e := by rw [← hc2]
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hc_pc : c.pc = a.pc := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_sb : c.sb = a.sb := by rw [← hc2]
  have hc_dMem : c.dMem = (M_mkSimpleBRAM.meth_read a.dMem).avAction_ := by rw [← hc2]
  have hc_dreq : c.dreq = (M_mkFIFO.meth_deq a.dreq).avAction_ := by rw [← hc2]
  -- fields of b untouched by writeback (given hnotmem)
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hb_toDmem : b.toDmem = a.toDmem := by rw [← hb2]
  have hb_fromDmem : b.fromDmem = a.fromDmem := by rw [← hb2]
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_d2e : b.d2e = a.d2e := by rw [← hb2]
  have hb_pc : b.pc = a.pc := by rw [← hb2]
  have hb_ep : b.ep = a.ep := by rw [← hb2]
  have hc_wb_guard : (M_mktop_pipelined.rule_RL_writeback c).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_retiredInst, hc_e2w, hnotmem]
    exact hb1
  have hb_responseD_guard : (M_mktop_pipelined.rule_RL_responseD b).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_responseD]
    rw [hb_dMem, hb_dreq, hb_fromDmem]
    exact hc1
  -- fields untouched by both rules
  have hiMem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.iMem = (M_mktop_pipelined.rule_RL_writeback c).2.iMem := by
    show b.iMem = c.iMem; rw [hb_iMem, hc_iMem]
  have hireq_eq : (M_mktop_pipelined.rule_RL_responseD b).2.ireq = (M_mktop_pipelined.rule_RL_writeback c).2.ireq := by
    show b.ireq = c.ireq; rw [hb_ireq, hc_ireq]
  have htoImem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.toImem = (M_mktop_pipelined.rule_RL_writeback c).2.toImem := by
    show b.toImem = c.toImem; rw [hb_toImem, hc_toImem]
  have hfromImem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.fromImem = (M_mktop_pipelined.rule_RL_writeback c).2.fromImem := by
    show b.fromImem = c.fromImem; rw [hb_fromImem, hc_fromImem]
  have htoDmem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.toDmem = (M_mktop_pipelined.rule_RL_writeback c).2.toDmem := by
    show b.toDmem = c.toDmem; rw [hb_toDmem, hc_toDmem]
  have hf2d_eq : (M_mktop_pipelined.rule_RL_responseD b).2.f2d = (M_mktop_pipelined.rule_RL_writeback c).2.f2d := by
    show b.f2d = c.f2d; rw [hb_f2d, hc_f2d]
  have hd2e_eq : (M_mktop_pipelined.rule_RL_responseD b).2.d2e = (M_mktop_pipelined.rule_RL_writeback c).2.d2e := by
    show b.d2e = c.d2e; rw [hb_d2e, hc_d2e]
  have hpc_eq : (M_mktop_pipelined.rule_RL_responseD b).2.pc = (M_mktop_pipelined.rule_RL_writeback c).2.pc := by
    show b.pc = c.pc; rw [hb_pc, hc_pc]
  have hep_eq : (M_mktop_pipelined.rule_RL_responseD b).2.ep = (M_mktop_pipelined.rule_RL_writeback c).2.ep := by
    show b.ep = c.ep; rw [hb_ep, hc_ep]
  have hsb_eq : (M_mktop_pipelined.rule_RL_responseD b).2.sb = (M_mktop_pipelined.rule_RL_writeback c).2.sb := by
    show b.sb = (M_mktop_pipelined.rule_RL_writeback c).2.sb
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hc_sb]
    rfl
  have hrf_eq : (M_mktop_pipelined.rule_RL_responseD b).2.rf = (M_mktop_pipelined.rule_RL_writeback c).2.rf := by
    show b.rf = (M_mktop_pipelined.rule_RL_writeback c).2.rf
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hc_rf, hnotmem]
    rfl
  have hretiredInst_eq : (M_mktop_pipelined.rule_RL_responseD b).2.retiredInst = (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst := by
    show b.retiredInst = (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hnotmem]
    rfl
  have he2w_eq : (M_mktop_pipelined.rule_RL_responseD b).2.e2w = (M_mktop_pipelined.rule_RL_writeback c).2.e2w := by
    show b.e2w = (M_mktop_pipelined.rule_RL_writeback c).2.e2w
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w]
  have hdMem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.dMem = (M_mktop_pipelined.rule_RL_writeback c).2.dMem := by
    have h1 : (M_mktop_pipelined.rule_RL_responseD b).2.dMem = (M_mkSimpleBRAM.meth_read a.dMem).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseD]; rw [hb_dMem]
    rw [h1]
    show (M_mkSimpleBRAM.meth_read a.dMem).avAction_ = c.dMem
    rw [hc_dMem]
  have hdreq_eq : (M_mktop_pipelined.rule_RL_responseD b).2.dreq = (M_mktop_pipelined.rule_RL_writeback c).2.dreq := by
    have h1 : (M_mktop_pipelined.rule_RL_responseD b).2.dreq = (M_mkFIFO.meth_deq a.dreq).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseD]; rw [hb_dreq]
    rw [h1]
    show (M_mkFIFO.meth_deq a.dreq).avAction_ = c.dreq
    rw [hc_dreq]
  have hfromDmem_eq : (M_mktop_pipelined.rule_RL_responseD b).2.fromDmem = (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem := by
    have h1 : (M_mktop_pipelined.rule_RL_responseD b).2.fromDmem =
        (M_mkFIFO.meth_enq b.fromDmem { byte_en := (M_mkFIFO.meth_first b.dreq).byte_en, addr := (M_mkFIFO.meth_first b.dreq).addr, data := (ActionValue (M_mkSimpleBRAM.meth_read b.dMem) 0).avValue }).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseD]
    have h2 : (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem = c.fromDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w, hnotmem]
    rw [h1, hb_fromDmem, hb_dreq, hb_dMem, h2, ← hc2]
  have final_eq : (M_mktop_pipelined.rule_RL_responseD b).2 = (M_mktop_pipelined.rule_RL_writeback c).2 :=
    (M_mktop_pipelined.state.mk.injEq ..).mpr
      ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
       hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2,
    Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩⟩
  · exact Prod.ext hc_wb_guard rfl
  · exact Prod.ext hb_responseD_guard final_eq

@[local grind →] theorem commutes_RL_fetch_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_requestI] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.toImem.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_fetch_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_responseI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_fetch_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_fetch_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_responseD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_fetch_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_fetch_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_decode] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.f2d.hasElement with _ | _ <;> simp_all

-- `RL_fetch` and `RL_execute` both write `pc`: `RL_fetch` sets `pc := pc + 4`
-- relative to the *current* `pc`, while `RL_execute` (on a taken/mispredicted branch)
-- sets `pc := nextPC` *unconditionally*. When `RL_execute` does NOT mispredict (the
-- common case), `RL_fetch`/`RL_execute` touch disjoint enough fields that this is a
-- plain 1-step diamond -- fully proven below via an internal case split.
--
-- When `RL_execute` DOES mispredict (flips `ep`), the entry `RL_fetch` just enqueued
-- into `f2d` (tagged with the pre-flip `ep`) is now stale. The fix: fire `RL_execute`,
-- then `RL_requestI`/`RL_responseI` (using the very `toImem` request `RL_fetch` itself
-- enqueued) to populate `fromImem`, then `RL_decode` (which now squash-drops the stale
-- entry -- no operand-readiness needed on that branch anymore), then `RL_fetch` again,
-- then ANOTHER `RL_requestI`/`RL_responseI` round (draining the *second* `RL_fetch`'s
-- fresh request) -- 7 steps total. On the execute-first side: `RL_fetch`, `RL_requestI`,
-- `RL_responseI` -- 3 steps. `commutes_RL_fetch_RL_execute_given_FetchPipeInv` below
-- proves this converges exactly (the second `RL_requestI` on the fetch-first side
-- re-latches `iMem.readResult` to the SAME post-redirect address the execute-first
-- side's `RL_requestI` reads, since both fire `RL_fetch` at the same post-redirect
-- `pc`), given `FetchPipeInv a` (`a.f2d` empty implies `a.ireq`/`a.fromImem` empty --
-- true of every reachable state, since there's only ever one fetch request in flight
-- through that pipe at a time). `FetchPipeInv` isn't provable here without `phi0`, so
-- the unconditional lemma below still can't discharge the misprediction branch and
-- stays `sorry` there.
@[local grind →] theorem commutes_RL_fetch_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hcg : (M_mktop_pipelined.rule_RL_fetch a).1 = BTrue Unit_ := by rw [hc]
  have hcg_raw := hcg
  dsimp only [M_mktop_pipelined.rule_RL_fetch] at hcg
  simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff] at hcg
  have ha_f2d : a.f2d.hasElement = false := by tauto
  have ha_toImem : a.toImem.hasElement = false := by tauto
  obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  -- fields of `c` untouched by fetch
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_dMem : c.dMem = a.dMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_dreq : c.dreq = a.dreq := by rw [← hc2]
  have hc_fromImem : c.fromImem = a.fromImem := by rw [← hc2]
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_d2e : c.d2e = a.d2e := by rw [← hc2]
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_sb : c.sb = a.sb := by rw [← hc2]
  have hc_fromDmem : c.fromDmem = a.fromDmem := by rw [← hc2]
  have hc_pc : c.pc = a.pc + 4 := by rw [← hc2]
  have hc_f2d : c.f2d = (M_mkFIFO.meth_enq a.f2d { pc := a.pc, ppc := a.pc + 4, iEp := a.ep }).avAction_ := by rw [← hc2]
  have hc_toImem : c.toImem = (M_mkFIFO.meth_enq a.toImem { byte_en := 0, addr := a.pc, data := 0 }).avAction_ := by rw [← hc2]
  -- fields of `b` untouched or determined by execute
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hb_retiredInst : b.retiredInst = a.retiredInst := by rw [← hb2]
  have hb_rf : b.rf = a.rf := by rw [← hb2]
  have hbg : (M_mktop_pipelined.rule_RL_execute a).1 = BTrue Unit_ := by rw [hb]
  have hep_dichotomy : (b.pc = a.pc ∧ b.ep = a.ep) ∨ b.ep = a.ep + 1 := by
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_execute]
    repeat' split
    all_goals first
      | (left; constructor <;> rfl)
      | (right; rfl)
      | (left; constructor <;> simp_all [bool_to_bitvec1, bool_not])
      | (right; simp_all [bool_to_bitvec1, bool_not])
      | simp_all
  rcases hep_dichotomy with ⟨hb_pc, hb_ep⟩ | hb_ep
  · -- EASY: no misprediction, 1-step diamond
    have hce_guard : (M_mktop_pipelined.rule_RL_execute c).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_execute] at hbg ⊢
      rw [hc_d2e, hc_ep, hc_toDmem, hc_e2w]
      exact hbg
    have hbf_guard : (M_mktop_pipelined.rule_RL_fetch b).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch] at hcg_raw ⊢
      rw [hb_f2d, hb_toImem]
      exact hcg_raw
    have hpc_ep_combined :
        ((M_mktop_pipelined.rule_RL_execute c).2.pc = c.pc ∧ (M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep ∧
         (M_mktop_pipelined.rule_RL_execute a).2.pc = a.pc ∧ (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep) ∨
        ((M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep + 1 ∧ (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep + 1) := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
      rw [hc_d2e, hc_ep]
      repeat' split
      all_goals first
        | (left; refine ⟨rfl, rfl, rfl, rfl⟩)
        | (right; exact ⟨rfl, rfl⟩)
        | (left; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [bool_to_bitvec1, bool_not])
        | (right; constructor <;> simp_all [bool_to_bitvec1, bool_not])
        | simp_all
    have ha_pc : (M_mktop_pipelined.rule_RL_execute a).2.pc = a.pc := (congrArg (·.pc) hb2).trans hb_pc
    have ha_ep : (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep := (congrArg (·.ep) hb2).trans hb_ep
    have hbv1_ne_succ : ∀ x : BitVec 1, x ≠ x + 1 := by decide
    have hc_ep_pass : (M_mktop_pipelined.rule_RL_execute c).2.pc = c.pc ∧
        (M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep := by
      rcases hpc_ep_combined with ⟨h1, h2, _, _⟩ | ⟨_, h4⟩
      · exact ⟨h1, h2⟩
      · exact absurd (ha_ep.symm.trans h4) (hbv1_ne_succ a.ep)
    have hf2d_eq : (M_mktop_pipelined.rule_RL_execute c).2.f2d = (M_mktop_pipelined.rule_RL_fetch b).2.f2d := by
      have h1 : (M_mktop_pipelined.rule_RL_execute c).2.f2d = c.f2d := by
        rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.f2d =
          (M_mkFIFO.meth_enq b.f2d { pc := b.pc, ppc := b.pc + 4, iEp := b.ep }).avAction_ := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h1, h2, hb_f2d, hb_pc, hb_ep, hc_f2d]
    have htoImem_eq : (M_mktop_pipelined.rule_RL_execute c).2.toImem = (M_mktop_pipelined.rule_RL_fetch b).2.toImem := by
      have h1 : (M_mktop_pipelined.rule_RL_execute c).2.toImem = c.toImem := by
        rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.toImem =
          (M_mkFIFO.meth_enq b.toImem { byte_en := 0, addr := b.pc, data := 0 }).avAction_ := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h1, h2, hb_toImem, hb_pc, hc_toImem]
    have hpc_eq : (M_mktop_pipelined.rule_RL_execute c).2.pc = (M_mktop_pipelined.rule_RL_fetch b).2.pc := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.pc = b.pc + 4 := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [hc_ep_pass.1, h2, hb_pc, hc_pc]
    have hep_eq : (M_mktop_pipelined.rule_RL_execute c).2.ep = (M_mktop_pipelined.rule_RL_fetch b).2.ep := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.ep = b.ep := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [hc_ep_pass.2, h2, hb_ep, hc_ep]
    have hd2e_eq : (M_mktop_pipelined.rule_RL_execute c).2.d2e = (M_mktop_pipelined.rule_RL_fetch b).2.d2e := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.d2e = b.d2e := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hsb_eq : (M_mktop_pipelined.rule_RL_execute c).2.sb = (M_mktop_pipelined.rule_RL_fetch b).2.sb := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.sb = b.sb := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have he2w_eq : (M_mktop_pipelined.rule_RL_execute c).2.e2w = (M_mktop_pipelined.rule_RL_fetch b).2.e2w := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.e2w = b.e2w := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have htoDmem_eq : (M_mktop_pipelined.rule_RL_execute c).2.toDmem = (M_mktop_pipelined.rule_RL_fetch b).2.toDmem := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.toDmem = b.toDmem := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hiMem_eq : (M_mktop_pipelined.rule_RL_execute c).2.iMem = (M_mktop_pipelined.rule_RL_fetch b).2.iMem := by
      show c.iMem = b.iMem; rw [hc_iMem, hb_iMem]
    have hdMem_eq : (M_mktop_pipelined.rule_RL_execute c).2.dMem = (M_mktop_pipelined.rule_RL_fetch b).2.dMem := by
      show c.dMem = b.dMem; rw [hc_dMem, hb_dMem]
    have hireq_eq : (M_mktop_pipelined.rule_RL_execute c).2.ireq = (M_mktop_pipelined.rule_RL_fetch b).2.ireq := by
      show c.ireq = b.ireq; rw [hc_ireq, hb_ireq]
    have hdreq_eq : (M_mktop_pipelined.rule_RL_execute c).2.dreq = (M_mktop_pipelined.rule_RL_fetch b).2.dreq := by
      show c.dreq = b.dreq; rw [hc_dreq, hb_dreq]
    have hfromImem_eq : (M_mktop_pipelined.rule_RL_execute c).2.fromImem = (M_mktop_pipelined.rule_RL_fetch b).2.fromImem := by
      show c.fromImem = b.fromImem; rw [hc_fromImem, hb_fromImem]
    have hfromDmem_eq : (M_mktop_pipelined.rule_RL_execute c).2.fromDmem = (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem = b.fromDmem := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hretiredInst_eq : (M_mktop_pipelined.rule_RL_execute c).2.retiredInst = (M_mktop_pipelined.rule_RL_fetch b).2.retiredInst := by
      show c.retiredInst = b.retiredInst; rw [hc_retiredInst, hb_retiredInst]
    have hrf_eq : (M_mktop_pipelined.rule_RL_execute c).2.rf = (M_mktop_pipelined.rule_RL_fetch b).2.rf := by
      show c.rf = b.rf; rw [hc_rf, hb_rf]
    have final_eq : (M_mktop_pipelined.rule_RL_execute c).2 = (M_mktop_pipelined.rule_RL_fetch b).2 :=
      (M_mktop_pipelined.state.mk.injEq ..).mpr
        ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
         hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
    refine ⟨(M_mktop_pipelined.rule_RL_execute c).2,
      Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩
    · exact Prod.ext hce_guard rfl
    · exact Prod.ext hbf_guard final_eq.symm
  · -- HARD: misprediction (see below)
    sorry
-- `RL_fetch` only touches `f2d`/`pc`/`toImem`, and `RL_writeback` only touches
-- `e2w`/`fromDmem`/`sb`/`rf`/`retiredInst` -- completely disjoint field sets (this used to
-- be blocked by `halted`: `RL_writeback` could set it and `RL_fetch`'s guard required
-- `¬halted`, but `halted` no longer exists in this design), so this is now a
-- straightforward one-step diamond.
@[local grind →] theorem commutes_RL_fetch_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch, M_mktop_pipelined.rule_RL_writeback] at hc hb
  obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  -- fields untouched by fetch
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_dMem : c.dMem = a.dMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_dreq : c.dreq = a.dreq := by rw [← hc2]
  have hc_fromImem : c.fromImem = a.fromImem := by rw [← hc2]
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_d2e : c.d2e = a.d2e := by rw [← hc2]
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_sb : c.sb = a.sb := by rw [← hc2]
  have hc_fromDmem : c.fromDmem = a.fromDmem := by rw [← hc2]
  -- fields untouched by writeback
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hb_toDmem : b.toDmem = a.toDmem := by rw [← hb2]
  have hb_d2e : b.d2e = a.d2e := by rw [← hb2]
  have hb_ep : b.ep = a.ep := by rw [← hb2]
  have hb_pc : b.pc = a.pc := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_wb_guard : (M_mktop_pipelined.rule_RL_writeback c).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_retiredInst, hc_e2w, hc_fromDmem]
    exact hb1
  have hc_fetch_guard : (M_mktop_pipelined.rule_RL_fetch b).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_fetch]
    rw [hb_f2d, hb_toImem]
    exact hc1
  have hiMem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.iMem = (M_mktop_pipelined.rule_RL_fetch b).2.iMem := by
    show c.iMem = b.iMem; rw [hc_iMem, hb_iMem]
  have hdMem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.dMem = (M_mktop_pipelined.rule_RL_fetch b).2.dMem := by
    show c.dMem = b.dMem; rw [hc_dMem, hb_dMem]
  have hireq_eq : (M_mktop_pipelined.rule_RL_writeback c).2.ireq = (M_mktop_pipelined.rule_RL_fetch b).2.ireq := by
    show c.ireq = b.ireq; rw [hc_ireq, hb_ireq]
  have hdreq_eq : (M_mktop_pipelined.rule_RL_writeback c).2.dreq = (M_mktop_pipelined.rule_RL_fetch b).2.dreq := by
    show c.dreq = b.dreq; rw [hc_dreq, hb_dreq]
  have hfromImem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.fromImem = (M_mktop_pipelined.rule_RL_fetch b).2.fromImem := by
    show c.fromImem = b.fromImem; rw [hc_fromImem, hb_fromImem]
  have htoDmem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.toDmem = (M_mktop_pipelined.rule_RL_fetch b).2.toDmem := by
    show c.toDmem = b.toDmem; rw [hc_toDmem, hb_toDmem]
  have hd2e_eq : (M_mktop_pipelined.rule_RL_writeback c).2.d2e = (M_mktop_pipelined.rule_RL_fetch b).2.d2e := by
    show c.d2e = b.d2e; rw [hc_d2e, hb_d2e]
  have hep_eq : (M_mktop_pipelined.rule_RL_writeback c).2.ep = (M_mktop_pipelined.rule_RL_fetch b).2.ep := by
    show c.ep = b.ep; rw [hc_ep, hb_ep]
  -- fields touched only by fetch: f2d, pc, toImem -- need b's fetch value = c's carried-through value
  have hf2d_eq : (M_mktop_pipelined.rule_RL_writeback c).2.f2d = (M_mktop_pipelined.rule_RL_fetch b).2.f2d := by
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.f2d = c.f2d := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.f2d = (M_mkFIFO.meth_enq b.f2d { pc := b.pc, ppc := b.pc + 4, iEp := b.ep }).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    rw [h1, h2, hb_f2d, hb_pc, hb_ep]
    show c.f2d = (M_mkFIFO.meth_enq a.f2d { pc := a.pc, ppc := a.pc + 4, iEp := a.ep }).avAction_
    rw [← hc2]; rfl
  have hpc_eq : (M_mktop_pipelined.rule_RL_writeback c).2.pc = (M_mktop_pipelined.rule_RL_fetch b).2.pc := by
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.pc = c.pc := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.pc = b.pc + 4 := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    rw [h1, h2, hb_pc]
    show c.pc = a.pc + 4
    rw [← hc2]; rfl
  have htoImem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.toImem = (M_mktop_pipelined.rule_RL_fetch b).2.toImem := by
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.toImem = c.toImem := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.toImem = (M_mkFIFO.meth_enq b.toImem { byte_en := 0, addr := b.pc, data := 0 }).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    rw [h1, h2, hb_toImem, hb_pc]
    show c.toImem = (M_mkFIFO.meth_enq a.toImem { byte_en := 0, addr := a.pc, data := 0 }).avAction_
    rw [← hc2]; rfl
  -- fields touched only by writeback: e2w, fromDmem, sb, rf, retiredInst
  have hb_e2w : b.e2w = (M_mkFIFO.meth_deq a.e2w).avAction_ := by rw [← hb2]
  have he2w_eq : (M_mktop_pipelined.rule_RL_writeback c).2.e2w = (M_mktop_pipelined.rule_RL_fetch b).2.e2w := by
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.e2w = b.e2w := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    rw [h2, hb_e2w]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w]
  have hfromDmem_eq : (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem = (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem := by
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem = b.fromDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb_fromDmem : b.fromDmem = (M_mktop_pipelined.rule_RL_writeback a).2.fromDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [← hb2]
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem = (M_mktop_pipelined.rule_RL_writeback a).2.fromDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w, hc_fromDmem]
    rw [h1, h2, hb_fromDmem]
  have hrf_eq : (M_mktop_pipelined.rule_RL_writeback c).2.rf = (M_mktop_pipelined.rule_RL_fetch b).2.rf := by
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.rf = b.rf := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb_rf : b.rf = (M_mktop_pipelined.rule_RL_writeback a).2.rf := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [← hb2]; rfl
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.rf = (M_mktop_pipelined.rule_RL_writeback a).2.rf := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w, hc_fromDmem, hc_rf]
    rw [h1, h2, hb_rf]
  have hretiredInst_eq : (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst = (M_mktop_pipelined.rule_RL_fetch b).2.retiredInst := by
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.retiredInst = b.retiredInst := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb_ri : b.retiredInst = (M_mktop_pipelined.rule_RL_writeback a).2.retiredInst := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [← hb2]; rfl
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst = (M_mktop_pipelined.rule_RL_writeback a).2.retiredInst := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w, hc_fromDmem]
    rw [h1, h2, hb_ri]
  have hsb_eq : (M_mktop_pipelined.rule_RL_writeback c).2.sb = (M_mktop_pipelined.rule_RL_fetch b).2.sb := by
    have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.sb = b.sb := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb_sb : b.sb = (M_mktop_pipelined.rule_RL_writeback a).2.sb := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [← hb2]; rfl
    have h1 : (M_mktop_pipelined.rule_RL_writeback c).2.sb = (M_mktop_pipelined.rule_RL_writeback a).2.sb := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w, hc_sb]
    rw [h1, h2, hb_sb]
  have final_eq : (M_mktop_pipelined.rule_RL_writeback c).2 = (M_mktop_pipelined.rule_RL_fetch b).2 :=
    (M_mktop_pipelined.state.mk.injEq ..).mpr
      ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
       hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2,
    Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩
  · exact Prod.ext hb_wb_guard rfl
  · exact Prod.ext hc_fetch_guard final_eq.symm

@[local grind →] theorem commutes_RL_decode_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_requestI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_decode_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_responseI] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.fromImem.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_decode_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_decode_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_responseD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_decode_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_fetch] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 hb1
  rcases h : a.f2d.hasElement with _ | _ <;> simp_all

@[local grind →] theorem commutes_RL_decode_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

-- Not provable via `exfalso` alone: `RL_decode` checks the epoch and, when
-- `f2d.first.iEp ≠ a.ep`, silently drops the entry (dequeuing `f2d`/`fromImem`) WITHOUT
-- requiring `d2e` to be empty -- so `RL_decode` and `RL_execute` (which always requires
-- `d2e` non-empty) *can* be simultaneously enabled, purely from their own guards.
--
-- The counterexample that shows this needs `iEp`/`ep` being a single bit: `f2d.first.iEp
-- ≠ a.ep` forces `f2d.first.iEp = a.ep + 1`. If `a.d2e` ALSO happens to hold a
-- mispredicting entry, firing `RL_decode` first drops the stale `f2d` entry, but firing
-- `RL_execute` first flips `ep` to `a.ep + 1`, making `RL_decode`'s squash check
-- (`f2d.first.iEp == ep`) read `a.ep + 1 == a.ep + 1` -- true -- so `RL_decode` now
-- treats the entry as fresh and issues it into `d2e` instead of dropping it. Genuinely
-- different trajectories for this specific `a`.
--
-- But this `a` is unreachable: `commutes_RL_decode_RL_execute_given_F2DStaleInv` below
-- proves the pair fully (via `exfalso`, same shape as the pre-epoch-check proof) given
-- `F2DStaleInv a : a.f2d.hasElement → f2d.first.iEp ≠ a.ep → a.d2e.hasElement = false`
-- -- i.e. a stale `f2d` entry always coincides with an empty `d2e`. This holds by
-- induction over reachable states: `RL_execute` is the only rule that changes `ep`, and
-- it *unconditionally* empties `d2e` in the same step, so the instant `f2d` becomes
-- stale, `d2e` is simultaneously drained; `RL_decode` (the only other rule touching
-- `f2d`) makes `f2d` fresh-or-empty on every firing. `F2DStaleInv` isn't provable here
-- without `phi0`, so the unconditional lemma stays `sorry`.
@[local grind →] theorem commutes_RL_decode_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

def F2DStaleInv (a : ImplModule.State) : Prop :=
  a.f2d.hasElement = true → (M_mkFIFO.meth_first a.f2d).iEp ≠ a.ep → a.d2e.hasElement = false

theorem commutes_RL_decode_RL_execute_given_F2DStaleInv {a b c : ImplModule.State}
    (hInv : F2DStaleInv a) :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode, M_mktop_pipelined.rule_RL_execute] at hc hb
  obtain ⟨hc1, _⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, _⟩ := Prod.mk.injEq .. |>.mp hb
  have hb_d2e : a.d2e.hasElement = true := by
    simp only [bool_and_true_iff, mkFIFO_RDY_deq_iff] at hb1
    tauto
  rcases hEM : (if ((M_mkFIFO.meth_first a.f2d).iEp == a.ep) then BTrue Unit_ else BFalse Unit_) with u | u
  · -- non-squash: decode's guard requires RDY_enq(d2e), i.e. d2e empty
    cases u
    rw [hEM] at hc1
    simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hc1
    have hd2e_empty : a.d2e.hasElement = false := by tauto
    rw [hd2e_empty] at hb_d2e
    exact absurd hb_d2e (by decide)
  · -- squash: f2d occupied and stale (iEp ≠ ep), so F2DStaleInv forces d2e empty
    cases u
    have hf2d_occ : a.f2d.hasElement = true := by
      rw [hEM] at hc1
      simp only [bool_and_true_iff, mkFIFO_RDY_deq_iff] at hc1
      tauto
    have hf2d_stale : (M_mkFIFO.meth_first a.f2d).iEp ≠ a.ep := by
      intro heq
      rw [heq] at hEM
      simp at hEM
    have hd2e_empty := hInv hf2d_occ hf2d_stale
    rw [hd2e_empty] at hb_d2e
    exact absurd hb_d2e (by decide)

-- ──────────────────────────────────────────────────────────────────────
-- `SbInv`: the scoreboard invariant needed for `RL_decode`/`RL_writeback` to
-- commute (matching the reference SimpleProcessor file's `SbInv`). `sb[r]` is
-- exactly the number of in-flight instructions (in `d2e`/`e2w`) whose
-- destination register maps to `r`: confirmed directly in the compiled rule
-- bodies -- `RL_decode` increments `sb[rd]` when it issues a legal,
-- `rd ≠ 0` instruction, and `RL_writeback` decrements it (`+ 3#2`, i.e.
-- `-1 mod 4`) when that instruction retires.
--
-- This is *not* wired into `commutes_RL_decode_RL_writeback` below: adding
-- `hInv` to that lemma's signature would make it unusable by
-- `rules_commute_weakly`'s default `by grind` (which needs every
-- `@[local grind →]` commute lemma to hold unconditionally, since `grind` has
-- no way to synthesize a proof of `SbInv a` from nothing when composing
-- `Module.getARule`). So this stays a separate, additional lemma
-- (`commutes_RL_decode_RL_writeback_given_SbInv`) rather than replacing the
-- unconditional one.
theorem bitvec1_bit_and' (p q : t_bool) :
    bit_and (bool_to_bitvec1 p) (bool_to_bitvec1 q) = bool_to_bitvec1 (bool_and p q) := by
  cases p <;> cases q <;> simp [bit_and, bool_to_bitvec1, bool_and]

theorem bitvec1_bit_or' (p q : t_bool) :
    bit_or (bool_to_bitvec1 p) (bool_to_bitvec1 q) = bool_to_bitvec1 (bool_or p q) := by
  cases p <;> cases q <;> simp [bit_or, bool_to_bitvec1, bool_or]

theorem bitvec1_bit_not' (p : t_bool) :
    bit_not (bool_to_bitvec1 p) = bool_to_bitvec1 (bool_not p) := by
  cases p <;> simp [bit_not, bool_to_bitvec1, bool_not]

@[simp] theorem bool_or_true_iff (p q : t_bool) :
    bool_or p q = BTrue Unit_ ↔ p = BTrue Unit_ ∨ q = BTrue Unit_ := by
  cases p <;> cases q <;> simp [bool_or]

theorem bool_or_false_iff (p q : t_bool) :
    bool_or p q = BFalse Unit_ ↔ p = BFalse Unit_ ∧ q = BFalse Unit_ := by
  cases p <;> cases q <;> simp [bool_or]

theorem bool_not_false_iff (p : t_bool) : bool_not p = BFalse Unit_ ↔ p = BTrue Unit_ := by
  cases p <;> simp [bool_not]

theorem arr_get_arr_set_self {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (v : α) (h : i < arr.size) :
    arr_get (arr_set arr i v) i = v := by
  unfold arr_get arr_set
  simp [Array.getElem!_eq_getD, h]

theorem arr_get_arr_set_ne {α : Type} [Inhabited α] (arr : Array α) (i j : Nat) (v : α) (h : i ≠ j) :
    arr_get (arr_set arr i v) j = arr_get arr j := by
  unfold arr_get arr_set
  simp [Array.getElem!_eq_getD, h]

theorem arr_set_self_get {α : Type} [Inhabited α] (arr : Array α) (i : Nat) :
    arr_set arr i (arr_get arr i) = arr := by
  unfold arr_set arr_get
  apply Array.ext_getElem?
  intro k
  by_cases hk : k = i
  · subst hk
    by_cases hbound : k < arr.size
    · simp [Array.getElem?_setIfInBounds_self, hbound]
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hbound]
  · simp [Array.getElem?_setIfInBounds_ne, hk, Ne.symm hk]

theorem arr_set_set_self {α : Type} (arr : Array α) (i : Nat) (v1 v2 : α) :
    arr_set (arr_set arr i v1) i v2 = arr_set arr i v2 := by
  unfold arr_set
  apply Array.ext_getElem?
  intro k
  by_cases hk : k = i <;> simp_all [Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self]

theorem arr_set_of_oob {α : Type} (arr : Array α) (i : Nat) (v : α) (h : ¬ i < arr.size) :
    arr_set arr i v = arr := by
  unfold arr_set
  simp only [Array.set!_eq_setIfInBounds]
  apply Array.ext_getElem?
  intro k
  rw [Array.getElem?_setIfInBounds]
  by_cases hk : i = k <;> simp_all

theorem arr_set_comm {α : Type} (arr : Array α) (i j : Nat) (v1 v2 : α) (h : i ≠ j) :
    arr_set (arr_set arr i v1) j v2 = arr_set (arr_set arr j v2) i v1 := by
  unfold arr_set
  simp only [Array.set!_eq_setIfInBounds]
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_setIfInBounds]
  by_cases hki : k = i
  · subst hki
    have hkj : ¬ j = k := by omega
    simp [hkj, Array.size_setIfInBounds]
  · by_cases hkj : k = j
    · subst hkj
      have hik : ¬ i = k := by omega
      simp [hik, Array.size_setIfInBounds]
    · have hik : ¬ i = k := fun he => hki he.symm
      have hjk : ¬ j = k := fun he => hkj he.symm
      simp [hik, hjk]

-- `decode`'s issue-mark and `writeback`'s release commute (used for the `sb`
-- field of `commutes_RL_decode_RL_writeback_given_SbInv`'s state-equality).
theorem arr_get_set_delta_comm {n : Nat}
    (arr : Array (BitVec n)) (i j : Nat) (di dj : BitVec n) :
    arr_set (arr_set arr i (arr_get arr i + di)) j
      (arr_get (arr_set arr i (arr_get arr i + di)) j + dj) =
    arr_set (arr_set arr j (arr_get arr j + dj)) i
      (arr_get (arr_set arr j (arr_get arr j + dj)) i + di) := by
  by_cases hij : i = j
  · subst hij
    rw [arr_set_set_self, arr_set_set_self]
    by_cases hbound : i < arr.size
    · rw [arr_get_arr_set_self _ _ _ hbound, arr_get_arr_set_self _ _ _ hbound]
      generalize arr_get arr i = x
      rw [BitVec.add_assoc, BitVec.add_comm di dj, ← BitVec.add_assoc]
    · rw [arr_set_of_oob _ _ _ hbound, arr_set_of_oob _ _ _ hbound]
  · rw [arr_get_arr_set_ne _ _ _ _ hij, arr_get_arr_set_ne _ _ _ _ (Ne.symm hij)]
    exact arr_set_comm _ _ _ _ _ hij

def dInstRd (dInst : t_decodedinst) : BitVec 5 := (RVUtil.getInstFields dInst.inst).rd

def dInstWrites (dInst : t_decodedinst) : t_bool :=
  bool_and (bool_and dInst.valid_rd dInst.legal)
    (bool_not (if dInstRd dInst == (0 : BitVec 5) then BTrue Unit_ else BFalse Unit_))

def sbContrib (hasElement : Bool) (dInst : t_decodedinst) (r : BitVec 5) : BitVec 2 :=
  ite_bsv (bool_and (if hasElement then BTrue Unit_ else BFalse Unit_)
      (bool_and (dInstWrites dInst) (if dInstRd dInst == r then BTrue Unit_ else BFalse Unit_)))
    (1 : BitVec 2) (0 : BitVec 2)

theorem sbContrib_zero_or_one (hasElement : Bool) (dInst : t_decodedinst) (r : BitVec 5) :
    sbContrib hasElement dInst r = 0 ∨ sbContrib hasElement dInst r = 1 := by
  unfold sbContrib ite_bsv
  split <;> simp

theorem sbContrib_sum_zero (x y : BitVec 2) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hsum : x + y = 0) : x = 0 ∧ y = 0 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;> simp_all <;> decide

def SbInv (a : ImplModule.State) : Prop :=
  a.sb.size = 32 ∧
  ∀ r : BitVec 5, arr_get a.sb r.toNat =
    sbContrib a.d2e.hasElement (M_mkFIFO.meth_first a.d2e).dInst r +
    sbContrib a.e2w.hasElement (M_mkFIFO.meth_first a.e2w).dInst r

def decodeOperandsReady (data : BitVec 32) (sb : Array (BitVec 2)) : t_bool :=
  bool_and
    (bool_or (bool_and (decodeInst data).valid_rs1
        (if arr_get sb (getInstFields data).rs1.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
             (bool_not (decodeInst data).valid_rs1))
    (bool_or (bool_and (decodeInst data).valid_rs2
        (if arr_get sb (getInstFields data).rs2.toNat == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_))
             (bool_not (decodeInst data).valid_rs2))

theorem sb_ready_iff (sb : Array (BitVec 2)) (idx : Nat) :
    (if arr_get sb idx == (0 : BitVec 2) then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ ↔ arr_get sb idx = 0 := by
  split <;> simp_all

-- If every register the operands need was ready under `sb`, it's still ready
-- under any `sb'` that agrees with `sb` on every register that was `0`
-- (writeback's release never turns a *ready* register unready).
theorem decodeOperandsReady_agree (data : BitVec 32) (sb sb' : Array (BitVec 2))
    (hagree : ∀ idx : BitVec 5, arr_get sb idx.toNat = 0 → arr_get sb' idx.toNat = 0)
    (h : decodeOperandsReady data sb = BTrue Unit_) :
    decodeOperandsReady data sb' = BTrue Unit_ := by
  unfold decodeOperandsReady at h ⊢
  simp only [bool_and_true_iff, bool_or_true_iff, sb_ready_iff] at h ⊢
  obtain ⟨hr1, hr2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hr1 with ⟨hv1, hz1⟩ | hv1
    · exact Or.inl ⟨hv1, hagree _ hz1⟩
    · exact Or.inr hv1
  · rcases hr2 with ⟨hv2, hz2⟩ | hv2
    · exact Or.inl ⟨hv2, hagree _ hz2⟩
    · exact Or.inr hv2

-- `FetchPipeInv`: in any reachable state, `f2d` empty implies `ireq`/`fromImem` are also
-- empty (there's only ever one instruction-fetch request in flight through the
-- toImem/ireq/fromImem pipe at a time, tied 1:1 to `f2d` occupancy). Not provable here
-- without `phi0`/reachability, so it stays a separate hypothesis rather than folding
-- into the unconditional `commutes_RL_fetch_RL_execute` above.
def FetchPipeInv (a : ImplModule.State) : Prop :=
  a.f2d.hasElement = false → a.ireq.hasElement = false ∧ a.fromImem.hasElement = false

theorem meth_put_depends_only_on_memory {α : Type} [Inhabited α]
    (s1 s2 : M_mkSimpleBRAM.state α) (h : s1.memory = s2.memory) (w : t_bool) (addr : BitVec 20) (d : α) :
    (M_mkSimpleBRAM.meth_put s1 w addr d).avAction_ = (M_mkSimpleBRAM.meth_put s2 w addr d).avAction_ := by
  dsimp only [M_mkSimpleBRAM.meth_put]
  rw [h]

theorem commutes_RL_fetch_RL_execute_given_FetchPipeInv {a b c : ImplModule.State}
    (hInv : FetchPipeInv a) :
  ImplModule.getRule .RL_fetch a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hcg : (M_mktop_pipelined.rule_RL_fetch a).1 = BTrue Unit_ := by rw [hc]
  have hcg_raw := hcg
  dsimp only [M_mktop_pipelined.rule_RL_fetch] at hcg
  simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff] at hcg
  have ha_f2d : a.f2d.hasElement = false := by tauto
  have ha_toImem : a.toImem.hasElement = false := by tauto
  obtain ⟨ha_ireq, ha_fromImem⟩ := hInv ha_f2d
  obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  -- fields of `c` untouched by fetch
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_dMem : c.dMem = a.dMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_dreq : c.dreq = a.dreq := by rw [← hc2]
  have hc_fromImem : c.fromImem = a.fromImem := by rw [← hc2]
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_d2e : c.d2e = a.d2e := by rw [← hc2]
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_sb : c.sb = a.sb := by rw [← hc2]
  have hc_fromDmem : c.fromDmem = a.fromDmem := by rw [← hc2]
  have hc_pc : c.pc = a.pc + 4 := by rw [← hc2]
  have hc_f2d : c.f2d = (M_mkFIFO.meth_enq a.f2d { pc := a.pc, ppc := a.pc + 4, iEp := a.ep }).avAction_ := by rw [← hc2]
  have hc_toImem : c.toImem = (M_mkFIFO.meth_enq a.toImem { byte_en := 0, addr := a.pc, data := 0 }).avAction_ := by rw [← hc2]
  -- fields of `b` untouched or determined by execute
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hb_retiredInst : b.retiredInst = a.retiredInst := by rw [← hb2]
  have hb_rf : b.rf = a.rf := by rw [← hb2]
  have hbg : (M_mktop_pipelined.rule_RL_execute a).1 = BTrue Unit_ := by rw [hb]
  have hpc_ep_combined :
      ((M_mktop_pipelined.rule_RL_execute c).2.pc = c.pc ∧ (M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep ∧
       (M_mktop_pipelined.rule_RL_execute a).2.pc = a.pc ∧ (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep) ∨
      ((M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep + 1 ∧ (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep + 1 ∧
       (M_mktop_pipelined.rule_RL_execute c).2.pc = (M_mktop_pipelined.rule_RL_execute a).2.pc) := by
    dsimp only [M_mktop_pipelined.rule_RL_execute]
    rw [hc_d2e, hc_ep]
    repeat' split
    all_goals first
      | (left; refine ⟨rfl, rfl, rfl, rfl⟩)
      | (right; refine ⟨rfl, rfl, rfl⟩)
      | (left; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [bool_to_bitvec1, bool_not])
      | (right; refine ⟨?_, ?_, ?_⟩ <;> simp_all [bool_to_bitvec1, bool_not])
      | simp_all
  have hbv1_ne_succ : ∀ x : BitVec 1, x ≠ x + 1 := by decide
  have hep_dichotomy : (b.pc = a.pc ∧ b.ep = a.ep) ∨ b.ep = a.ep + 1 := by
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_execute]
    repeat' split
    all_goals first
      | (left; constructor <;> rfl)
      | (right; rfl)
      | (left; constructor <;> simp_all [bool_to_bitvec1, bool_not])
      | (right; simp_all [bool_to_bitvec1, bool_not])
      | simp_all
  rcases hep_dichotomy with ⟨hb_pc, hb_ep⟩ | hb_ep
  · -- EASY: no misprediction, 1-step diamond
    have hce_guard : (M_mktop_pipelined.rule_RL_execute c).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_execute] at hbg ⊢
      rw [hc_d2e, hc_ep, hc_toDmem, hc_e2w]
      exact hbg
    have hbf_guard : (M_mktop_pipelined.rule_RL_fetch b).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch] at hcg_raw ⊢
      rw [hb_f2d, hb_toImem]
      exact hcg_raw
    have ha_pc : (M_mktop_pipelined.rule_RL_execute a).2.pc = a.pc := (congrArg (·.pc) hb2).trans hb_pc
    have ha_ep : (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep := (congrArg (·.ep) hb2).trans hb_ep
    have hc_ep_pass : (M_mktop_pipelined.rule_RL_execute c).2.pc = c.pc ∧
        (M_mktop_pipelined.rule_RL_execute c).2.ep = c.ep := by
      rcases hpc_ep_combined with ⟨h1, h2, _, _⟩ | ⟨_, h4, _⟩
      · exact ⟨h1, h2⟩
      · exact absurd (ha_ep.symm.trans h4) (hbv1_ne_succ a.ep)
    have hf2d_eq : (M_mktop_pipelined.rule_RL_execute c).2.f2d = (M_mktop_pipelined.rule_RL_fetch b).2.f2d := by
      have h1 : (M_mktop_pipelined.rule_RL_execute c).2.f2d = c.f2d := by
        rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.f2d =
          (M_mkFIFO.meth_enq b.f2d { pc := b.pc, ppc := b.pc + 4, iEp := b.ep }).avAction_ := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h1, h2, hb_f2d, hb_pc, hb_ep, hc_f2d]
    have htoImem_eq : (M_mktop_pipelined.rule_RL_execute c).2.toImem = (M_mktop_pipelined.rule_RL_fetch b).2.toImem := by
      have h1 : (M_mktop_pipelined.rule_RL_execute c).2.toImem = c.toImem := by
        rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.toImem =
          (M_mkFIFO.meth_enq b.toImem { byte_en := 0, addr := b.pc, data := 0 }).avAction_ := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h1, h2, hb_toImem, hb_pc, hc_toImem]
    have hpc_eq : (M_mktop_pipelined.rule_RL_execute c).2.pc = (M_mktop_pipelined.rule_RL_fetch b).2.pc := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.pc = b.pc + 4 := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [hc_ep_pass.1, h2, hb_pc, hc_pc]
    have hep_eq : (M_mktop_pipelined.rule_RL_execute c).2.ep = (M_mktop_pipelined.rule_RL_fetch b).2.ep := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.ep = b.ep := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [hc_ep_pass.2, h2, hb_ep, hc_ep]
    have hd2e_eq : (M_mktop_pipelined.rule_RL_execute c).2.d2e = (M_mktop_pipelined.rule_RL_fetch b).2.d2e := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.d2e = b.d2e := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hsb_eq : (M_mktop_pipelined.rule_RL_execute c).2.sb = (M_mktop_pipelined.rule_RL_fetch b).2.sb := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.sb = b.sb := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have he2w_eq : (M_mktop_pipelined.rule_RL_execute c).2.e2w = (M_mktop_pipelined.rule_RL_fetch b).2.e2w := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.e2w = b.e2w := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have htoDmem_eq : (M_mktop_pipelined.rule_RL_execute c).2.toDmem = (M_mktop_pipelined.rule_RL_fetch b).2.toDmem := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.toDmem = b.toDmem := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hiMem_eq : (M_mktop_pipelined.rule_RL_execute c).2.iMem = (M_mktop_pipelined.rule_RL_fetch b).2.iMem := by
      show c.iMem = b.iMem; rw [hc_iMem, hb_iMem]
    have hdMem_eq : (M_mktop_pipelined.rule_RL_execute c).2.dMem = (M_mktop_pipelined.rule_RL_fetch b).2.dMem := by
      show c.dMem = b.dMem; rw [hc_dMem, hb_dMem]
    have hireq_eq : (M_mktop_pipelined.rule_RL_execute c).2.ireq = (M_mktop_pipelined.rule_RL_fetch b).2.ireq := by
      show c.ireq = b.ireq; rw [hc_ireq, hb_ireq]
    have hdreq_eq : (M_mktop_pipelined.rule_RL_execute c).2.dreq = (M_mktop_pipelined.rule_RL_fetch b).2.dreq := by
      show c.dreq = b.dreq; rw [hc_dreq, hb_dreq]
    have hfromImem_eq : (M_mktop_pipelined.rule_RL_execute c).2.fromImem = (M_mktop_pipelined.rule_RL_fetch b).2.fromImem := by
      show c.fromImem = b.fromImem; rw [hc_fromImem, hb_fromImem]
    have hfromDmem_eq : (M_mktop_pipelined.rule_RL_execute c).2.fromDmem = (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem := by
      have h2 : (M_mktop_pipelined.rule_RL_fetch b).2.fromDmem = b.fromDmem := by
        dsimp only [M_mktop_pipelined.rule_RL_fetch]
      rw [h2, ← hc2]
      dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]
      rw [← hb2]
    have hretiredInst_eq : (M_mktop_pipelined.rule_RL_execute c).2.retiredInst = (M_mktop_pipelined.rule_RL_fetch b).2.retiredInst := by
      show c.retiredInst = b.retiredInst; rw [hc_retiredInst, hb_retiredInst]
    have hrf_eq : (M_mktop_pipelined.rule_RL_execute c).2.rf = (M_mktop_pipelined.rule_RL_fetch b).2.rf := by
      show c.rf = b.rf; rw [hc_rf, hb_rf]
    have final_eq : (M_mktop_pipelined.rule_RL_execute c).2 = (M_mktop_pipelined.rule_RL_fetch b).2 :=
      (M_mktop_pipelined.state.mk.injEq ..).mpr
        ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
         hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
    refine ⟨(M_mktop_pipelined.rule_RL_execute c).2,
      Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩, Relation.ReflTransGen.single ⟨.RL_fetch, ?_⟩⟩
    · exact Prod.ext hce_guard rfl
    · exact Prod.ext hbf_guard final_eq.symm
  · -- HARD: misprediction, multi-step diamond using FetchPipeInv
    obtain ⟨ha_ireq, ha_fromImem⟩ := hInv ha_f2d
    have hc1_guard : (M_mktop_pipelined.rule_RL_execute c).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_execute] at hbg ⊢
      rw [hc_d2e, hc_ep, hc_toDmem, hc_e2w]
      exact hbg
    have ha_ep' : (M_mktop_pipelined.rule_RL_execute a).2.ep = a.ep + 1 := (congrArg (·.ep) hb2).trans hb_ep
    have hc1_ep : (M_mktop_pipelined.rule_RL_execute c).2.ep = b.ep := by
      rcases hpc_ep_combined with ⟨_, _, _, h4⟩ | ⟨h1, _, _⟩
      · exact absurd (h4.symm.trans ha_ep') (hbv1_ne_succ a.ep)
      · rw [hc_ep] at h1; exact h1.trans hb_ep.symm
    have hc1_pc : (M_mktop_pipelined.rule_RL_execute c).2.pc = b.pc := by
      rcases hpc_ep_combined with ⟨_, _, _, h4⟩ | ⟨_, _, h3⟩
      · exact absurd (h4.symm.trans ha_ep') (hbv1_ne_succ a.ep)
      · exact h3.trans (congrArg (·.pc) hb2)
    have hc1_d2e : (M_mktop_pipelined.rule_RL_execute c).2.d2e = b.d2e := by
      rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]; rw [← hb2]
    have hc1_sb : (M_mktop_pipelined.rule_RL_execute c).2.sb = b.sb := by
      rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]; rw [← hb2]
    have hc1_e2w : (M_mktop_pipelined.rule_RL_execute c).2.e2w = b.e2w := by
      rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]; rw [← hb2]
    have hc1_toDmem : (M_mktop_pipelined.rule_RL_execute c).2.toDmem = b.toDmem := by
      rw [← hc2]; dsimp only [M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_fetch]; rw [← hb2]
    -- fields untouched by execute: c1 = c on these
    have hc1_f2d : (M_mktop_pipelined.rule_RL_execute c).2.f2d = c.f2d := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_toImem : (M_mktop_pipelined.rule_RL_execute c).2.toImem = c.toImem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_ireq : (M_mktop_pipelined.rule_RL_execute c).2.ireq = c.ireq := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_fromImem : (M_mktop_pipelined.rule_RL_execute c).2.fromImem = c.fromImem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_iMem : (M_mktop_pipelined.rule_RL_execute c).2.iMem = c.iMem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_dMem : (M_mktop_pipelined.rule_RL_execute c).2.dMem = c.dMem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_dreq : (M_mktop_pipelined.rule_RL_execute c).2.dreq = c.dreq := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_retiredInst : (M_mktop_pipelined.rule_RL_execute c).2.retiredInst = c.retiredInst := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_rf : (M_mktop_pipelined.rule_RL_execute c).2.rf = c.rf := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hc1_fromDmem : (M_mktop_pipelined.rule_RL_execute c).2.fromDmem = c.fromDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    have hb_fromDmem : b.fromDmem = a.fromDmem := by rw [← hb2]
    have hc1_eq : (M_mktop_pipelined.rule_RL_execute c).2 =
        { b with f2d := c.f2d, toImem := c.toImem } := by
      apply (M_mktop_pipelined.state.mk.injEq ..).mpr
      refine ⟨?_, ?_, ?_, ?_, hc1_toImem, ?_, hc1_toDmem, ?_, hc1_f2d, hc1_d2e, hc1_e2w, ?_, hc1_pc, hc1_ep, ?_, hc1_sb⟩
      · exact hc_iMem.trans hb_iMem.symm
      · exact hc_dMem.trans hb_dMem.symm
      · exact hc_ireq.trans hb_ireq.symm
      · exact hc_dreq.trans hb_dreq.symm
      · exact hc_fromImem.trans hb_fromImem.symm
      · exact hc_fromDmem.trans hb_fromDmem.symm
      · exact hc_retiredInst.trans hb_retiredInst.symm
      · exact hc_rf.trans hb_rf.symm
    set c1 : ImplModule.State := { b with f2d := c.f2d, toImem := c.toImem } with hc1_def
    -- c1.toImem is occupied (fetch's stale request), c1.ireq is empty (FetchPipeInv)
    have hc1_toImem_occ : c1.toImem.hasElement = true := by
      rw [hc1_def]; dsimp only; rw [hc_toImem]; dsimp only [M_mkFIFO.meth_enq]
    have hc1_ireq_empty : c1.ireq.hasElement = false := by
      rw [hc1_def]; dsimp only; rw [hb_ireq, ha_ireq]
    have hc1_fromImem_empty : c1.fromImem.hasElement = false := by
      rw [hc1_def]; dsimp only; rw [hb_fromImem, ha_fromImem]
    have hc2_guard : (M_mktop_pipelined.rule_RL_requestI c1).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_requestI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff]
      simp only [M_mkSimpleBRAM.meth_RDY_put]
      tauto
    set c2 : ImplModule.State := (M_mktop_pipelined.rule_RL_requestI c1).2 with hc2_def
    have hc2_toImem : c2.toImem.hasElement = false := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_deq]
    have hc2_ireq_occ : c2.ireq.hasElement = true := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_enq]
    have hc2_ireq_first : c2.ireq = (M_mkFIFO.meth_enq c1.ireq (M_mkFIFO.meth_first c1.toImem)).avAction_ := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_fromImem : c2.fromImem.hasElement = false := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]; exact hc1_fromImem_empty
    have hc2_f2d : c2.f2d = c1.f2d := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_d2e : c2.d2e = c1.d2e := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_sb : c2.sb = c1.sb := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_e2w : c2.e2w = c1.e2w := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_toDmem : c2.toDmem = c1.toDmem := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_pc : c2.pc = c1.pc := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_ep : c2.ep = c1.ep := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_rf : c2.rf = c1.rf := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_retiredInst : c2.retiredInst = c1.retiredInst := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_dMem : c2.dMem = c1.dMem := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_dreq : c2.dreq = c1.dreq := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc2_fromDmem : c2.fromDmem = c1.fromDmem := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc3_guard : (M_mktop_pipelined.rule_RL_responseI c2).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
        M_mkSimpleBRAM.meth_RDY_read]
      tauto
    set c3 : ImplModule.State := (M_mktop_pipelined.rule_RL_responseI c2).2 with hc3_def
    have hc3_ireq : c3.ireq.hasElement = false := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_deq]
    have hc3_fromImem_occ : c3.fromImem.hasElement = true := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_enq]
    have hc3_iMem : c3.iMem = c2.iMem := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkSimpleBRAM.meth_read]
    have hc3_f2d : c3.f2d = c2.f2d := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_d2e : c3.d2e = c2.d2e := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_sb : c3.sb = c2.sb := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_e2w : c3.e2w = c2.e2w := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_toDmem : c3.toDmem = c2.toDmem := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_pc : c3.pc = c2.pc := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_ep : c3.ep = c2.ep := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_rf : c3.rf = c2.rf := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_retiredInst : c3.retiredInst = c2.retiredInst := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_dMem : c3.dMem = c2.dMem := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_dreq : c3.dreq = c2.dreq := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_fromDmem : c3.fromDmem = c2.fromDmem := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc3_toImem : c3.toImem = c2.toImem := by
      rw [hc3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    -- c3.f2d = c.f2d (stale, tagged a.ep), c3.ep = a.ep+1: squash condition holds
    have hc3_f2d_eq : c3.f2d = c.f2d := by rw [hc3_f2d, hc2_f2d]
    have hc3_ep_eq : c3.ep = a.ep + 1 := by rw [hc3_ep, hc2_ep]; show c1.ep = a.ep + 1; rw [hc1_def]; exact hb_ep
    have hbv1_ne_succ_beq : ∀ x : BitVec 1, ¬ ((x == x + 1) = true) := by decide
    have hc3_squash : (if ((M_mkFIFO.meth_first c3.f2d).iEp == c3.ep) then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
      rw [hc3_f2d_eq, hc3_ep_eq, hc_f2d]
      dsimp only [M_mkFIFO.meth_first, M_mkFIFO.meth_enq]
      simp [hbv1_ne_succ_beq a.ep]
    have hc3_f2d_occ : c3.f2d.hasElement = true := by
      rw [hc3_f2d_eq, hc_f2d]; dsimp only [M_mkFIFO.meth_enq]
    have hc4_guard : (M_mktop_pipelined.rule_RL_decode c3).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_decode]
      rw [hc3_squash]
      simp only [bitvec1_bit_and', bitvec1_bit_or', bitvec1_bit_not', bitvec1_roundtrip,
        bool_and_true_iff, bool_or_true_iff, bool_not, reduceCtorEq,
        mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff]
      tauto
    set c4 : ImplModule.State := (M_mktop_pipelined.rule_RL_decode c3).2 with hc4_def
    have hc4_f2d : c4.f2d.hasElement = false := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode, M_mkFIFO.meth_deq]
    have hc4_fromImem : c4.fromImem.hasElement = false := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode, M_mkFIFO.meth_deq]
    have hc4_d2e : c4.d2e = c3.d2e := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]; rw [hc3_squash]
    have hc4_sb : c4.sb = c3.sb := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]; rw [hc3_squash]
    have hc4_toImem : c4.toImem = c3.toImem := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_ireq : c4.ireq = c3.ireq := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_iMem : c4.iMem = c3.iMem := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_e2w : c4.e2w = c3.e2w := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_toDmem : c4.toDmem = c3.toDmem := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_pc : c4.pc = c3.pc := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_ep : c4.ep = c3.ep := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_rf : c4.rf = c3.rf := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_retiredInst : c4.retiredInst = c3.retiredInst := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_dMem : c4.dMem = c3.dMem := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_dreq : c4.dreq = c3.dreq := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_fromDmem : c4.fromDmem = c3.fromDmem := by
      rw [hc4_def]; dsimp only [M_mktop_pipelined.rule_RL_decode]
    have hc4_toImem_empty : c4.toImem.hasElement = false := by
      rw [hc4_toImem, hc3_toImem, hc2_toImem]
    have hc5_guard : (M_mktop_pipelined.rule_RL_fetch c4).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff]
      tauto
    set c5 : ImplModule.State := (M_mktop_pipelined.rule_RL_fetch c4).2 with hc5_def
    have hc5_pc : c5.pc = c4.pc + 4 := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_f2d : c5.f2d = (M_mkFIFO.meth_enq c4.f2d { pc := c4.pc, ppc := c4.pc + 4, iEp := c4.ep }).avAction_ := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_toImem : c5.toImem = (M_mkFIFO.meth_enq c4.toImem { byte_en := 0, addr := c4.pc, data := 0 }).avAction_ := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_toImem_occ : c5.toImem.hasElement = true := by
      rw [hc5_toImem]; dsimp only [M_mkFIFO.meth_enq]
    have hc5_ireq : c5.ireq = c4.ireq := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_fromImem : c5.fromImem = c4.fromImem := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_iMem : c5.iMem = c4.iMem := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_d2e : c5.d2e = c4.d2e := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_sb : c5.sb = c4.sb := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_e2w : c5.e2w = c4.e2w := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_toDmem : c5.toDmem = c4.toDmem := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_ep : c5.ep = c4.ep := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_rf : c5.rf = c4.rf := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_retiredInst : c5.retiredInst = c4.retiredInst := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_dMem : c5.dMem = c4.dMem := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_dreq : c5.dreq = c4.dreq := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_fromDmem : c5.fromDmem = c4.fromDmem := by
      rw [hc5_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hc5_ireq_empty : c5.ireq.hasElement = false := by
      rw [hc5_ireq, hc4_ireq, hc3_ireq]
    have hc5_fromImem_empty : c5.fromImem.hasElement = false := by
      rw [hc5_fromImem, hc4_fromImem]
    have hc6_guard : (M_mktop_pipelined.rule_RL_requestI c5).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_requestI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
        M_mkSimpleBRAM.meth_RDY_put]
      tauto
    set c6 : ImplModule.State := (M_mktop_pipelined.rule_RL_requestI c5).2 with hc6_def
    have hc6_toImem : c6.toImem.hasElement = false := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_deq]
    have hc6_ireq_occ : c6.ireq.hasElement = true := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_enq]
    have hc6_ireq_first : c6.ireq = (M_mkFIFO.meth_enq c5.ireq (M_mkFIFO.meth_first c5.toImem)).avAction_ := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_fromImem : c6.fromImem.hasElement = false := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]; exact hc5_fromImem_empty
    have hc6_f2d : c6.f2d = c5.f2d := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_d2e : c6.d2e = c5.d2e := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_sb : c6.sb = c5.sb := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_e2w : c6.e2w = c5.e2w := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_toDmem : c6.toDmem = c5.toDmem := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_pc : c6.pc = c5.pc := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_ep : c6.ep = c5.ep := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_rf : c6.rf = c5.rf := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_retiredInst : c6.retiredInst = c5.retiredInst := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_dMem : c6.dMem = c5.dMem := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_dreq : c6.dreq = c5.dreq := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc6_fromDmem : c6.fromDmem = c5.fromDmem := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc7_guard : (M_mktop_pipelined.rule_RL_responseI c6).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
        M_mkSimpleBRAM.meth_RDY_read]
      tauto
    set c7 : ImplModule.State := (M_mktop_pipelined.rule_RL_responseI c6).2 with hc7_def
    have hc7_ireq : c7.ireq.hasElement = false := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_deq]
    have hc7_fromImem_occ : c7.fromImem.hasElement = true := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_enq]
    have hc7_fromImem_val : c7.fromImem = (M_mkFIFO.meth_enq c6.fromImem
        { byte_en := (M_mkFIFO.meth_first c6.ireq).byte_en, addr := (M_mkFIFO.meth_first c6.ireq).addr,
          data := (M_mkSimpleBRAM.meth_read c6.iMem).avValue_ }).avAction_ := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, ActionValue]
    have hc7_iMem : c7.iMem = c6.iMem := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkSimpleBRAM.meth_read]
    have hc7_f2d : c7.f2d = c6.f2d := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_d2e : c7.d2e = c6.d2e := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_sb : c7.sb = c6.sb := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_e2w : c7.e2w = c6.e2w := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_toDmem : c7.toDmem = c6.toDmem := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_pc : c7.pc = c6.pc := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_ep : c7.ep = c6.ep := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_rf : c7.rf = c6.rf := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_retiredInst : c7.retiredInst = c6.retiredInst := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_dMem : c7.dMem = c6.dMem := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_dreq : c7.dreq = c6.dreq := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_fromDmem : c7.fromDmem = c6.fromDmem := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hc7_toImem : c7.toImem = c6.toImem := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    -- b-side: fetch, requestI, responseI (3 steps)
    have hb1_guard : (M_mktop_pipelined.rule_RL_fetch b).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_fetch]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff]
      rw [hb_f2d, hb_toImem]; tauto
    set b1 : ImplModule.State := (M_mktop_pipelined.rule_RL_fetch b).2 with hb1_def
    have hb1_pc : b1.pc = b.pc + 4 := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_f2d : b1.f2d = (M_mkFIFO.meth_enq b.f2d { pc := b.pc, ppc := b.pc + 4, iEp := b.ep }).avAction_ := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_toImem : b1.toImem = (M_mkFIFO.meth_enq b.toImem { byte_en := 0, addr := b.pc, data := 0 }).avAction_ := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_toImem_occ : b1.toImem.hasElement = true := by
      rw [hb1_toImem]; dsimp only [M_mkFIFO.meth_enq]
    have hb1_ireq_empty : b1.ireq.hasElement = false := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]; rw [hb_ireq, ha_ireq]
    have hb1_fromImem : b1.fromImem = b.fromImem := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_ireq : b1.ireq = b.ireq := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_iMem : b1.iMem = b.iMem := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_d2e : b1.d2e = b.d2e := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_sb : b1.sb = b.sb := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_e2w : b1.e2w = b.e2w := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_toDmem : b1.toDmem = b.toDmem := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_ep : b1.ep = b.ep := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_rf : b1.rf = b.rf := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_retiredInst : b1.retiredInst = b.retiredInst := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_dMem : b1.dMem = b.dMem := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_dreq : b1.dreq = b.dreq := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb1_fromDmem : b1.fromDmem = b.fromDmem := by
      rw [hb1_def]; dsimp only [M_mktop_pipelined.rule_RL_fetch]
    have hb2_guard : (M_mktop_pipelined.rule_RL_requestI b1).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_requestI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
        M_mkSimpleBRAM.meth_RDY_put]
      tauto
    set b2 : ImplModule.State := (M_mktop_pipelined.rule_RL_requestI b1).2 with hb2_def
    have hb2_toImem : b2.toImem.hasElement = false := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_deq]
    have hb2_ireq_occ : b2.ireq.hasElement = true := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkFIFO.meth_enq]
    have hb2_ireq_first : b2.ireq = (M_mkFIFO.meth_enq b1.ireq (M_mkFIFO.meth_first b1.toImem)).avAction_ := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_fromImem : b2.fromImem = b1.fromImem := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_f2d : b2.f2d = b1.f2d := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_d2e : b2.d2e = b1.d2e := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_sb : b2.sb = b1.sb := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_e2w : b2.e2w = b1.e2w := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_toDmem : b2.toDmem = b1.toDmem := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_pc : b2.pc = b1.pc := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_ep : b2.ep = b1.ep := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_rf : b2.rf = b1.rf := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_retiredInst : b2.retiredInst = b1.retiredInst := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_dMem : b2.dMem = b1.dMem := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_dreq : b2.dreq = b1.dreq := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_fromDmem : b2.fromDmem = b1.fromDmem := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb3_guard : (M_mktop_pipelined.rule_RL_responseI b2).1 = BTrue Unit_ := by
      dsimp only [M_mktop_pipelined.rule_RL_responseI]
      simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff,
        M_mkSimpleBRAM.meth_RDY_read]
      tauto
    set b3 : ImplModule.State := (M_mktop_pipelined.rule_RL_responseI b2).2 with hb3_def
    have hb3_ireq : b3.ireq.hasElement = false := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_deq]
    have hb3_fromImem_val : b3.fromImem = (M_mkFIFO.meth_enq b2.fromImem
        { byte_en := (M_mkFIFO.meth_first b2.ireq).byte_en, addr := (M_mkFIFO.meth_first b2.ireq).addr,
          data := (M_mkSimpleBRAM.meth_read b2.iMem).avValue_ }).avAction_ := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, ActionValue]
    have hb3_iMem : b3.iMem = b2.iMem := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkSimpleBRAM.meth_read]
    have hb3_f2d : b3.f2d = b2.f2d := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_d2e : b3.d2e = b2.d2e := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_sb : b3.sb = b2.sb := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_e2w : b3.e2w = b2.e2w := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_toDmem : b3.toDmem = b2.toDmem := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_pc : b3.pc = b2.pc := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_ep : b3.ep = b2.ep := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_rf : b3.rf = b2.rf := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_retiredInst : b3.retiredInst = b2.retiredInst := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_dMem : b3.dMem = b2.dMem := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_dreq : b3.dreq = b2.dreq := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_fromDmem : b3.fromDmem = b2.fromDmem := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    have hb3_toImem : b3.toImem = b2.toImem := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI]
    -- KEY: c4.pc = b.pc (both are the post-redirect nextPC), so the second requestI's
    -- fetch request on the c-side and the first requestI's request on the b-side target
    -- the SAME address.
    have hc4_pc_eq_b_pc : c4.pc = b.pc := by
      rw [hc4_pc, hc3_pc, hc2_pc]
    have hc5_toImem_first : (M_mkFIFO.meth_first c5.toImem) = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := by
      rw [hc5_toImem, hc4_pc_eq_b_pc]; dsimp only [M_mkFIFO.meth_enq, M_mkFIFO.meth_first]
    have hb1_toImem_first : (M_mkFIFO.meth_first b1.toImem) = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := by
      rw [hb1_toImem]; dsimp only [M_mkFIFO.meth_enq, M_mkFIFO.meth_first]
    -- iMem's `.memory` component never actually changes (every instruction fetch is a
    -- read: byte_en = 0), so it stays at `a.iMem.memory` throughout both paths.
    have hc1_iMem_eq : c1.iMem = a.iMem := hb_iMem
    have hc1_toImem_first : (M_mkFIFO.meth_first c1.toImem) = { byte_en := (0:BitVec 4), addr := a.pc, data := (0:BitVec 32) } := by
      show (M_mkFIFO.meth_first c.toImem) = _
      rw [hc_toImem]; dsimp only [M_mkFIFO.meth_enq, M_mkFIFO.meth_first]
    have hc2_iMem_memory : c2.iMem.memory = a.iMem.memory := by
      rw [hc2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI, M_mkSimpleBRAM.meth_put]
      rw [hc1_iMem_eq, hc1_toImem_first]
      simp [bool_not]
    have hc5_iMem_memory : c5.iMem.memory = a.iMem.memory := by
      rw [hc5_iMem, hc4_iMem, hc3_iMem, hc2_iMem_memory]
    have hb1_iMem_eq : b1.iMem = a.iMem := by rw [hb1_iMem, hb_iMem]
    have hc6_iMem_eq_b2_iMem : c6.iMem = b2.iMem := by
      rw [hc6_def, hb2_def]
      dsimp only [M_mktop_pipelined.rule_RL_requestI]
      rw [hc5_toImem_first, hb1_toImem_first]
      exact meth_put_depends_only_on_memory c5.iMem b1.iMem (by rw [hc5_iMem_memory, hb1_iMem_eq]) _ _ _
    have hc7_iMem_eq_b3_iMem : c7.iMem = b3.iMem := by
      rw [hc7_iMem, hb3_iMem, hc6_iMem_eq_b2_iMem]
    -- toImem: both end up empty, with the same stale (b.pc-tagged) element
    have hc6_toImem_full : c6.toImem = (M_mkFIFO.meth_deq c5.toImem).avAction_ := by
      rw [hc6_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hb2_toImem_full : b2.toImem = (M_mkFIFO.meth_deq b1.toImem).avAction_ := by
      rw [hb2_def]; dsimp only [M_mktop_pipelined.rule_RL_requestI]
    have hc5_toImem_elt : c5.toImem.element = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := hc5_toImem_first
    have hb1_toImem_elt : b1.toImem.element = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := hb1_toImem_first
    have hc7_toImem_full : c7.toImem = { hasElement := false, element := { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } } := by
      rw [hc7_toImem, hc6_toImem_full]
      dsimp only [M_mkFIFO.meth_deq]
      rw [hc5_toImem_elt]
    have hb3_toImem_full : b3.toImem = { hasElement := false, element := { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } } := by
      rw [hb3_toImem, hb2_toImem_full]
      dsimp only [M_mkFIFO.meth_deq]
      rw [hb1_toImem_elt]
    have hc7_toImem_eq_b3 : c7.toImem = b3.toImem := by rw [hc7_toImem_full, hb3_toImem_full]
    -- ireq: both end up empty, with the same stale (b.pc-tagged) element
    have hc6_ireq_elt : c6.ireq.element = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := by
      rw [hc6_ireq_first]; dsimp only [M_mkFIFO.meth_enq]; rw [hc5_toImem_first]
    have hb2_ireq_elt : b2.ireq.element = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := by
      rw [hb2_ireq_first]; dsimp only [M_mkFIFO.meth_enq]; rw [hb1_toImem_first]
    have hc7_ireq_full : c7.ireq = { hasElement := false, element := { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } } := by
      rw [hc7_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_deq]
      rw [hc6_ireq_elt]
    have hb3_ireq_full : b3.ireq = { hasElement := false, element := { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } } := by
      rw [hb3_def]; dsimp only [M_mktop_pipelined.rule_RL_responseI, M_mkFIFO.meth_deq]
      rw [hb2_ireq_elt]
    have hc7_ireq_eq_b3 : c7.ireq = b3.ireq := by rw [hc7_ireq_full, hb3_ireq_full]
    -- ep and pc chains: c4.ep = b.ep, c4.pc = b.pc (already have), c7/c5's pc,ep chase down to b.pc/b.ep
    have hc4_ep_eq_b_ep : c4.ep = b.ep := by
      rw [hc4_ep, hc3_ep, hc2_ep]
    have hc7_f2d_eq_b3 : c7.f2d = b3.f2d := by
      rw [hc7_f2d, hc6_f2d, hc5_f2d, hb3_f2d, hb2_f2d, hb1_f2d, hc4_pc_eq_b_pc, hc4_ep_eq_b_ep]
      dsimp only [M_mkFIFO.meth_enq]
    have hc6_ireq_first' : (M_mkFIFO.meth_first c6.ireq) = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := hc6_ireq_elt
    have hb2_ireq_first' : (M_mkFIFO.meth_first b2.ireq) = { byte_en := (0:BitVec 4), addr := b.pc, data := (0:BitVec 32) } := hb2_ireq_elt
    have hc7_fromImem_eq_b3 : c7.fromImem = b3.fromImem := by
      rw [hc7_fromImem_val, hb3_fromImem_val, hc6_ireq_first', hb2_ireq_first', hc6_iMem_eq_b2_iMem]
      dsimp only [M_mkFIFO.meth_enq]
    -- fields carried straight through from b (c1's construction leaves them = b's)
    have hc7_d2e_eq_b3 : c7.d2e = b3.d2e := by
      rw [hc7_d2e, hc6_d2e, hc5_d2e, hc4_d2e, hc3_d2e, hc2_d2e, hb3_d2e, hb2_d2e, hb1_d2e]
    have hc7_sb_eq_b3 : c7.sb = b3.sb := by
      rw [hc7_sb, hc6_sb, hc5_sb, hc4_sb, hc3_sb, hc2_sb, hb3_sb, hb2_sb, hb1_sb]
    have hc7_e2w_eq_b3 : c7.e2w = b3.e2w := by
      rw [hc7_e2w, hc6_e2w, hc5_e2w, hc4_e2w, hc3_e2w, hc2_e2w, hb3_e2w, hb2_e2w, hb1_e2w]
    have hc7_toDmem_eq_b3 : c7.toDmem = b3.toDmem := by
      rw [hc7_toDmem, hc6_toDmem, hc5_toDmem, hc4_toDmem, hc3_toDmem, hc2_toDmem, hb3_toDmem, hb2_toDmem, hb1_toDmem]
    have hc7_pc_eq_b3 : c7.pc = b3.pc := by
      rw [hc7_pc, hc6_pc, hc5_pc, hb3_pc, hb2_pc, hb1_pc, hc4_pc_eq_b_pc]
    have hc7_ep_eq_b3 : c7.ep = b3.ep := by
      rw [hc7_ep, hc6_ep, hc5_ep, hc4_ep, hc3_ep, hc2_ep, hb3_ep, hb2_ep, hb1_ep]
    have hc7_rf_eq_b3 : c7.rf = b3.rf := by
      rw [hc7_rf, hc6_rf, hc5_rf, hc4_rf, hc3_rf, hc2_rf, hb3_rf, hb2_rf, hb1_rf]
    have hc7_retiredInst_eq_b3 : c7.retiredInst = b3.retiredInst := by
      rw [hc7_retiredInst, hc6_retiredInst, hc5_retiredInst, hc4_retiredInst, hc3_retiredInst, hc2_retiredInst,
        hb3_retiredInst, hb2_retiredInst, hb1_retiredInst]
    have hc7_dMem_eq_b3 : c7.dMem = b3.dMem := by
      rw [hc7_dMem, hc6_dMem, hc5_dMem, hc4_dMem, hc3_dMem, hc2_dMem, hb3_dMem, hb2_dMem, hb1_dMem]
    have hc7_dreq_eq_b3 : c7.dreq = b3.dreq := by
      rw [hc7_dreq, hc6_dreq, hc5_dreq, hc4_dreq, hc3_dreq, hc2_dreq, hb3_dreq, hb2_dreq, hb1_dreq]
    have hc7_fromDmem_eq_b3 : c7.fromDmem = b3.fromDmem := by
      rw [hc7_fromDmem, hc6_fromDmem, hc5_fromDmem, hc4_fromDmem, hc3_fromDmem, hc2_fromDmem,
        hb3_fromDmem, hb2_fromDmem, hb1_fromDmem]
    have final_eq : c7 = b3 :=
      (M_mktop_pipelined.state.mk.injEq ..).mpr
        ⟨hc7_iMem_eq_b3_iMem, hc7_dMem_eq_b3, hc7_ireq_eq_b3, hc7_dreq_eq_b3, hc7_toImem_eq_b3,
         hc7_fromImem_eq_b3, hc7_toDmem_eq_b3, hc7_fromDmem_eq_b3, hc7_f2d_eq_b3, hc7_d2e_eq_b3,
         hc7_e2w_eq_b3, hc7_retiredInst_eq_b3, hc7_pc_eq_b3, hc7_ep_eq_b3, hc7_rf_eq_b3, hc7_sb_eq_b3⟩
    have step1 : ImplModule.getARule c c1 := ⟨.RL_execute, Prod.ext hc1_guard (hc1_eq.trans hc1_def.symm)⟩
    have step2 : ImplModule.getARule c1 c2 := ⟨.RL_requestI, Prod.ext hc2_guard rfl⟩
    have step3 : ImplModule.getARule c2 c3 := ⟨.RL_responseI, Prod.ext hc3_guard rfl⟩
    have step4 : ImplModule.getARule c3 c4 := ⟨.RL_decode, Prod.ext hc4_guard rfl⟩
    have step5 : ImplModule.getARule c4 c5 := ⟨.RL_fetch, Prod.ext hc5_guard rfl⟩
    have step6 : ImplModule.getARule c5 c6 := ⟨.RL_requestI, Prod.ext hc6_guard rfl⟩
    have step7 : ImplModule.getARule c6 c7 := ⟨.RL_responseI, Prod.ext hc7_guard rfl⟩
    have stepb1 : ImplModule.getARule b b1 := ⟨.RL_fetch, Prod.ext hb1_guard rfl⟩
    have stepb2 : ImplModule.getARule b1 b2 := ⟨.RL_requestI, Prod.ext hb2_guard rfl⟩
    have stepb3 : ImplModule.getARule b2 b3 := ⟨.RL_responseI, Prod.ext hb3_guard rfl⟩
    refine ⟨c7, ?_, ?_⟩
    · exact .tail (.tail (.tail (.tail (.tail (.tail (.single step1) step2) step3) step4) step5) step6) step7
    · rw [final_eq]
      exact .tail (.tail (.single stepb1) stepb2) stepb3



-- Given `SbInv a`, this pair fully commutes -- both guards firing in the
-- swapped order (`hc_wb_guard`/`hb_decode_guard`) via the scoreboard-
-- readiness-survives-release argument (`decodeOperandsReady_agree`), and the
-- final state equality (`final_eq`): the `d2e` entry's `rv1`/`rv2` fields
-- agree (same aliasing argument, threaded through to a value rather than a
-- guard) and the `sb` update commutes (`decode`'s issue-mark vs `writeback`'s
-- release, via `arr_get_set_delta_comm`).
theorem commutes_RL_decode_RL_writeback_given_SbInv {a b c : ImplModule.State} (hInv : SbInv a) :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbg : (M_mktop_pipelined.rule_RL_writeback a).1 = BTrue Unit_ := by rw [hb]
  dsimp only [M_mktop_pipelined.rule_RL_writeback] at hbg
  simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hbg
  have he2w : a.e2w.hasElement = true := by
    have := hbg.2.1
    simpa [mkFIFO_RDY_deq_iff] using this
  have hretired : a.retiredInst = Invalid Unit_ := by
    rcases h : a.retiredInst with u | u
    · cases u; rfl
    · exfalso; rw [h] at hbg; exact absurd hbg.1 (by simp)
  obtain ⟨_, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  obtain ⟨_, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hsize, hpt⟩ := hInv
  -- shared facts, independent of decode's squash status
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_fromDmem : c.fromDmem = a.fromDmem := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hb_d2e : b.d2e = a.d2e := by rw [← hb2]
  have hb_ep : b.ep = a.ep := by rw [← hb2]
  have hc_wb_guard : (M_mktop_pipelined.rule_RL_writeback c).1 = BTrue Unit_ := by
    have hbg_orig : (M_mktop_pipelined.rule_RL_writeback a).1 = BTrue Unit_ := by rw [hb]
    dsimp only [M_mktop_pipelined.rule_RL_writeback] at hbg_orig ⊢
    rw [hc_e2w, hc_fromDmem, hc_retiredInst]
    exact hbg_orig
  have hRwLt : (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat < a.sb.size := by
    rw [hsize]; have := (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).isLt; omega
  have hb_sb : b.sb = arr_set a.sb (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat
      (arr_get a.sb (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat +
        ite_bsv (dInstWrites (M_mkFIFO.meth_first a.e2w).dInst) (3 : BitVec 2) (0 : BitVec 2)) := by
    have hdisc : (bitvec1_to_bool (bit_and
          (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.valid_rd)
            (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.legal))
          (bool_to_bitvec1 (bool_not (if ((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd == (0:BitVec 5)) = true then BTrue Unit_ else BFalse Unit_)))))
        = dInstWrites (M_mkFIFO.meth_first a.e2w).dInst := by
      unfold dInstWrites dInstRd
      simp only [bitvec1_bit_and', bitvec1_bit_not', bitvec1_roundtrip]
    rw [← hb2]
    dsimp only
    unfold ite_bsv
    rw [hdisc]
    unfold dInstRd
    cases dInstWrites (M_mkFIFO.meth_first a.e2w).dInst <;> rfl
  have hsb_agree0 : ∀ idx : BitVec 5, arr_get a.sb idx.toNat = 0 → arr_get b.sb idx.toNat = 0 := by
    intro idx h0
    by_cases heq : idx = dInstRd (M_mkFIFO.meth_first a.e2w).dInst
    · rw [heq] at h0 ⊢
      have hpteq := hpt (dInstRd (M_mkFIFO.meth_first a.e2w).dInst)
      rw [h0] at hpteq
      have hx01 := sbContrib_zero_or_one a.d2e.hasElement (M_mkFIFO.meth_first a.d2e).dInst (dInstRd (M_mkFIFO.meth_first a.e2w).dInst)
      have hy01 := sbContrib_zero_or_one a.e2w.hasElement (M_mkFIFO.meth_first a.e2w).dInst (dInstRd (M_mkFIFO.meth_first a.e2w).dInst)
      have hxy0 := sbContrib_sum_zero _ _ hx01 hy01 hpteq.symm
      have he2w_contrib_zero : ite_bsv (dInstWrites (M_mkFIFO.meth_first a.e2w).dInst) (1 : BitVec 2) (0 : BitVec 2) = 0 := by
        have := hxy0.2
        unfold sbContrib at this
        rw [he2w] at this
        simpa using this
      rw [hb_sb, arr_get_arr_set_self _ _ _ hRwLt]
      cases hdw : dInstWrites (M_mkFIFO.meth_first a.e2w).dInst with
      | BTrue u => cases u; rw [hdw] at he2w_contrib_zero; simp [ite_bsv] at he2w_contrib_zero
      | BFalse u => cases u; rw [h0]; simp [ite_bsv]
    · rw [hb_sb, arr_get_arr_set_ne]
      · exact h0
      · intro hcon; exact heq (BitVec.eq_of_toNat_eq hcon.symm)
  -- decode's operand-readiness guard is now GATED behind the epoch match (only
  -- required when NOT squashed): `bool_or (bool_and EPMATCH OPREADY) (bool_not EPMATCH)`.
  -- We still need to show this gated fact survives onto `b`, splitting on whether `a`'s
  -- entry is squashed or not (the epoch-match discriminant is identical for `a`/`b`,
  -- since `b.f2d = a.f2d` and `b.ep = a.ep`).
  have hcg : (M_mktop_pipelined.rule_RL_decode a).1 = BTrue Unit_ := by rw [hc]
  dsimp only [M_mktop_pipelined.rule_RL_decode] at hcg
  have hcg' := hcg
  simp only [bool_and_true_iff] at hcg'
  have hopReady_gated := hcg'.1
  simp only [bitvec1_bit_and', bitvec1_bit_or', bitvec1_bit_not', bitvec1_roundtrip] at hopReady_gated
  have hRest := hcg'.2
  have hb_decode_guard : (M_mktop_pipelined.rule_RL_decode b).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_decode]
    simp only [bool_and_true_iff]
    refine ⟨?_, ?_⟩
    · simp only [bitvec1_bit_and', bitvec1_bit_or', bitvec1_bit_not', bitvec1_roundtrip]
      rw [hb_fromImem, hb_f2d, hb_ep]
      rcases hEM : (if ((M_mkFIFO.meth_first a.f2d).iEp == a.ep) then BTrue Unit_ else BFalse Unit_) with u | u
      · cases u
        rw [hEM] at hopReady_gated
        have hopReady_a : decodeOperandsReady (M_mkFIFO.meth_first a.fromImem).data a.sb = BTrue Unit_ := by
          unfold decodeOperandsReady
          simp only [bool_and_true_iff, bool_or_true_iff, bool_not, reduceCtorEq]
          simp only [bool_or_true_iff, bool_and_true_iff, bool_not, reduceCtorEq] at hopReady_gated
          tauto
        have hopReady_b := decodeOperandsReady_agree _ a.sb b.sb hsb_agree0 hopReady_a
        unfold decodeOperandsReady at hopReady_b
        simp only [bool_and_true_iff, bool_or_true_iff, bool_not, reduceCtorEq] at hopReady_b ⊢
        tauto
      · cases u
        simp only [bool_or_true_iff, bool_not, reduceCtorEq]
        tauto
    · rw [hb_f2d, hb_fromImem, hb_ep, hb_d2e]
      exact hRest
  -- remaining "unchanged by this rule" facts (squash-independent: decode only ever
  -- touches f2d/fromImem/d2e/sb)
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_dMem : c.dMem = a.dMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_dreq : c.dreq = a.dreq := by rw [← hc2]
  have hc_toImem : c.toImem = a.toImem := by rw [← hc2]
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_pc : c.pc = a.pc := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_fromImem : c.fromImem = (M_mkFIFO.meth_deq a.fromImem).avAction_ := by rw [← hc2]
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_toDmem : b.toDmem = a.toDmem := by rw [← hb2]
  have hb_pc : b.pc = a.pc := by rw [← hb2]
  have he2w_eq : (M_mktop_pipelined.rule_RL_decode b).2.e2w = (M_mktop_pipelined.rule_RL_writeback c).2.e2w := by
    show b.e2w = _
    rw [← hb2, ← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_decode]
  have hfromDmem_eq : (M_mktop_pipelined.rule_RL_decode b).2.fromDmem = (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem := by
    show b.fromDmem = _
    rw [← hb2, ← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_decode]
  have hrf_eq : (M_mktop_pipelined.rule_RL_decode b).2.rf = (M_mktop_pipelined.rule_RL_writeback c).2.rf := by
    show b.rf = _
    rw [← hb2, ← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_decode]
  have hretiredInst_eq : (M_mktop_pipelined.rule_RL_decode b).2.retiredInst = (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst := by
    show b.retiredInst = _
    rw [← hb2, ← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_decode]
  have hf2d_eq : (M_mktop_pipelined.rule_RL_decode b).2.f2d = (M_mktop_pipelined.rule_RL_writeback c).2.f2d := by
    show _ = c.f2d
    rw [← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_decode]
    simp only [hb_f2d, hb_fromImem, hb_d2e]
  have hfromImem_eq : (M_mktop_pipelined.rule_RL_decode b).2.fromImem = (M_mktop_pipelined.rule_RL_writeback c).2.fromImem := by
    show _ = c.fromImem
    rw [← hc2]
    dsimp only [M_mktop_pipelined.rule_RL_decode]
    simp only [hb_f2d, hb_fromImem, hb_d2e]
  have hiMem_eq : (M_mktop_pipelined.rule_RL_decode b).2.iMem = (M_mktop_pipelined.rule_RL_writeback c).2.iMem :=
    hb_iMem.trans hc_iMem.symm
  have hdMem_eq : (M_mktop_pipelined.rule_RL_decode b).2.dMem = (M_mktop_pipelined.rule_RL_writeback c).2.dMem :=
    hb_dMem.trans hc_dMem.symm
  have hireq_eq : (M_mktop_pipelined.rule_RL_decode b).2.ireq = (M_mktop_pipelined.rule_RL_writeback c).2.ireq :=
    hb_ireq.trans hc_ireq.symm
  have hdreq_eq : (M_mktop_pipelined.rule_RL_decode b).2.dreq = (M_mktop_pipelined.rule_RL_writeback c).2.dreq :=
    hb_dreq.trans hc_dreq.symm
  have htoImem_eq : (M_mktop_pipelined.rule_RL_decode b).2.toImem = (M_mktop_pipelined.rule_RL_writeback c).2.toImem :=
    hb_toImem.trans hc_toImem.symm
  have htoDmem_eq : (M_mktop_pipelined.rule_RL_decode b).2.toDmem = (M_mktop_pipelined.rule_RL_writeback c).2.toDmem :=
    hb_toDmem.trans hc_toDmem.symm
  have hpc_eq : (M_mktop_pipelined.rule_RL_decode b).2.pc = (M_mktop_pipelined.rule_RL_writeback c).2.pc :=
    hb_pc.trans hc_pc.symm
  have hep_eq : (M_mktop_pipelined.rule_RL_decode b).2.ep = (M_mktop_pipelined.rule_RL_writeback c).2.ep :=
    hb_ep.trans hc_ep.symm
  have final_eq : (M_mktop_pipelined.rule_RL_decode b).2 = (M_mktop_pipelined.rule_RL_writeback c).2 := by
    by_cases hnorm : (if ((M_mkFIFO.meth_first a.f2d).iEp == a.ep) then BTrue Unit_ else BFalse Unit_) = BTrue Unit_
    · -- decode not squashed: genuine issue+release commute, with the rf-aliasing argument
      have hd2e : a.d2e.hasElement = false := by
        rw [hnorm] at hRest
        simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff] at hRest
        tauto
      have hopReady : decodeOperandsReady (M_mkFIFO.meth_first a.fromImem).data a.sb = BTrue Unit_ := by
        have hopReady_gated' := hopReady_gated
        rw [hnorm] at hopReady_gated'
        unfold decodeOperandsReady
        simp only [bool_and_true_iff, bool_or_true_iff, bool_not, reduceCtorEq]
        simp only [bool_or_true_iff, bool_and_true_iff, bool_not, reduceCtorEq] at hopReady_gated'
        tauto
      have hsb_a_Rw : arr_get a.sb (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat =
          ite_bsv (dInstWrites (M_mkFIFO.meth_first a.e2w).dInst) 1 0 := by
        have h := hpt (dInstRd (M_mkFIFO.meth_first a.e2w).dInst)
        rw [hd2e, he2w] at h
        have hzero : sbContrib false (M_mkFIFO.meth_first a.d2e).dInst (dInstRd (M_mkFIFO.meth_first a.e2w).dInst) = 0 := rfl
        rw [hzero, zero_add] at h
        rw [h]
        unfold sbContrib
        simp only [dInstRd, BEq.rfl, if_true, bool_and_true_right]
        rfl
      obtain ⟨rfv, hb_rf⟩ : ∃ v, b.rf = arr_set a.rf (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat v :=
        ⟨_, by rw [← hb2]; unfold dInstRd; rfl⟩
      have hrf_ne : ∀ idx : BitVec 5, idx ≠ dInstRd (M_mkFIFO.meth_first a.e2w).dInst →
          arr_get a.rf idx.toNat = arr_get b.rf idx.toNat := by
        intro idx hidx
        rw [hb_rf, arr_get_arr_set_ne]
        intro hcon; exact hidx (BitVec.eq_of_toNat_eq hcon.symm)
      have hb_rf_not_write : dInstWrites (M_mkFIFO.meth_first a.e2w).dInst = BFalse Unit_ → b.rf = a.rf := by
        intro hnw
        have hdisc2 : (bitvec1_to_bool (bit_and
              (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.valid_rd)
                (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.legal))
              (bool_to_bitvec1 (bool_not (if ((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd == (0:BitVec 5)) = true then BTrue Unit_ else BFalse Unit_)))))
            = dInstWrites (M_mkFIFO.meth_first a.e2w).dInst := by
          unfold dInstWrites dInstRd
          simp only [bitvec1_bit_and', bitvec1_bit_not', bitvec1_roundtrip]
        have : b.rf = arr_set a.rf (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat (arr_get a.rf (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat) := by
          rw [← hb2]
          dsimp only
          unfold dInstRd
          rw [hdisc2, hnw]
        rw [this, arr_set_self_get]
      have hrf_agree_reg : ∀ idx : BitVec 5, arr_get a.sb idx.toNat = 0 →
          arr_get a.rf idx.toNat = arr_get b.rf idx.toNat := by
        intro idx h0
        by_cases heq : idx = dInstRd (M_mkFIFO.meth_first a.e2w).dInst
        · subst heq
          by_cases hw : dInstWrites (M_mkFIFO.meth_first a.e2w).dInst = BTrue Unit_
          · exfalso
            rw [hsb_a_Rw, hw] at h0
            simp [ite_bsv] at h0
          · have hnw : dInstWrites (M_mkFIFO.meth_first a.e2w).dInst = BFalse Unit_ := by
              rcases hh : dInstWrites (M_mkFIFO.meth_first a.e2w).dInst with _ | _
              · exact absurd hh hw
              · rfl
            rw [hb_rf_not_write hnw]
        · exact hrf_ne idx heq
      have hc_sb : c.sb = arr_set a.sb (dInstRd (decodeInst (M_mkFIFO.meth_first a.fromImem).data)).toNat
          (arr_get a.sb (dInstRd (decodeInst (M_mkFIFO.meth_first a.fromImem).data)).toNat +
            ite_bsv (dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data)) (1 : BitVec 2) (0 : BitVec 2)) := by
        have hdisc3 : (bitvec1_to_bool (bit_and
              (bit_and (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).valid_rd)
                (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).legal))
              (bool_to_bitvec1 (bool_not (if ((getInstFields (M_mkFIFO.meth_first a.fromImem).data).rd == (0 : BitVec 5)) = true then BTrue Unit_ else BFalse Unit_)))))
            = dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data) := by
          unfold dInstWrites dInstRd
          unfold decodeInst
          simp only [bitvec1_bit_and', bitvec1_bit_not', bitvec1_roundtrip]
        rw [← hc2]
        dsimp only
        rw [hnorm]
        unfold ite_bsv
        rw [hdisc3]
        unfold dInstRd
        cases dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data) <;> rfl
      have hb_sb2 : (M_mktop_pipelined.rule_RL_decode b).2.sb =
          arr_set b.sb (dInstRd (decodeInst (M_mkFIFO.meth_first a.fromImem).data)).toNat
            (arr_get b.sb (dInstRd (decodeInst (M_mkFIFO.meth_first a.fromImem).data)).toNat +
              ite_bsv (dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data)) (1 : BitVec 2) (0 : BitVec 2)) := by
        have hdisc3 : (bitvec1_to_bool (bit_and
              (bit_and (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).valid_rd)
                (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).legal))
              (bool_to_bitvec1 (bool_not (if ((getInstFields (M_mkFIFO.meth_first a.fromImem).data).rd == (0 : BitVec 5)) = true then BTrue Unit_ else BFalse Unit_)))))
            = dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data) := by
          unfold dInstWrites dInstRd
          unfold decodeInst
          simp only [bitvec1_bit_and', bitvec1_bit_not', bitvec1_roundtrip]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [hb_fromImem, hb_f2d, hb_ep, hnorm]
        unfold ite_bsv
        rw [hdisc3]
        unfold dInstRd
        cases dInstWrites (decodeInst (M_mkFIFO.meth_first a.fromImem).data) <;> rfl
      have hwb_sb2 : (M_mktop_pipelined.rule_RL_writeback c).2.sb =
          arr_set c.sb (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat
            (arr_get c.sb (dInstRd (M_mkFIFO.meth_first a.e2w).dInst).toNat +
              ite_bsv (dInstWrites (M_mkFIFO.meth_first a.e2w).dInst) (3 : BitVec 2) (0 : BitVec 2)) := by
        have hdisc4 : (bitvec1_to_bool (bit_and
              (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.valid_rd)
                (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.legal))
              (bool_to_bitvec1 (bool_not (if ((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd == (0 : BitVec 5)) = true then BTrue Unit_ else BFalse Unit_)))))
            = dInstWrites (M_mkFIFO.meth_first a.e2w).dInst := by
          unfold dInstWrites dInstRd
          simp only [bitvec1_bit_and', bitvec1_bit_not', bitvec1_roundtrip]
        dsimp only [M_mktop_pipelined.rule_RL_writeback]
        rw [hc_e2w]
        unfold ite_bsv
        rw [hdisc4]
        unfold dInstRd
        cases dInstWrites (M_mkFIFO.meth_first a.e2w).dInst <;> rfl
      have hsb_eq : (M_mktop_pipelined.rule_RL_decode b).2.sb = (M_mktop_pipelined.rule_RL_writeback c).2.sb := by
        rw [hb_sb2, hwb_sb2, hb_sb, hc_sb]
        exact arr_get_set_delta_comm a.sb _ _ _ _
      have hopReady' := hopReady
      unfold decodeOperandsReady at hopReady'
      simp only [bool_and_true_iff, bool_or_true_iff, sb_ready_iff] at hopReady'
      obtain ⟨hr1, hr2⟩ := hopReady'
      have hd2e_eq : (M_mktop_pipelined.rule_RL_decode b).2.d2e = (M_mktop_pipelined.rule_RL_writeback c).2.d2e := by
        have hc_d2e_untouched : (M_mktop_pipelined.rule_RL_writeback c).2.d2e = c.d2e := by
          dsimp only [M_mktop_pipelined.rule_RL_writeback]
        rw [hc_d2e_untouched, ← hc2]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [hb_d2e, hb_fromImem, hb_f2d, hb_ep, hnorm]
        generalize hsq1 : (bitvec1_to_bool (bit_or (bit_or
                (bool_to_bitvec1 (if ((getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs1 == (0:BitVec 5)) = true then BTrue Unit_ else BFalse Unit_))
                (bit_not (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).valid_rs1)))
              (bit_not (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).legal)))) = sq1
        generalize hsq2 : (bitvec1_to_bool (bit_or (bit_or
                (bool_to_bitvec1 (if ((getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs2 == (0:BitVec 5)) = true then BTrue Unit_ else BFalse Unit_))
                (bit_not (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).valid_rs2)))
              (bit_not (bool_to_bitvec1 (decodeInst (M_mkFIFO.meth_first a.fromImem).data).legal)))) = sq2
        have hgo1 : sq1 = BFalse Unit_ →
            arr_get b.rf (getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs1.toNat =
            arr_get a.rf (getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs1.toNat := by
          intro hf
          rw [hf] at hsq1
          simp only [bitvec1_bit_and', bitvec1_bit_or', bitvec1_bit_not', bitvec1_roundtrip] at hsq1
          obtain ⟨hab, hlegal⟩ := (bool_or_false_iff _ _).mp hsq1
          obtain ⟨hne0, hv1⟩ := (bool_or_false_iff _ _).mp hab
          rw [(bool_not_false_iff _).mp hv1] at hr1
          rcases hr1 with ⟨_, hz1⟩ | hcontra
          · exact (hrf_agree_reg _ hz1).symm
          · simp [bool_not] at hcontra
        have hgo2 : sq2 = BFalse Unit_ →
            arr_get b.rf (getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs2.toNat =
            arr_get a.rf (getInstFields (M_mkFIFO.meth_first a.fromImem).data).rs2.toNat := by
          intro hf
          rw [hf] at hsq2
          simp only [bitvec1_bit_and', bitvec1_bit_or', bitvec1_bit_not', bitvec1_roundtrip] at hsq2
          obtain ⟨hab, hlegal⟩ := (bool_or_false_iff _ _).mp hsq2
          obtain ⟨hne0, hv2⟩ := (bool_or_false_iff _ _).mp hab
          rw [(bool_not_false_iff _).mp hv2] at hr2
          rcases hr2 with ⟨_, hz2⟩ | hcontra
          · exact (hrf_agree_reg _ hz2).symm
          · simp [bool_not] at hcontra
        cases sq1
        case BTrue u1 =>
          cases u1
          cases sq2
          case BTrue u2 => cases u2; rfl
          case BFalse u2 => cases u2; rw [hgo2 rfl]
        case BFalse u1 =>
          cases u1
          rw [hgo1 rfl]
          cases sq2
          case BTrue u2 => cases u2; rfl
          case BFalse u2 => cases u2; rw [hgo2 rfl]
      exact (M_mktop_pipelined.state.mk.injEq ..).mpr
        ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
         hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
    · -- decode squashed: no `d2e`/`sb` marking at all, so both are simply untouched by
      -- decode; `sb`'s only remaining change is writeback's own release
      have hsquash : (if ((M_mkFIFO.meth_first a.f2d).iEp == a.ep) then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
        rcases h : (if ((M_mkFIFO.meth_first a.f2d).iEp == a.ep) then BTrue Unit_ else BFalse Unit_) with u | u
        · cases u; exact absurd h hnorm
        · cases u; rfl
      have hd2e_eq : (M_mktop_pipelined.rule_RL_decode b).2.d2e = (M_mktop_pipelined.rule_RL_writeback c).2.d2e := by
        have hc_d2e_untouched : (M_mktop_pipelined.rule_RL_writeback c).2.d2e = c.d2e := by
          dsimp only [M_mktop_pipelined.rule_RL_writeback]
        rw [hc_d2e_untouched]
        dsimp only [M_mktop_pipelined.rule_RL_decode]
        rw [hb_fromImem, hb_f2d, hb_ep, ← hc2, hsquash, hb_d2e]
      have hsb_eq : (M_mktop_pipelined.rule_RL_decode b).2.sb = (M_mktop_pipelined.rule_RL_writeback c).2.sb := by
        have hdb_sb : (M_mktop_pipelined.rule_RL_decode b).2.sb = b.sb := by
          dsimp only [M_mktop_pipelined.rule_RL_decode]
          rw [hb_fromImem, hb_f2d, hb_ep, hsquash]
        rw [hdb_sb, ← hb2, ← hc2]
        dsimp only [M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_decode]
        rw [hsquash]
      exact (M_mktop_pipelined.state.mk.injEq ..).mpr
        ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
         hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2,
    Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_decode, ?_⟩⟩
  · exact Prod.ext hc_wb_guard rfl
  · exact Prod.ext hb_decode_guard final_eq

theorem commutes_RL_writeback_RL_decode_given_SbInv {a b c : ImplModule.State} (hInv : SbInv a) :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_decode_RL_writeback_given_SbInv hInv hb hc
  exact ⟨d, hd2, hd1⟩

-- Genuinely NOT confluent AS AN UNCONDITIONAL LEMMA (required here, since
-- `rules_commute_weakly`'s default `by grind` composes every `@[local grind →]`
-- commute lemma unconditionally). `RL_decode` reads the scoreboard `sb` to
-- decide whether rs1/rs2 are ready, and `RL_writeback` releases (decrements)
-- `sb[rd]`; from an UNREACHABLE state where `a.sb[R] = 0` while `a.e2w`'s
-- instruction *also* validly targets `rd = R`, firing order flips decode's
-- readiness check for a register decode reads as rs1/rs2 that aliases `R`.
-- `commutes_RL_decode_RL_writeback_given_SbInv` above proves this *is* true
-- (fully, no `sorry`) given the scoreboard invariant `SbInv a`. `SbInv` itself
-- is a real, provable invariant of reachable states (proved by induction over
-- `phi0`'s reachability in the reference file), but `phi0` stays `sorry` here,
-- so that route isn't available for the *unconditional* signature
-- `rules_commute_weakly` needs, and this is left unproved.
@[local grind →] theorem commutes_RL_decode_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_decode a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

@[local grind →] theorem commutes_RL_execute_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_requestI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_execute_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_responseI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_execute_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     clear hc hb;
     simp only [mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hb1;
     generalize hsq : (if ((M_mkFIFO.meth_first a.d2e).iEp == a.ep) = true then BTrue Unit_ else BFalse Unit_) = sq at hc1 ⊢;
     generalize hmem : (isMemoryInst (M_mkFIFO.meth_first a.d2e).dInst) = mem at hc1 ⊢;
     cases sq <;> cases mem <;>
       simp only [bool_not, mkFIFO_RDY_enq_iff, mkFIFO_RDY_deq_iff, mkFIFO_RDY_first_iff, bool_and_true_iff] at hc1 ⊢ <;>
       first
         | rfl
         | (exfalso; simp_all; done)
         | (simp_all; done))

@[local grind →] theorem commutes_RL_execute_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseD c).2, Relation.ReflTransGen.single ⟨.RL_responseD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_responseD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

-- See `commutes_RL_fetch_RL_execute` (the ordered-opposite of this pair): same `pc`
-- write-write race; the no-misprediction case is proven there via an internal case
-- split, and the misprediction case needs `FetchPipeInv`
-- (`commutes_RL_fetch_RL_execute_given_FetchPipeInv`, fully proven), which isn't
-- available unconditionally without `phi0`, so this is left unproved.
@[local grind →] theorem commutes_RL_execute_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

-- See `commutes_RL_fetch_RL_execute_given_FetchPipeInv` (the ordered-opposite of this
-- pair): fully proven via the two-round requestI/responseI trick, ported here via the
-- standard commute-swap trick.
theorem commutes_RL_execute_RL_fetch_given_FetchPipeInv {a b c : ImplModule.State}
    (hInv : FetchPipeInv a) :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_fetch_RL_execute_given_FetchPipeInv hInv hb hc
  exact ⟨d, hd2, hd1⟩

-- See `commutes_RL_decode_RL_execute_given_F2DStaleInv` (the ordered-opposite of this
-- pair): fully proven given `F2DStaleInv`, which isn't available unconditionally
-- without `phi0`, so this is left unproved.
@[local grind →] theorem commutes_RL_execute_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

-- See `commutes_RL_decode_RL_execute_given_F2DStaleInv` (the ordered-opposite of this
-- pair): fully proven, ported here via the standard commute-swap trick.
theorem commutes_RL_execute_RL_decode_given_F2DStaleInv {a b c : ImplModule.State}
    (hInv : F2DStaleInv a) :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_decode_RL_execute_given_F2DStaleInv hInv hb hc
  exact ⟨d, hd2, hd1⟩

@[local grind →] theorem commutes_RL_execute_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

-- `e2w` is shared: `RL_execute` enqueues it (only when not squashed); `RL_writeback`
-- dequeues it unconditionally. When `RL_writeback` also fires from the same state,
-- `RL_execute`'s "not squashed" branch is impossible (it would require `e2w` empty,
-- contradicting `RL_writeback`'s dequeue-readiness), so `RL_execute` must be in its
-- squash branch, where it never touches `e2w`, `sb`, `toDmem`, `ep`, or `pc` -- and `sb`'s
-- release (by `RL_writeback`) commutes with nothing else touching it.
@[local grind →] theorem commutes_RL_execute_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_execute a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute, M_mktop_pipelined.rule_RL_writeback] at hc hb
  obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc
  obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb
  have he2w_ready : a.e2w.hasElement = true := by
    have hb1' := hb1
    simp only [bool_and_true_iff, mkFIFO_RDY_deq_iff] at hb1'
    exact hb1'.2.1
  have hsquash : (bool_not (if ((M_mkFIFO.meth_first a.d2e).iEp == a.ep) then BTrue Unit_ else BFalse Unit_)) = BTrue Unit_ := by
    by_contra hne
    have hbf : (bool_not (if ((M_mkFIFO.meth_first a.d2e).iEp == a.ep) then BTrue Unit_ else BFalse Unit_)) = BFalse Unit_ := by
      cases h : (bool_not (if ((M_mkFIFO.meth_first a.d2e).iEp == a.ep) then BTrue Unit_ else BFalse Unit_)) with
      | BTrue u => cases u; exact absurd h hne
      | BFalse u => cases u; rfl
    have hc1' := hc1
    rw [hbf] at hc1'
    simp only [bool_and_true_iff, mkFIFO_RDY_enq_iff] at hc1'
    have he2w_not_ready : a.e2w.hasElement = false := by tauto
    rw [he2w_ready] at he2w_not_ready
    exact absurd he2w_not_ready (by decide)
  rw [hsquash] at hc1 hc2
  -- fields of c untouched (or trivially unchanged given squash) by execute
  have hc_toDmem : c.toDmem = a.toDmem := by rw [← hc2]
  have hc_ep : c.ep = a.ep := by rw [← hc2]
  have hc_pc : c.pc = a.pc := by rw [← hc2]
  have hc_e2w : c.e2w = a.e2w := by rw [← hc2]
  have hc_retiredInst : c.retiredInst = a.retiredInst := by rw [← hc2]
  have hc_fromDmem : c.fromDmem = a.fromDmem := by rw [← hc2]
  have hc_rf : c.rf = a.rf := by rw [← hc2]
  have hc_f2d : c.f2d = a.f2d := by rw [← hc2]
  have hc_iMem : c.iMem = a.iMem := by rw [← hc2]
  have hc_dMem : c.dMem = a.dMem := by rw [← hc2]
  have hc_ireq : c.ireq = a.ireq := by rw [← hc2]
  have hc_dreq : c.dreq = a.dreq := by rw [← hc2]
  have hc_toImem : c.toImem = a.toImem := by rw [← hc2]
  have hc_fromImem : c.fromImem = a.fromImem := by rw [← hc2]
  have hc_d2e : c.d2e = (M_mkFIFO.meth_deq a.d2e).avAction_ := by rw [← hc2]
  -- fields of b untouched by writeback
  have hb_d2e : b.d2e = a.d2e := by rw [← hb2]
  have hb_ep : b.ep = a.ep := by rw [← hb2]
  have hb_toDmem : b.toDmem = a.toDmem := by rw [← hb2]
  have hb_pc : b.pc = a.pc := by rw [← hb2]
  have hb_f2d : b.f2d = a.f2d := by rw [← hb2]
  have hb_iMem : b.iMem = a.iMem := by rw [← hb2]
  have hb_dMem : b.dMem = a.dMem := by rw [← hb2]
  have hb_ireq : b.ireq = a.ireq := by rw [← hb2]
  have hb_dreq : b.dreq = a.dreq := by rw [← hb2]
  have hb_toImem : b.toImem = a.toImem := by rw [← hb2]
  have hb_fromImem : b.fromImem = a.fromImem := by rw [← hb2]
  have hc_wb_guard : (M_mktop_pipelined.rule_RL_writeback c).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_retiredInst, hc_e2w, hc_fromDmem]
    exact hb1
  have hb_execute_guard : (M_mktop_pipelined.rule_RL_execute b).1 = BTrue Unit_ := by
    dsimp only [M_mktop_pipelined.rule_RL_execute]
    rw [hb_d2e, hb_ep, hsquash]
    exact hc1
  -- fields untouched by both rules: trivially agree via a
  have hiMem_eq : (M_mktop_pipelined.rule_RL_execute b).2.iMem = (M_mktop_pipelined.rule_RL_writeback c).2.iMem := by
    show b.iMem = c.iMem; rw [hb_iMem, hc_iMem]
  have hdMem_eq : (M_mktop_pipelined.rule_RL_execute b).2.dMem = (M_mktop_pipelined.rule_RL_writeback c).2.dMem := by
    show b.dMem = c.dMem; rw [hb_dMem, hc_dMem]
  have hireq_eq : (M_mktop_pipelined.rule_RL_execute b).2.ireq = (M_mktop_pipelined.rule_RL_writeback c).2.ireq := by
    show b.ireq = c.ireq; rw [hb_ireq, hc_ireq]
  have hdreq_eq : (M_mktop_pipelined.rule_RL_execute b).2.dreq = (M_mktop_pipelined.rule_RL_writeback c).2.dreq := by
    show b.dreq = c.dreq; rw [hb_dreq, hc_dreq]
  have htoImem_eq : (M_mktop_pipelined.rule_RL_execute b).2.toImem = (M_mktop_pipelined.rule_RL_writeback c).2.toImem := by
    show b.toImem = c.toImem; rw [hb_toImem, hc_toImem]
  have hfromImem_eq : (M_mktop_pipelined.rule_RL_execute b).2.fromImem = (M_mktop_pipelined.rule_RL_writeback c).2.fromImem := by
    show b.fromImem = c.fromImem; rw [hb_fromImem, hc_fromImem]
  have hf2d_eq : (M_mktop_pipelined.rule_RL_execute b).2.f2d = (M_mktop_pipelined.rule_RL_writeback c).2.f2d := by
    show b.f2d = c.f2d; rw [hb_f2d, hc_f2d]
  have htoDmem_eq : (M_mktop_pipelined.rule_RL_execute b).2.toDmem = (M_mktop_pipelined.rule_RL_writeback c).2.toDmem := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.toDmem = b.toDmem := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]; rw [hb_d2e, hb_ep, hsquash]
    rw [h1, hb_toDmem]
    show a.toDmem = c.toDmem; rw [hc_toDmem]
  have hep_eq : (M_mktop_pipelined.rule_RL_execute b).2.ep = (M_mktop_pipelined.rule_RL_writeback c).2.ep := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.ep = b.ep := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]; rw [hb_d2e, hb_ep, hsquash]
    rw [h1, hb_ep]
    show a.ep = c.ep; rw [hc_ep]
  have hpc_eq : (M_mktop_pipelined.rule_RL_execute b).2.pc = (M_mktop_pipelined.rule_RL_writeback c).2.pc := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.pc = b.pc := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]; rw [hb_d2e, hb_ep, hsquash]
    rw [h1, hb_pc]
    show a.pc = c.pc; rw [hc_pc]
  -- fields computed by writeback, untouched by execute (need b's value matches)
  have he2w_eq : (M_mktop_pipelined.rule_RL_execute b).2.e2w = (M_mktop_pipelined.rule_RL_writeback c).2.e2w := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.e2w = b.e2w := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]; rw [hb_d2e, hb_ep, hsquash]
    have h2 : (M_mktop_pipelined.rule_RL_writeback c).2.e2w = (M_mkFIFO.meth_deq a.e2w).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rw [hc_e2w]
    have hb_e2w_def : b.e2w = (M_mkFIFO.meth_deq a.e2w).avAction_ := by rw [← hb2]
    rw [h1, h2, hb_e2w_def]
  have hrf_eq : (M_mktop_pipelined.rule_RL_execute b).2.rf = (M_mktop_pipelined.rule_RL_writeback c).2.rf := by
    show b.rf = (M_mktop_pipelined.rule_RL_writeback c).2.rf
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hc_fromDmem, hc_rf]
    rfl
  have hretiredInst_eq : (M_mktop_pipelined.rule_RL_execute b).2.retiredInst = (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst := by
    show b.retiredInst = (M_mktop_pipelined.rule_RL_writeback c).2.retiredInst
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hc_fromDmem]
    rfl
  have hfromDmem_eq : (M_mktop_pipelined.rule_RL_execute b).2.fromDmem = (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem := by
    show b.fromDmem = (M_mktop_pipelined.rule_RL_writeback c).2.fromDmem
    rw [← hb2]
    dsimp only [M_mktop_pipelined.rule_RL_writeback]
    rw [hc_e2w, hc_fromDmem]
  -- d2e: dequeued by execute, untouched by writeback
  have hd2e_eq : (M_mktop_pipelined.rule_RL_execute b).2.d2e = (M_mktop_pipelined.rule_RL_writeback c).2.d2e := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.d2e = (M_mkFIFO.meth_deq b.d2e).avAction_ := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]
    rw [h1, hb_d2e]
    show (M_mkFIFO.meth_deq a.d2e).avAction_ = c.d2e
    rw [hc_d2e]
  -- sb: released independently by both rules at (generally) different indices; commutes
  have hsb_eq : (M_mktop_pipelined.rule_RL_execute b).2.sb = (M_mktop_pipelined.rule_RL_writeback c).2.sb := by
    have h1 : (M_mktop_pipelined.rule_RL_execute b).2.sb =
        arr_set b.sb ((getInstFields (M_mkFIFO.meth_first b.d2e).dInst.inst).rd).toNat
          ((arr_get b.sb ((getInstFields (M_mkFIFO.meth_first b.d2e).dInst.inst).rd).toNat +
            match _ : (bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first b.d2e).dInst.valid_rd) (bool_to_bitvec1 (M_mkFIFO.meth_first b.d2e).dInst.legal)) (bool_to_bitvec1 (bool_not (if (((getInstFields (M_mkFIFO.meth_first b.d2e).dInst.inst).rd == (0 : BitVec 5))) then BTrue Unit_ else BFalse Unit_))))) with
              | BTrue _ => (3 : BitVec 2)
              | BFalse _ => (0 : BitVec 2))) := by
      dsimp only [M_mktop_pipelined.rule_RL_execute]; rw [hb_d2e, hb_ep, hsquash]; rfl
    have h2 : (M_mktop_pipelined.rule_RL_writeback c).2.sb =
        arr_set c.sb ((getInstFields (M_mkFIFO.meth_first c.e2w).dInst.inst).rd).toNat
          ((arr_get c.sb ((getInstFields (M_mkFIFO.meth_first c.e2w).dInst.inst).rd).toNat +
            match _ : (bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first c.e2w).dInst.valid_rd) (bool_to_bitvec1 (M_mkFIFO.meth_first c.e2w).dInst.legal)) (bool_to_bitvec1 (bool_not (if (((getInstFields (M_mkFIFO.meth_first c.e2w).dInst.inst).rd == (0 : BitVec 5))) then BTrue Unit_ else BFalse Unit_))))) with
              | BTrue _ => (3 : BitVec 2)
              | BFalse _ => (0 : BitVec 2))) := by
      dsimp only [M_mktop_pipelined.rule_RL_writeback]; rfl
    have hc_sb : c.sb =
        arr_set a.sb ((getInstFields (M_mkFIFO.meth_first a.d2e).dInst.inst).rd).toNat
          ((arr_get a.sb ((getInstFields (M_mkFIFO.meth_first a.d2e).dInst.inst).rd).toNat +
            match _ : (bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first a.d2e).dInst.valid_rd) (bool_to_bitvec1 (M_mkFIFO.meth_first a.d2e).dInst.legal)) (bool_to_bitvec1 (bool_not (if (((getInstFields (M_mkFIFO.meth_first a.d2e).dInst.inst).rd == (0 : BitVec 5))) then BTrue Unit_ else BFalse Unit_))))) with
              | BTrue _ => (3 : BitVec 2)
              | BFalse _ => (0 : BitVec 2))) := by
      rw [← hc2]; rfl
    have hb_sb : b.sb =
        arr_set a.sb ((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd).toNat
          ((arr_get a.sb ((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd).toNat +
            match _ : (bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.valid_rd) (bool_to_bitvec1 (M_mkFIFO.meth_first a.e2w).dInst.legal)) (bool_to_bitvec1 (bool_not (if (((getInstFields (M_mkFIFO.meth_first a.e2w).dInst.inst).rd == (0 : BitVec 5))) then BTrue Unit_ else BFalse Unit_))))) with
              | BTrue _ => (3 : BitVec 2)
              | BFalse _ => (0 : BitVec 2))) := by
      rw [← hb2]; rfl
    rw [h1, h2, hb_d2e, hc_e2w, hb_sb, hc_sb]
    exact arr_get_set_delta_comm a.sb _ _ _ _
  have final_eq : (M_mktop_pipelined.rule_RL_execute b).2 = (M_mktop_pipelined.rule_RL_writeback c).2 :=
    (M_mktop_pipelined.state.mk.injEq ..).mpr
      ⟨hiMem_eq, hdMem_eq, hireq_eq, hdreq_eq, htoImem_eq, hfromImem_eq, htoDmem_eq, hfromDmem_eq,
       hf2d_eq, hd2e_eq, he2w_eq, hretiredInst_eq, hpc_eq, hep_eq, hrf_eq, hsb_eq⟩
  refine ⟨(M_mktop_pipelined.rule_RL_writeback c).2,
    Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩, Relation.ReflTransGen.single ⟨.RL_execute, ?_⟩⟩
  · exact Prod.ext hc_wb_guard rfl
  · exact Prod.ext hb_execute_guard final_eq


@[local grind →] theorem commutes_RL_writeback_RL_requestI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestI c).2, Relation.ReflTransGen.single ⟨.RL_requestI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_requestI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_writeback_RL_responseI {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseI a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_responseI c).2, Relation.ReflTransGen.single ⟨.RL_responseI, ?_⟩, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_responseI] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

@[local grind →] theorem commutes_RL_writeback_RL_requestD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_requestD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  refine ⟨(M_mktop_pipelined.rule_RL_requestD c).2, Relation.ReflTransGen.single ⟨.RL_requestD, ?_⟩, Relation.ReflTransGen.single ⟨.RL_writeback, ?_⟩⟩ <;>
    dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback, M_mktop_pipelined.rule_RL_requestD] at hc hb ⊢ <;>
    (obtain ⟨hc1, hc2⟩ := Prod.mk.injEq .. |>.mp hc;
     obtain ⟨hb1, hb2⟩ := Prod.mk.injEq .. |>.mp hb;
     subst hc2; subst hb2; dsimp only;
     first
       | (simp_all; done)
       | grind
       | (split_ifs at hc1 hb1 ⊢ <;> simp_all)
       | (split_ifs at hc1 hb1 ⊢ <;> grind))

-- See `commutes_RL_responseD_RL_writeback` (the ordered-opposite of this pair): fully
-- proven, ported here via the standard commute-swap trick.
@[local grind →] theorem commutes_RL_writeback_RL_responseD {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_responseD a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_responseD_RL_writeback hb hc
  exact ⟨d, hd2, hd1⟩

-- See `commutes_RL_fetch_RL_writeback` (the ordered-opposite of this pair): fully proven
-- via disjoint fields, ported here via the standard commute-swap trick.
@[local grind →] theorem commutes_RL_writeback_RL_fetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_fetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_fetch_RL_writeback hb hc
  exact ⟨d, hd2, hd1⟩

-- See `commutes_RL_decode_RL_writeback` (the ordered-opposite of this pair): same
-- missing-scoreboard-invariant obstruction (`commutes_RL_writeback_RL_decode_given_SbInv`
-- above proves the `SbInv`-conditioned version fully, no `sorry`), left unproved.
@[local grind →] theorem commutes_RL_writeback_RL_decode {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_decode a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  sorry

-- See `commutes_RL_execute_RL_writeback` (the ordered-opposite of this pair): fully
-- proven, ported here via the standard commute-swap trick.
@[local grind →] theorem commutes_RL_writeback_RL_execute {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_execute a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨d, hd1, hd2⟩ := commutes_RL_execute_RL_writeback hb hc
  exact ⟨d, hd2, hd1⟩

@[local grind →] theorem commutes_RL_writeback_RL_writeback {a b c : ImplModule.State} :
  ImplModule.getRule .RL_writeback a c →
  ImplModule.getRule .RL_writeback a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  dsimp [ImplModule, Module.getRule, ofRule] at hc hb
  have hbc : b = c := by rw [hc] at hb; exact (Prod.mk.injEq .. |>.mp hb).2.symm
  exact ⟨c, Relation.ReflTransGen.refl, hbc ▸ Relation.ReflTransGen.refl⟩

@[local grind →] theorem phi0_reaches_phi0_RL_requestI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_responseI (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseI i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_requestD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_requestD i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_responseD (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_responseD i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_fetch (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_fetch i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_decode (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_decode i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_execute (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_execute i i' → phi0 i' s := by
  sorry

@[local grind →] theorem phi0_reaches_phi0_RL_writeback (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_writeback i i' → phi0 i' s := by
  sorry

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  sorry

-- ──────────────────────────────────────────────────────────────────────
-- Below: fixed generic boilerplate (closes `refines` via enough_star).
-- ──────────────────────────────────────────────────────────────────────

attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

def mktop_pipelined_refinement : StructuredRefinement where
  Method := Method
  Rule := Rule
  spec := SpecModule
  impl := ImplModule
  flushed := phi0
  rules_strongly_normalising := rules_strongly_normalising
  method_rule_commute := by intro a b c e h hm; obtain ⟨r, hr⟩ := h; cases r <;> grind

theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  φ_ind phi0 ImplModule.getARule i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star SpecModule.getMethod s l s'
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mktop_pipelined_refinement

#print axioms refines

end M_mktop_pipelined.Refines
