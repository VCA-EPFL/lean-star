
import Star.Bluespec.CompiledProcessor.mktop_pipelined
import Star.Extra.HVector
open BluespecPrelude
open Params_types
open RVUtil

set_option maxHeartbeats 1000000

-- ═══ Specification (fill in State, methods, and phi0) ═══

namespace M_mktop_pipelined.Spec

structure State where
  pc : BitVec 32
  halted : BitVec 1
  rf : Array (BitVec 32) := .mk (List.replicate 32 default)
  imem : Array (BitVec 32) := .mk (List.replicate 65536 default)
  dmem : Array (BitVec 32) := .mk (List.replicate 65536 default)
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
        pc := nextPC }
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


structure Footprint where
  V : Type
  α : Type
  f : α → Type
  l : List α
  args : HVector f l
  ret : V




@[simp] abbrev Methods (M : Type) (State : Type) := M → Footprint → State → State → Prop
@[simp] abbrev Rules (R : Type) (State : Type) := R → State → State → Prop

structure Module (R M : Type) where
  State : Type
  rules : Rules R State
  methods : Methods M State

def Footprint.arg0 {V} v := @Footprint.mk V (Fin 0) (λ _ => Empty) [] .nil v

def ofAVMethod0 {State Value} (meth : State → t_actionvalue_ Value State) (meth_RDY : State → t_bool)
    : Footprint → State → State → Prop := fun e s s' =>
  ∃ v, meth s = ⟨v, s'⟩
         ∧ e = Footprint.arg0 v
         ∧ meth_RDY s = BTrue Unit_

def ofRule {State} (rule : State → t_bool × State) : State → State → Prop := fun s s' =>
  rule s = ⟨BTrue Unit_, s'⟩

def SpecModule : Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .meth_getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommit M_mktop_pipelined.Spec.meth_RDY_getCommit
  rules := Empty.casesOn _

def ImplModule : Module Rule Method where
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
-- Below: fixed generic boilerplate (closes `refines` via enough_star).
-- ──────────────────────────────────────────────────────────────────────
@[simp] abbrev Rule1 (A : Type _) := A → A → Prop
@[simp] abbrev Method1 (A : Type _) (E : Type _) := A → E → A → Prop -- B is the equeu element

variable {A B E}
variable (flush : A -> B -> Prop)
variable (rule : Rule1 A)
variable (method_i : Method1 A E)
variable (method_s : Method1 B E)

inductive trans_refl {A} (rule : Rule1 A) : Rule1 A where
| step {a b c} : rule a b → trans_refl rule b c → trans_refl rule a c
| refl {a} : trans_refl rule a a

inductive star : A -> List E -> A -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1 s2 s3 l e1, star s1 l s2 -> method_i s2 e1 s3 -> star s1 (e1 :: l) s3

inductive star_extend : A -> List E -> A -> Prop where
  | refl : ∀ s, star_extend s [] s
  | step_int : ∀ s l s' s'' , star_extend s l s' ->  trans_refl rule s' s'' -> star_extend s l s''
  | step_ext : ∀ s l s' s'' e, star_extend s l s' -> method_i s' e s'' -> star_extend s (e :: l) s''



def Module.getRule {R M} (m : Module R M) (name : R) : Rule1 m.State :=
  m.rules name

def Module.getARule {R M} (m : Module R M) : Rule1 m.State := fun s s' =>
  ∃ r : R, m.getRule r s s'

structure Event1 (M : Type _) where
  name : M
  footprint : Footprint

def Module.getMethod {R M} (m : Module R M) : Method1 m.State (Event1 M) := fun s e =>
  m.methods e.1 e.2 s


attribute [local grind →] Module.getARule
attribute [grind cases] Event1

set_option maxHeartbeats 4000000

open M_mktop_pipelined

-- ═══════════ 0. generic normalization lemmas ═══════════

@[simp] theorem unit_eq_Unit (u : unit_) : u = Unit_ := by cases u; rfl

@[simp] theorem bool_and_true_l (b : t_bool) : bool_and (BTrue Unit_) b = b := rfl
@[simp] theorem bool_and_false_l (b : t_bool) : bool_and (BFalse Unit_) b = BFalse Unit_ := rfl
@[simp] theorem bool_and_false_r (a : t_bool) : bool_and a (BFalse Unit_) = BFalse Unit_ := by
  cases a <;> rfl
@[simp] theorem bool_and_true_r (a : t_bool) : bool_and a (BTrue Unit_) = a := by
  cases a with
  | BTrue u => cases u; rfl
  | BFalse u => cases u; rfl
@[simp] theorem bool_not_true : bool_not (BTrue Unit_) = BFalse Unit_ := rfl
@[simp] theorem bool_not_false : bool_not (BFalse Unit_) = BTrue Unit_ := rfl

@[simp] theorem arr_get_nil {α : Type} [Inhabited α] (n : Nat) :
    arr_get (#[] : Array α) n = default := by
  simp [arr_get]

@[simp] theorem arr_set_nil {α : Type} (n : Nat) (v : α) :
    arr_set (#[] : Array α) n v = #[] := by
  simp [arr_set]

@[simp] theorem getD_nil {α : Type} (n : Nat) (d : α) :
    Array.getD (#[] : Array α) n d = d := by
  simp [Array.getD]

-- ═══════════ 1. closed facts about instruction 0x00000000 ═══════════

@[simp] theorem decode0_legal : (decodeInst 0).legal = BFalse Unit_ := rfl
@[simp] theorem decode0_valid_rs1 : (decodeInst 0).valid_rs1 = BTrue Unit_ := rfl
@[simp] theorem decode0_valid_rs2 : (decodeInst 0).valid_rs2 = BFalse Unit_ := rfl
@[simp] theorem decode0_valid_rd : (decodeInst 0).valid_rd = BTrue Unit_ := rfl
@[simp] theorem decode0_inst : (decodeInst 0).inst = 0 := rfl
@[simp] theorem isMem0 : isMemoryInst (decodeInst 0) = BTrue Unit_ := rfl
@[simp] theorem isCtrl0 : isControlInst (decodeInst 0) = BFalse Unit_ := rfl
@[simp] theorem imm0 : getImmediate (decodeInst 0) = 0 := rfl
@[simp] theorem fields0_rd : (getInstFields 0).rd = 0 := rfl
@[simp] theorem fields0_rs1 : (getInstFields 0).rs1 = 0 := rfl
@[simp] theorem fields0_rs2 : (getInstFields 0).rs2 = 0 := rfl
@[simp] theorem fields0_funct3 : (getInstFields 0).funct3 = 0 := rfl

@[simp] theorem execControl0 (pc : BitVec 32) :
    execControl32 0 0 0 0 pc = { taken := BFalse Unit_, nextPC := pc + 4 } := rfl
@[simp] theorem execALU0 (pc : BitVec 32) : execALU32 0 0 0 0 pc = 0 := rfl

-- ═══════════ 2. the abstraction ═══════════

/-- pc after `n` instruction fetches -/
def pcOf (n : Nat) : BitVec 32 := BitVec.ofNat 32 (4 * n)

@[simp] theorem pcOf_succ (n : Nat) : pcOf n + 4 = pcOf (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_add]

@[simp] theorem pcOf_succ' (n : Nat) : pcOf n + BitVec.ofNat 32 4 = pcOf (n + 1) :=
  pcOf_succ n

theorem pcOf_zero : pcOf 0 = 0 := rfl

/-- instruction-memory request/response payload for instruction `j` -/
def memEntry (j : Nat) : t_mem := { byte_en := 0, addr := pcOf j, data := 0 }
/-- data-memory request/response payload (always the same for instruction 0) -/
def dmemEntry : t_mem := { byte_en := 0, addr := 0, data := 0 }
def f2dEntry (j : Nat) : t_f2d := { pc := pcOf j, ppc := pcOf (j + 1), iEp := 0 }
def d2eEntry (j : Nat) : t_d2e :=
  { dInst := decodeInst 0, pc := pcOf j, ppc := pcOf (j + 1), iEp := 0, rv1 := 0, rv2 := 0 }
def e2wEntry (j : Nat) : t_e2w :=
  { memBusiness := { isUnsigned := BFalse Unit_, size := 0, offset := 0 },
    pc := pcOf j, data := 0, dInst := decodeInst 0 }
def commitAt (j : Nat) : t_commitinst := { pc := pcOf j, inst := 0, rd := 0, data := 0 }

/-- spec state after `c` commits -/
def specAt (c : Nat) : M_mktop_pipelined.Spec.State :=
  { pc := pcOf c, halted := if c = 0 then 0 else 1, rf := #[], imem := #[], dmem := #[] }

theorem specAt_zero : specAt 0 = default := rfl

/-- occupancy count of a 4-position stage -/
def occ (v : Fin 4) : Nat := if v = 0 then 0 else 1

@[simp] theorem occ0 : occ 0 = 0 := rfl
@[simp] theorem occ1 : occ 1 = 1 := rfl
@[simp] theorem occ2 : occ 2 = 1 := rfl
@[simp] theorem occ3 : occ 3 = 1 := rfl

theorem fin4_cases : ∀ v : Fin 4, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by decide

-- closed Fin-4 comparisons, so occupancy flags reduce after case analysis
@[simp] theorem fq01 : ((0 : Fin 4) == 1) = false := rfl
@[simp] theorem fq02 : ((0 : Fin 4) == 2) = false := rfl
@[simp] theorem fq03 : ((0 : Fin 4) == 3) = false := rfl
@[simp] theorem fq11 : ((1 : Fin 4) == 1) = true := rfl
@[simp] theorem fq12 : ((1 : Fin 4) == 2) = false := rfl
@[simp] theorem fq13 : ((1 : Fin 4) == 3) = false := rfl
@[simp] theorem fq21 : ((2 : Fin 4) == 1) = false := rfl
@[simp] theorem fq22 : ((2 : Fin 4) == 2) = true := rfl
@[simp] theorem fq23 : ((2 : Fin 4) == 3) = false := rfl
@[simp] theorem fq31 : ((3 : Fin 4) == 1) = false := rfl
@[simp] theorem fq32 : ((3 : Fin 4) == 2) = false := rfl
@[simp] theorem fq33 : ((3 : Fin 4) == 3) = true := rfl
@[simp] theorem fn0 : ((0 : Fin 4) != 0) = false := rfl
@[simp] theorem fn1 : ((1 : Fin 4) != 0) = true := rfl
@[simp] theorem fn2 : ((2 : Fin 4) != 0) = true := rfl
@[simp] theorem fn3 : ((3 : Fin 4) != 0) = true := rfl
@[simp] theorem fne1 : ((1 : Fin 4) ≠ 0) = True := by simp
@[simp] theorem fne2 : ((2 : Fin 4) ≠ 0) = True := by simp
@[simp] theorem fne3 : ((3 : Fin 4) ≠ 0) = True := by simp

/--
Invariant of the reachable states of the pipelined implementation started
from `default`, all of whose in-flight instructions are 0x00000000.

* `c`  : number of commits already emitted through the method
* `r`  : `retiredInst` holds commit `c`
* `w`  : e2w / data-memory round-trip stage:
         0 = empty, 1 = e2w + toDmem, 2 = e2w + dreq, 3 = e2w + fromDmem
* `x`  : d2e holds an instruction
* `fe` : front-end stage:
         0 = empty, 1 = f2d + toImem, 2 = f2d + ireq, 3 = f2d + fromImem
-/
structure Inv (c : Nat) (r : Bool) (w : Fin 4) (x : Bool) (fe : Fin 4)
    (i : M_mktop_pipelined.state) : Prop where
  pc_eq  : i.pc = pcOf (c + r.toNat + occ w + x.toNat + occ fe)
  ep_eq  : i.ep = 0
  rf_eq  : i.rf = #[]
  sb_eq  : i.sb = #[]
  imem_eq : i.iMem = { memory := #[], readResult := 0 }
  dmem_eq : i.dMem = { memory := #[], readResult := 0 }
  -- front-end (instruction index c + r + occ w + x)
  f2d_h  : i.f2d.hasElement = (fe != 0)
  f2d_e  : fe ≠ 0 → i.f2d.element = f2dEntry (c + r.toNat + occ w + x.toNat)
  toI_h  : i.toImem.hasElement = (fe == 1)
  toI_e  : fe = 1 → i.toImem.element = memEntry (c + r.toNat + occ w + x.toNat)
  irq_h  : i.ireq.hasElement = (fe == 2)
  irq_e  : fe = 2 → i.ireq.element = memEntry (c + r.toNat + occ w + x.toNat)
  frI_h  : i.fromImem.hasElement = (fe == 3)
  frI_e  : fe = 3 → i.fromImem.element = memEntry (c + r.toNat + occ w + x.toNat)
  -- d2e (instruction index c + r + occ w)
  d2e_h  : i.d2e.hasElement = x
  d2e_e  : x = true → i.d2e.element = d2eEntry (c + r.toNat + occ w)
  -- e2w and data-memory round trip (instruction index c + r)
  e2w_h  : i.e2w.hasElement = (w != 0)
  e2w_e  : w ≠ 0 → i.e2w.element = e2wEntry (c + r.toNat)
  toD_h  : i.toDmem.hasElement = (w == 1)
  toD_e  : w = 1 → i.toDmem.element = dmemEntry
  drq_h  : i.dreq.hasElement = (w == 2)
  drq_e  : w = 2 → i.dreq.element = dmemEntry
  frD_h  : i.fromDmem.hasElement = (w == 3)
  frD_e  : w = 3 → i.fromDmem.element = dmemEntry
  -- retired instruction (commit index c)
  ri_eq  : i.retiredInst = if r then Valid (commitAt c) else Invalid Unit_

theorem inv_default : Inv 0 false 0 false 0 (default : M_mktop_pipelined.state) := by
  constructor <;> first | rfl | (intro h; exact absurd h (by decide))

-- ═══════════ 3. rule preservation ═══════════

theorem preserve_fetch {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_fetch i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases fe with rfl | rfl | rfl | rfl
  · -- fe = 0 : the rule fires
    refine ⟨r, w, x, 1, ?_⟩
    unfold rule_RL_fetch at hr
    simp only [M_mkFIFO.meth_RDY_enq, M_mkFIFO.meth_enq, hf2dH, htoIH,
      fn0, fq01, Bool.false_eq_true, if_false, bool_and_true_l] at hr
    rw [Prod.mk.injEq] at hr
    obtain ⟨-, hi'⟩ := hr
    subst hi'
    constructor <;>
      simp_all [f2dEntry, memEntry, occ]
  all_goals {
    -- fe ≠ 0 : f2d is full, the guard is false
    exfalso
    unfold rule_RL_fetch at hr
    simp only [M_mkFIFO.meth_RDY_enq, hf2dH, fn1, fn2, fn3, if_true,
      bool_and_false_r] at hr
    simp at hr
  }

private theorem requestI_default_bv : (default : BitVec 32) = 0 := rfl

theorem preserve_requestI {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_requestI i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases fe with rfl | rfl | rfl | rfl
  · -- fe = 0 : toImem is empty, the guard is false
    exfalso
    unfold rule_RL_requestI at hr
    simp only [M_mkFIFO.meth_RDY_deq, htoIH, fq01, Bool.false_eq_true, if_false,
      bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  · -- fe = 1 : the rule fires
    refine ⟨r, w, x, 2, ?_⟩
    have htoIE' := htoIE rfl
    unfold rule_RL_requestI at hr
    simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_enq, M_mkFIFO.meth_RDY_first,
      M_mkSimpleBRAM.meth_RDY_put, htoIH, hirqH, fq11, fq12, if_true,
      Bool.false_eq_true, if_false, bool_and_true_l] at hr
    rw [Prod.mk.injEq] at hr
    obtain ⟨-, hi'⟩ := hr
    subst hi'
    constructor <;>
      simp_all [M_mkFIFO.meth_deq, M_mkFIFO.meth_enq, M_mkFIFO.meth_first,
        M_mkSimpleBRAM.meth_put, memEntry, occ, requestI_default_bv]
  all_goals {
    -- fe = 2 or 3 : toImem is empty, the guard is false
    exfalso
    unfold rule_RL_requestI at hr
    simp only [M_mkFIFO.meth_RDY_deq, htoIH, fq21, fq31, Bool.false_eq_true, if_false,
      bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  }

theorem preserve_responseI {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_responseI i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases fe with rfl | rfl | rfl | rfl
  · -- fe = 0 : ireq is empty, the guard is false
    exfalso
    unfold rule_RL_responseI at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hirqH, fq02,
      Bool.false_eq_true, if_false, bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  · -- fe = 1 : ireq is empty, the guard is false
    exfalso
    unfold rule_RL_responseI at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hirqH, fq12,
      Bool.false_eq_true, if_false, bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  · -- fe = 2 : the rule fires
    refine ⟨r, w, x, 3, ?_⟩
    unfold rule_RL_responseI at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkSimpleBRAM.meth_read,
      M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
      M_mkFIFO.meth_deq, M_mkFIFO.meth_enq, M_mkFIFO.meth_first,
      hirqH, hfrIH, fq22, fq23, if_true, Bool.false_eq_true, if_false,
      bool_and_true_l, ActionValue] at hr
    rw [Prod.mk.injEq] at hr
    obtain ⟨-, hi'⟩ := hr
    subst hi'
    constructor <;> simp_all [memEntry, occ]
  · -- fe = 3 : ireq is empty, the guard is false
    exfalso
    unfold rule_RL_responseI at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hirqH, fq32,
      Bool.false_eq_true, if_false, bool_and_true_l, bool_and_false_l] at hr
    simp at hr

private theorem decode_default_bv2 : (default : BitVec 2) = 0 := rfl

theorem preserve_decode {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_decode i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases fe with rfl | rfl | rfl | rfl
  · -- fe = 0 : fromImem empty, guard is false
    exfalso
    unfold rule_RL_decode at hr
    simp only [M_mkFIFO.meth_RDY_deq, hfrIH, fq03, Bool.false_eq_true, if_false,
      bool_and_false_l, bool_and_false_r] at hr
    simp at hr
  · -- fe = 1 : fromImem empty, guard is false
    exfalso
    unfold rule_RL_decode at hr
    simp only [M_mkFIFO.meth_RDY_deq, hfrIH, fq13, Bool.false_eq_true, if_false,
      bool_and_false_l, bool_and_false_r] at hr
    simp at hr
  · -- fe = 2 : fromImem empty, guard is false
    exfalso
    unfold rule_RL_decode at hr
    simp only [M_mkFIFO.meth_RDY_deq, hfrIH, fq23, Bool.false_eq_true, if_false,
      bool_and_false_l, bool_and_false_r] at hr
    simp at hr
  · -- fe = 3
    obtain ⟨iMem, dMem, ireq, dreq, toImem, fromImem, toDmem, fromDmem,
      f2d, d2e, e2w, retiredInst, pc, ep, rf, sb⟩ := i
    obtain ⟨f2dH, f2dEl⟩ := f2d
    obtain ⟨frIH, frIEl⟩ := fromImem
    obtain ⟨d2eH, d2eEl⟩ := d2e
    have hf2dH' : f2dH = true := hf2dH
    have hfrIH' : frIH = true := hfrIH
    have hf2dEl' : f2dEl = f2dEntry (c + r.toNat + occ w + x.toNat) := hf2dE (by decide)
    have hfrIEl' : frIEl = memEntry (c + r.toNat + occ w + x.toNat) := hfrIE rfl
    have hep' : ep = 0 := hep
    have hsb' : sb = #[] := hsb
    have hrf' : rf = #[] := hrf
    subst hf2dH' hfrIH' hf2dEl' hfrIEl' hep' hsb' hrf'
    cases x with
    | false =>
      -- d2e empty : the rule fires
      have hd2eH' : d2eH = false := hd2eH
      subst hd2eH'
      refine ⟨r, w, true, 0, ?_⟩
      have h2 :
          ({ iMem := iMem, dMem := dMem, ireq := ireq, dreq := dreq, toImem := toImem,
             fromImem := { hasElement := false, element := memEntry (c + r.toNat + occ w) },
             toDmem := toDmem, fromDmem := fromDmem,
             f2d := { hasElement := false, element := f2dEntry (c + r.toNat + occ w) },
             d2e := { hasElement := true, element := d2eEntry (c + r.toNat + occ w) },
             e2w := e2w, retiredInst := retiredInst, pc := pc, ep := 0, rf := #[],
             sb := #[] } : state) = i' := by
        set_option maxRecDepth 100000 in
        with_unfolding_all exact congrArg Prod.snd hr
      subst h2
      constructor <;>
        simp_all [d2eEntry, f2dEntry, memEntry, occ]
    | true =>
      -- d2e full : guard is false
      have hd2eH' : d2eH = true := hd2eH
      subst hd2eH'
      exfalso
      unfold rule_RL_decode at hr
      simp [M_mkFIFO.meth_first, M_mkFIFO.meth_RDY_enq, M_mkFIFO.meth_RDY_deq,
        M_mkFIFO.meth_RDY_first, f2dEntry, memEntry, decode_default_bv2,
        bool_to_bitvec1, bitvec1_to_bool, bit_and, bit_or, bit_not] at hr

-- closed-form facts used while reducing rule_RL_execute on instruction 0.
-- The match discriminants of the rule are in dependent positions (they carry
-- `h : _ = _` equations), so simp cannot rewrite inside them; instead we `rw`
-- them wholesale to literal constructors with the D-lemmas below, after which
-- simp's iota reduction picks the branch.
private theorem execute_D1 (j : Nat) :
    bool_not (if ((d2eEntry j).iEp == (0 : BitVec 1)) then BTrue Unit_ else BFalse Unit_)
      = BFalse Unit_ := rfl
private theorem execute_D2 (j : Nat) :
    isMemoryInst (d2eEntry j).dInst = BTrue Unit_ := isMem0
private theorem execute_e55 :
    (extract_bits (0 : BitVec 32) 5 5 == 1) = false := by decide
private theorem execute_D3 (j : Nat) :
    (if (extract_bits (d2eEntry j).dInst.inst 5 5 == 1) then BTrue Unit_ else BFalse Unit_)
      = BFalse Unit_ := by
  simp only [d2eEntry, decode0_inst, execute_e55, Bool.false_eq_true, if_false]
private theorem execute_add00 : (0 : BitVec 32) + 0 = 0 := by decide
private theorem execute_ex10_32 : extract_bits (0 : BitVec 32) 1 0 = (0 : BitVec 2) := by
  decide
private theorem execute_ex10_f3 : extract_bits (0 : BitVec 3) 1 0 = (0 : BitVec 2) := by
  decide
private theorem execute_addr :
    concat_bits (extract_bits (0 : BitVec 32) 31 2) 2 (0 : BitVec 2) = (0 : BitVec 32) := by
  decide
private theorem execute_shl5 :
    shift_left (0 : BitVec 32) (concat_bits (0 : BitVec 2) 3 (0 : BitVec 3))
      = (0 : BitVec 32) := by decide
private theorem execute_isU :
    bitvec1_to_bool (extract_bits (0 : BitVec 3) 2 2) = BFalse Unit_ := rfl

theorem preserve_execute {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_execute i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  cases x with
  | false =>
    -- d2e is empty : RDY_deq d2e is false, the guard collapses
    exfalso
    unfold rule_RL_execute at hr
    simp only [M_mkFIFO.meth_RDY_deq, hd2eH, Bool.false_eq_true, if_false,
      bool_and_false_l, bool_and_false_r] at hr
    simp at hr
  | true =>
    have hel := hd2eE rfl
    rcases fin4_cases w with rfl | rfl | rfl | rfl
    · -- w = 0 : the rule fires, moving the instruction from d2e to e2w + toDmem
      refine ⟨r, 1, false, fe, ?_⟩
      have hfirst : M_mkFIFO.meth_first i.d2e = d2eEntry (c + r.toNat) := by
        simp only [M_mkFIFO.meth_first]
        simpa using hel
      unfold rule_RL_execute at hr
      rw [hfirst, hep, execute_D1, execute_D2, execute_D3] at hr
      simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
        M_mkFIFO.meth_deq, M_mkFIFO.meth_enq,
        hd2eH, htoDH, he2wH, hsb, d2eEntry,
        fq01, fn0, Bool.false_eq_true, if_false, if_true,
        decode0_inst, imm0, fields0_funct3, bool_and_true_r,
        execute_add00, execute_ex10_32, execute_ex10_f3,
        execute_addr, execute_shl5, execute_isU, tuple2] at hr
      rw [Prod.mk.injEq] at hr
      obtain ⟨-, hi'⟩ := hr
      subst hi'
      constructor <;>
        simp_all [f2dEntry, memEntry, d2eEntry, e2wEntry, dmemEntry, commitAt, occ]
    · -- w = 1 : toDmem (and e2w) full, the guard collapses
      exfalso
      have hfirst : M_mkFIFO.meth_first i.d2e = d2eEntry (c + r.toNat + 1) := by
        simp only [M_mkFIFO.meth_first]
        simpa using hel
      unfold rule_RL_execute at hr
      rw [hfirst, hep, execute_D1, execute_D2, execute_D3] at hr
      simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
        hd2eH, htoDH, he2wH,
        fq11, fn1, if_true,
        bool_and_true_r, bool_and_false_r] at hr
      simp at hr
    · -- w = 2 : e2w full, the guard collapses
      exfalso
      have hfirst : M_mkFIFO.meth_first i.d2e = d2eEntry (c + r.toNat + 1) := by
        simp only [M_mkFIFO.meth_first]
        simpa using hel
      unfold rule_RL_execute at hr
      rw [hfirst, hep, execute_D1, execute_D2, execute_D3] at hr
      simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
        hd2eH, htoDH, he2wH,
        fq21, fn2, Bool.false_eq_true, if_false, if_true,
        bool_and_true_r, bool_and_false_r] at hr
      simp at hr
    · -- w = 3 : e2w full, the guard collapses
      exfalso
      have hfirst : M_mkFIFO.meth_first i.d2e = d2eEntry (c + r.toNat + 1) := by
        simp only [M_mkFIFO.meth_first]
        simpa using hel
      unfold rule_RL_execute at hr
      rw [hfirst, hep, execute_D1, execute_D2, execute_D3] at hr
      simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
        hd2eH, htoDH, he2wH,
        fq31, fn3, Bool.false_eq_true, if_false, if_true,
        bool_and_true_r, bool_and_false_r] at hr
      simp at hr

private theorem preserve_requestD_default_bv : (default : BitVec 32) = 0 := rfl

theorem preserve_requestD {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_requestD i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases w with rfl | rfl | rfl | rfl
  · -- w = 0 : toDmem empty, the guard is false
    exfalso
    unfold rule_RL_requestD at hr
    simp only [M_mkFIFO.meth_RDY_deq, htoDH, fq01, Bool.false_eq_true, if_false,
      bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  · -- w = 1 : the rule fires, request moves toDmem → dreq, dMem gets a read-put
    refine ⟨r, 2, x, fe, ?_⟩
    unfold rule_RL_requestD at hr
    simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_RDY_enq,
      M_mkSimpleBRAM.meth_RDY_put, htoDH, hdrqH, fq11, fq12, if_true,
      Bool.false_eq_true, if_false, bool_and_true_r] at hr
    rw [Prod.mk.injEq] at hr
    obtain ⟨-, hi'⟩ := hr
    subst hi'
    constructor <;>
      simp_all [M_mkFIFO.meth_deq, M_mkFIFO.meth_enq, M_mkFIFO.meth_first,
        M_mkSimpleBRAM.meth_put, dmemEntry, occ, preserve_requestD_default_bv]
  all_goals {
    -- w = 2, 3 : toDmem empty, the guard is false
    exfalso
    unfold rule_RL_requestD at hr
    simp only [M_mkFIFO.meth_RDY_deq, htoDH, fq21, fq31, Bool.false_eq_true, if_false,
      bool_and_true_l, bool_and_false_l] at hr
    simp at hr
  }

theorem preserve_responseD {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_responseD i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  rcases fin4_cases w with rfl | rfl | rfl | rfl
  · -- w = 0 : dreq is empty, the guard is false
    exfalso
    unfold rule_RL_responseD at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hdrqH, fq02,
      Bool.false_eq_true, if_false, bool_and_false_l,
      bool_and_false_r] at hr
    simp at hr
  · -- w = 1 : dreq is empty, the guard is false
    exfalso
    unfold rule_RL_responseD at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hdrqH, fq12,
      Bool.false_eq_true, if_false, bool_and_false_l,
      bool_and_false_r] at hr
    simp at hr
  · -- w = 2 : the rule fires, response moves from dreq to fromDmem
    refine ⟨r, 3, x, fe, ?_⟩
    unfold rule_RL_responseD at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq,
      M_mkFIFO.meth_RDY_enq, M_mkFIFO.meth_RDY_first, hdrqH, hfrDH, fq22, fq23,
      Bool.false_eq_true, if_false, if_true, bool_and_true_r,
      M_mkFIFO.meth_deq, M_mkFIFO.meth_enq, M_mkFIFO.meth_first,
      M_mkSimpleBRAM.meth_read, ActionValue] at hr
    rw [Prod.mk.injEq] at hr
    obtain ⟨-, hi'⟩ := hr
    subst hi'
    constructor <;> simp_all [dmemEntry, occ]
  · -- w = 3 : dreq is empty, the guard is false
    exfalso
    unfold rule_RL_responseD at hr
    simp only [M_mkSimpleBRAM.meth_RDY_read, M_mkFIFO.meth_RDY_deq, hdrqH, fq32,
      Bool.false_eq_true, if_false, bool_and_false_l,
      bool_and_false_r] at hr
    simp at hr

-- closed-form facts used while reducing rule_RL_writeback on instruction 0 (same
-- technique as for rule_RL_execute: rewrite the dependent match discriminants to
-- literal constructors, then let simp pick the branch).

private theorem wb_D_mem (j : Nat) : isMemoryInst (e2wEntry j).dInst = BTrue Unit_ := isMem0

private theorem wb_D_wr (j : Nat) :
    bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (e2wEntry j).dInst.valid_rd)
      (bool_to_bitvec1 (e2wEntry j).dInst.legal))
      (bool_to_bitvec1 (bool_not (if (((getInstFields (e2wEntry j).dInst.inst).rd == (0 : BitVec 5)))
        then BTrue Unit_ else BFalse Unit_)))) = BFalse Unit_ := by
  simp only [e2wEntry]; with_unfolding_all rfl

private theorem wb_D_vrd (j : Nat) :
    bitvec1_to_bool (bool_to_bitvec1 (e2wEntry j).dInst.valid_rd) = BTrue Unit_ := by
  simp only [e2wEntry]; with_unfolding_all rfl

private theorem wb_D_sz0 (j : Nat) :
    (if ((concat_bits (bool_to_bitvec1 (e2wEntry j).memBusiness.isUnsigned) 2
        (e2wEntry j).memBusiness.size == (0 : BitVec 3))) then BTrue Unit_ else BFalse Unit_)
      = BTrue Unit_ := by
  simp only [e2wEntry]; with_unfolding_all rfl

private theorem wb_data0 (j : Nat) :
    (sign_extend (extract_bits (shift_right_logical dmemEntry.data
      (concat_bits (e2wEntry j).memBusiness.offset 3 (0 : BitVec 3))) 7 0) : BitVec 32) = 0 := by
  simp only [e2wEntry, dmemEntry]; decide

-- the same closed facts, in the literal form produced by `simp`'s BitVec normalisation
private theorem wb_decode0_inst : (decodeInst (BitVec.ofNat 32 0)).inst = BitVec.ofNat 32 0 := rfl
private theorem wb_fields0_rd : (getInstFields (BitVec.ofNat 32 0)).rd = BitVec.ofNat 5 0 := rfl

theorem preserve_writeback {c r w x fe i i'}
    (h : Inv c r w x fe i) (hr : rule_RL_writeback i = (BTrue Unit_, i')) :
    ∃ r' w' x' fe', Inv c r' w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  cases r with
  | true =>
    -- retiredInst is full : the guard is false
    exfalso
    simp only [if_true] at hri
    unfold rule_RL_writeback at hr
    rw [hri] at hr
    simp only [bool_and_false_l] at hr
    simp at hr
  | false =>
    simp only [Bool.false_eq_true, if_false] at hri
    rcases fin4_cases w with rfl | rfl | rfl | rfl
    · -- w = 0 : e2w empty
      exfalso
      unfold rule_RL_writeback at hr
      rw [hri] at hr
      simp only [M_mkFIFO.meth_RDY_deq, he2wH, fn0, Bool.false_eq_true, if_false,
        bool_and_true_l, bool_and_false_l] at hr
      simp at hr
    · -- w = 1 : fromDmem empty
      exfalso
      have hfirst : M_mkFIFO.meth_first i.e2w = e2wEntry c := by
        simp only [M_mkFIFO.meth_first]; simpa using he2wE (by decide)
      unfold rule_RL_writeback at hr
      rw [hri, hfirst, wb_D_mem] at hr
      simp only [M_mkFIFO.meth_RDY_deq, he2wH, hfrDH, fn1, fq13, if_true,
        Bool.false_eq_true, if_false, bool_and_true_l, bool_and_false_l] at hr
      simp at hr
    · -- w = 2 : fromDmem empty
      exfalso
      have hfirst : M_mkFIFO.meth_first i.e2w = e2wEntry c := by
        simp only [M_mkFIFO.meth_first]; simpa using he2wE (by decide)
      unfold rule_RL_writeback at hr
      rw [hri, hfirst, wb_D_mem] at hr
      simp only [M_mkFIFO.meth_RDY_deq, he2wH, hfrDH, fn2, fq23, if_true,
        Bool.false_eq_true, if_false, bool_and_true_l, bool_and_false_l] at hr
      simp at hr
    · -- w = 3 : the rule fires
      refine ⟨true, 0, x, fe, ?_⟩
      have hfirst : M_mkFIFO.meth_first i.e2w = e2wEntry c := by
        simp only [M_mkFIFO.meth_first]; simpa using he2wE (by decide)
      have hfirstD : M_mkFIFO.meth_first i.fromDmem = dmemEntry := by
        simp only [M_mkFIFO.meth_first]; simpa using hfrDE rfl
      unfold rule_RL_writeback at hr
      rw [hri, hfirst, hfirstD, wb_D_mem, wb_D_wr, wb_D_vrd, wb_D_sz0] at hr
      simp only [M_mkFIFO.meth_RDY_deq, M_mkFIFO.meth_RDY_first, M_mkFIFO.meth_deq,
        he2wH, hfrDH, hrf, hsb, fn3, fq33, if_true, bool_and_true_r,
        arr_set_nil, wb_data0] at hr
      rw [Prod.mk.injEq] at hr
      obtain ⟨-, hi'⟩ := hr
      subst hi'
      constructor <;>
        simp_all [f2dEntry, memEntry, d2eEntry, e2wEntry, dmemEntry, commitAt, occ,
          wb_decode0_inst, wb_fields0_rd]


-- ═══════════ 4. the method, on both sides ═══════════

/-- The implementation can only emit a commit event when `retiredInst` is full,
    and the event payload is exactly `commitAt c`. -/
theorem impl_method {c r w x fe i i' v} {fp : Footprint}
    (h : Inv c r w x fe i)
    (hv : meth_getCommitInst i = ⟨v, i'⟩)
    (hfp : fp = Footprint.arg0 v)
    (hrdy : meth_RDY_getCommitInst i = BTrue Unit_) :
    r = true ∧ v = commitAt c ∧ fp = Footprint.arg0 (commitAt c)
      ∧ ∃ w' x' fe', Inv (c + 1) false w' x' fe' i' := by
  obtain ⟨hpc, hep, hrf, hsb, hiM, hdM, hf2dH, hf2dE, htoIH, htoIE, hirqH, hirqE,
    hfrIH, hfrIE, hd2eH, hd2eE, he2wH, he2wE, htoDH, htoDE, hdrqH, hdrqE,
    hfrDH, hfrDE, hri⟩ := h
  cases r
  · -- r = false : retiredInst is Invalid, so RDY_getCommitInst is BFalse — absurd
    simp only [Bool.false_eq_true, if_false] at hri
    simp [meth_RDY_getCommitInst, hri] at hrdy
  · -- r = true : retiredInst = Valid (commitAt c)
    simp only [if_true] at hri
    simp only [meth_getCommitInst, hri] at hv
    rw [t_actionvalue_.mk.injEq] at hv
    obtain ⟨hveq, hi'⟩ := hv
    subst hi'
    subst hveq
    refine ⟨rfl, rfl, hfp, w, x, fe, ?_⟩
    constructor <;> simp_all

/-- The spec's one deterministic step from `specAt c`. -/
theorem spec_step (c : Nat) :
    M_mktop_pipelined.Spec.stepOne (specAt c) = (specAt (c + 1), commitAt c) := by
  unfold M_mktop_pipelined.Spec.stepOne
  simp only [specAt]
  split
  · -- the decoded instruction is 0x00000000, which is illegal: contradiction
    next a heq =>
      simp only [getD_nil, show (default : BitVec 32) = 0#32 from rfl,
        show (decodeInst (0#32)).legal = BFalse Unit_ from rfl] at heq
      exact t_bool.noConfusion heq
  · -- illegal branch: pc advances by 4, machine halts, commit is `commitAt c`
    simp [commitAt, show (default : BitVec 32) = 0#32 from rfl,
      show (getInstFields (0#32)).rd = 0#5 from rfl]


def φ (i :ImplModule.State) (s : SpecModule.State) : Prop :=
  ∃ c r w x fe, Inv c r w x fe i ∧ s = specAt c

theorem phi_rule {i i' s} (h : φ i s) (hr : ImplModule.getARule i i') :
    φ i' s := by
  obtain ⟨c, r, w, x, fe, hInv, rfl⟩ := h
  obtain ⟨ru, hru⟩ := hr
  cases ru
  case RL_requestI =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_requestI hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_responseI =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_responseI hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_requestD =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_requestD hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_responseD =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_responseD hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_fetch =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_fetch hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_decode =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_decode hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_execute =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_execute hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩
  case RL_writeback =>
    obtain ⟨r', w', x', fe', h'⟩ := preserve_writeback hInv hru
    exact ⟨c, r', w', x', fe', h', rfl⟩

theorem phi_trans_refl {i i' s} (h : φ i s)
    (ht : trans_refl ImplModule.getARule i i') : φ i' s := by
  induction ht with
  | refl => exact h
  | step hab _ ih => exact ih (phi_rule h hab)

theorem phi_method {i i' s e} (h : φ i s)
    (hm : ImplModule.getMethod i e i') :
    ∃ s', SpecModule.getMethod s e s' ∧ φ i' s' := by
  obtain ⟨c, r, w, x, fe, hInv, rfl⟩ := h
  obtain ⟨name, fp⟩ := e
  cases name
  obtain ⟨v, hv, hfp, hrdy⟩ := hm
  obtain ⟨-, -, hfpc, w', x', fe', hInv'⟩ := impl_method hInv hv hfp hrdy
  refine ⟨specAt (c + 1), ⟨commitAt c, ?_, hfpc, rfl⟩,
    c + 1, false, w', x', fe', hInv', rfl⟩
  show M_mktop_pipelined.Spec.meth_getCommit (specAt c) = _
  simp [M_mktop_pipelined.Spec.meth_getCommit, spec_step c]




theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event1 Method)} :
  φ i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
    ∃ s', star SpecModule.getMethod s l s'
         ∧ φ i' s' := by
  intro hφ hstar
  induction hstar with
  | refl => exact ⟨s, star.refl s, hφ⟩
  | step_int _ _ _ hse ht ih =>
    obtain ⟨s', hs', hφ'⟩ := ih
    exact ⟨s', hs', phi_trans_refl hφ' ht⟩
  | step_ext _ _ _ _ hse hm ih =>
    obtain ⟨s₁, hs₁, hφ₁⟩ := ih
    obtain ⟨s₂, hspec, hφ₂⟩ := phi_method hφ₁ hm
    exact ⟨s₂, star.step _ _ _ _ _ hs₁ hspec, hφ₂⟩

instance : Inhabited ImplModule.State :=
  inferInstanceAs (Inhabited M_mktop_pipelined.state)

instance : Inhabited SpecModule.State :=
  inferInstanceAs (Inhabited M_mktop_pipelined.Spec.State)

theorem initial_phi :
  φ default default := by
  exact ⟨0, false, 0, false, 0, inv_default, specAt_zero.symm⟩

#print axioms refines
#print axioms initial_phi

end M_mktop_pipelined.Refines
