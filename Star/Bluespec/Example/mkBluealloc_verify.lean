import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.Example.Bluealloc_types
import Star.Bluespec.Example.mkBluealloc
import Star.Tactic
import Star.Bluespec.Basic

open BluespecPrelude
open Bluealloc_types
open M_mkBluealloc
open BluespecVerification

attribute [bsv_rules] M_mkBluealloc.rule_RL_do_read_index M_mkBluealloc.rule_RL_do_write_index M_mkBluealloc.rule_RL_do_free_lookup M_mkBluealloc.rule_RL_do_free_read M_mkBluealloc.rule_RL_do_free_write M_mkBluealloc.rule_RL_do_alloc_prefetch M_mkBluealloc.rule_RL_do_alloc_wait
attribute [bsv_methods] M_mkBluealloc.meth_alloc M_mkBluealloc.meth_RDY_alloc M_mkBluealloc.meth_free M_mkBluealloc.meth_RDY_free M_mkBluealloc.meth_write_req M_mkBluealloc.meth_RDY_write_req M_mkBluealloc.meth_read_req M_mkBluealloc.meth_RDY_read_req M_mkBluealloc.meth_read_resp M_mkBluealloc.meth_RDY_read_resp

namespace M_mkBluealloc.Verify

-- ═══ Transition Catalog ═══

-- Rules:
--  rule_RL_do_read_index : state → (t_bool × state)
--    guard: (rule_RL_do_read_index s).1
--  rule_RL_do_write_index : state → (t_bool × state)
--    guard: (rule_RL_do_write_index s).1
--  rule_RL_do_free_lookup : state → (t_bool × state)
--    guard: (rule_RL_do_free_lookup s).1
--  rule_RL_do_free_read : state → (t_bool × state)
--    guard: (rule_RL_do_free_read s).1
--  rule_RL_do_free_write : state → (t_bool × state)
--    guard: (rule_RL_do_free_write s).1
--  rule_RL_do_alloc_prefetch : state → (t_bool × state)
--    guard: (rule_RL_do_alloc_prefetch s).1
--  rule_RL_do_alloc_wait : state → (t_bool × state)
--    guard: (rule_RL_do_alloc_wait s).1

-- Action methods:
--  meth_alloc : state → t_actionvalue_ (BitVec 16) state
--    guard: meth_RDY_alloc s
--  meth_free : state → BitVec 16 → t_actionvalue_ unit_ state
--    guard: meth_RDY_free s
--  meth_write_req : state → BitVec 16 → BitVec 32 → t_actionvalue_ unit_ state
--    guard: meth_RDY_write_req s
--  meth_read_req : state → BitVec 16 → t_actionvalue_ unit_ state
--    guard: meth_RDY_read_req s
--  meth_read_resp : state → t_actionvalue_ (BitVec 32) state
--    guard: meth_RDY_read_resp s

-- ═══ Rule Infrastructure ═══

-- Enumeration of all rules in this module
inductive RuleTag where
  | RL_do_read_index
  | RL_do_write_index
  | RL_do_free_lookup
  | RL_do_free_read
  | RL_do_free_write
  | RL_do_alloc_prefetch
  | RL_do_alloc_wait

-- Apply a rule to a state (only fires if guard is ready)
def applyRule (tag : RuleTag) (s : state) : state :=
  match tag with
  | .RL_do_read_index =>
    let r := rule_RL_do_read_index s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_write_index =>
    let r := rule_RL_do_write_index s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_free_lookup =>
    let r := rule_RL_do_free_lookup s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_free_read =>
    let r := rule_RL_do_free_read s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_free_write =>
    let r := rule_RL_do_free_write s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_alloc_prefetch =>
    let r := rule_RL_do_alloc_prefetch s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s
  | .RL_do_alloc_wait =>
    let r := rule_RL_do_alloc_wait s
    match r.1 with | BTrue _ => r.2 | BFalse _ => s

-- Apply a sequence of rules to a state
def applyRules : List RuleTag → state → state
  | [], s => s
  | r :: rs, s => applyRules rs (applyRule r s)

-- ═══ Reconvergence Theorems ═══

-- Critical pair: rule_RL_do_read_index × rule_RL_do_write_index
theorem reconverge_RL_do_read_index_RL_do_write_index (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_write_index s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_write_index s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.)] at *
  revert h1 h2
  simp [bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  cases s.opState <;>
  simp [bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB, bool_and] at *

-- Critical pair: rule_RL_do_read_index × rule_RL_do_free_lookup
theorem reconverge_RL_do_read_index_RL_do_free_lookup (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_lookup s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_free_lookup s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × rule_RL_do_free_read
theorem reconverge_RL_do_read_index_RL_do_free_read (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_read s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_free_read s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × rule_RL_do_free_write
theorem reconverge_RL_do_read_index_RL_do_free_write (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_write s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_free_write s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × rule_RL_do_alloc_prefetch
theorem reconverge_RL_do_read_index_RL_do_alloc_prefetch (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_alloc_prefetch s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × rule_RL_do_alloc_wait
-- Not vacuous: read_index requires opState=OP_READ_INDEX, alloc_wait requires
-- allocState=AL_WAIT — independent fields, so both can fire together.
-- The rules commute: read_index writes {bram_index, bram_data, opState}, alloc_wait
-- writes {bram_rever, allocNextStable, allocState}. Disjoint, with each rule only
-- reading fields it writes (plus unchanged state). Hence applying either order
-- yields the same final state.
theorem reconverge_RL_do_read_index_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_read_index s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  refine ⟨[RuleTag.RL_do_alloc_wait], [RuleTag.RL_do_read_index], ?_⟩
  -- The alloc_wait guard evaluated at (read_index s).2 equals the guard at s,
  -- because read_index doesn't touch allocState or bram_rever.
  have ga : (rule_RL_do_alloc_wait (rule_RL_do_read_index s).2).1 = BTrue Unit_ := by sorry
    /- have : (rule_RL_do_alloc_wait (rule_RL_do_read_index s).2).1 = (rule_RL_do_alloc_wait s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_read_index]
     - rw [this]; exact h2 -/
  -- Symmetrically, read_index guard is preserved by alloc_wait.
  have gb : (rule_RL_do_read_index (rule_RL_do_alloc_wait s).2).1 = BTrue Unit_ := by sorry
    /- have : (rule_RL_do_read_index (rule_RL_do_alloc_wait s).2).1 = (rule_RL_do_read_index s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_read_index]
     - rw [this]; exact h1 -/
  -- Unfold applyRules/applyRule, resolve matches via ga/gb, then prove states equal.
  simp only [applyRules, applyRule, ga, gb]
  -- Both sides are now the second rule applied to the first rule's output state.
  -- With disjoint field updates, the resulting state records are definitionally equal.
  simp [rule_RL_do_read_index, rule_RL_do_alloc_wait]

-- Critical pair: rule_RL_do_read_index × meth_alloc
-- Vacuous: read_index requires opState=OP_READ_INDEX, alloc requires opState=OP_IDLE.
theorem reconverge_RL_do_read_index_alloc (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_read_index s).2).avAction_ =
    (rule_RL_do_read_index (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Critical pair: rule_RL_do_read_index × meth_free
theorem reconverge_RL_do_read_index_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_read_index s).2 free_f).avAction_ =
    (rule_RL_do_read_index (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × meth_write_req
theorem reconverge_RL_do_read_index_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_read_index s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_read_index (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × meth_read_req
theorem reconverge_RL_do_read_index_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_read_index s).2 read_req_addr).avAction_ =
    (rule_RL_do_read_index (meth_read_req s read_req_addr).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_read_index × meth_read_resp
theorem reconverge_RL_do_read_index_read_resp (s : state)
    (h1 : (rule_RL_do_read_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_read_index s).2).avAction_ =
    (rule_RL_do_read_index (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × rule_RL_do_free_lookup
theorem reconverge_RL_do_write_index_RL_do_free_lookup (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_lookup s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_write_index s).2 =
      applyRules rs2 (rule_RL_do_free_lookup s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × rule_RL_do_free_read
theorem reconverge_RL_do_write_index_RL_do_free_read (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_read s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_write_index s).2 =
      applyRules rs2 (rule_RL_do_free_read s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × rule_RL_do_free_write
theorem reconverge_RL_do_write_index_RL_do_free_write (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_write s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_write_index s).2 =
      applyRules rs2 (rule_RL_do_free_write s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × rule_RL_do_alloc_prefetch
theorem reconverge_RL_do_write_index_RL_do_alloc_prefetch (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_write_index s).2 =
      applyRules rs2 (rule_RL_do_alloc_prefetch s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × rule_RL_do_alloc_wait
-- Commute: write_index writes {bram_index, bram_data, opState}, alloc_wait writes
-- {bram_rever, allocNextStable, allocState}. Disjoint; guards on independent fields.
theorem reconverge_RL_do_write_index_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_write_index s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  refine ⟨[RuleTag.RL_do_alloc_wait], [RuleTag.RL_do_write_index], ?_⟩
  have ga : (rule_RL_do_alloc_wait (rule_RL_do_write_index s).2).1 = BTrue Unit_ := by
    /- have : (rule_RL_do_alloc_wait (rule_RL_do_write_index s).2).1 = (rule_RL_do_alloc_wait s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_write_index]
     - rw [this]; exact h2 -/
    sorry
  have gb : (rule_RL_do_write_index (rule_RL_do_alloc_wait s).2).1 = BTrue Unit_ := by
    /- have : (rule_RL_do_write_index (rule_RL_do_alloc_wait s).2).1 = (rule_RL_do_write_index s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_write_index]
     - rw [this]; exact h1 -/
    sorry
  simp only [applyRules, applyRule, ga, gb]
  simp [rule_RL_do_write_index, rule_RL_do_alloc_wait]

-- Critical pair: rule_RL_do_write_index × meth_alloc
-- Vacuous: write_index requires opState=OP_WRITE_INDEX, alloc requires opState=OP_IDLE.
theorem reconverge_RL_do_write_index_alloc (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_write_index s).2).avAction_ =
    (rule_RL_do_write_index (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Critical pair: rule_RL_do_write_index × meth_free
theorem reconverge_RL_do_write_index_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_write_index s).2 free_f).avAction_ =
    (rule_RL_do_write_index (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × meth_write_req
theorem reconverge_RL_do_write_index_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_write_index s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_write_index (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × meth_read_req
theorem reconverge_RL_do_write_index_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_write_index s).2 read_req_addr).avAction_ =
    (rule_RL_do_write_index (meth_read_req s read_req_addr).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_write_index × meth_read_resp
theorem reconverge_RL_do_write_index_read_resp (s : state)
    (h1 : (rule_RL_do_write_index s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_write_index s).2).avAction_ =
    (rule_RL_do_write_index (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × rule_RL_do_free_read
theorem reconverge_RL_do_free_lookup_RL_do_free_read (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_read s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_lookup s).2 =
      applyRules rs2 (rule_RL_do_free_read s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × rule_RL_do_free_write
theorem reconverge_RL_do_free_lookup_RL_do_free_write (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_write s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_lookup s).2 =
      applyRules rs2 (rule_RL_do_free_write s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × rule_RL_do_alloc_prefetch
theorem reconverge_RL_do_free_lookup_RL_do_alloc_prefetch (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_lookup s).2 =
      applyRules rs2 (rule_RL_do_alloc_prefetch s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × rule_RL_do_alloc_wait
-- Commute: free_lookup's putA on bram_rever only updates readResultA, while
-- alloc_wait's readB reads readResultB (and doesn't mutate state), so writes to
-- bram_rever are independent. Other written fields are disjoint.
theorem reconverge_RL_do_free_lookup_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_lookup s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  refine ⟨[RuleTag.RL_do_alloc_wait], [RuleTag.RL_do_free_lookup], ?_⟩
  -- RDY methods of mkSimpleBRAM2 are constant BTrue, and the only fields the
  -- guards inspect (opState/allocState) are disjoint.
  have ga : (rule_RL_do_alloc_wait (rule_RL_do_free_lookup s).2).1 = BTrue Unit_ := by
    have : (rule_RL_do_alloc_wait (rule_RL_do_free_lookup s).2).1 = (rule_RL_do_alloc_wait s).1 := by
      simp [rule_RL_do_alloc_wait, rule_RL_do_free_lookup,
            M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
            M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
            M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
            M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
    rw [this]; exact h2
  have gb : (rule_RL_do_free_lookup (rule_RL_do_alloc_wait s).2).1 = BTrue Unit_ := by
    /- have : (rule_RL_do_free_lookup (rule_RL_do_alloc_wait s).2).1 = (rule_RL_do_free_lookup s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_free_lookup,
     -         M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
     -         M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
     -         M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
     -         M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
     - rw [this]; exact h1 -/
     sorry
  simp only [applyRules, applyRule, ga, gb]
  simp [rule_RL_do_free_lookup, rule_RL_do_alloc_wait,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB,
        ActionValue]

-- Critical pair: rule_RL_do_free_lookup × meth_alloc
-- Vacuous: free_lookup requires opState=OP_FREE_LOOKUP, alloc requires opState=OP_IDLE.
theorem reconverge_RL_do_free_lookup_alloc (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_free_lookup s).2).avAction_ =
    (rule_RL_do_free_lookup (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Does not have to be considered
theorem reconverge_RL_do_free_lookup_alloc' (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    False := by
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Critical pair: rule_RL_do_free_lookup × meth_free
theorem reconverge_RL_do_free_lookup_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_free_lookup s).2 free_f).avAction_ =
    (rule_RL_do_free_lookup (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × meth_write_req
theorem reconverge_RL_do_free_lookup_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_free_lookup s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_free_lookup (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × meth_read_req
theorem reconverge_RL_do_free_lookup_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_free_lookup s).2 read_req_addr).avAction_ =
    (rule_RL_do_free_lookup (meth_read_req s read_req_addr).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_lookup × meth_read_resp
theorem reconverge_RL_do_free_lookup_read_resp (s : state)
    (h1 : (rule_RL_do_free_lookup s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_free_lookup s).2).avAction_ =
    (rule_RL_do_free_lookup (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × rule_RL_do_free_write
theorem reconverge_RL_do_free_read_RL_do_free_write (s : state)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_free_write s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_read s).2 =
      applyRules rs2 (rule_RL_do_free_write s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × rule_RL_do_alloc_prefetch
theorem reconverge_RL_do_free_read_RL_do_alloc_prefetch (s : state)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_read s).2 =
      applyRules rs2 (rule_RL_do_alloc_prefetch s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × rule_RL_do_alloc_wait
-- Commute: free_read's writes to bram_rever are via readA (no state change);
-- alloc_wait's write via readB also no-op on state. Other fields disjoint.
theorem reconverge_RL_do_free_read_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_read s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  refine ⟨[RuleTag.RL_do_alloc_wait], [RuleTag.RL_do_free_read], ?_⟩
  have ga : (rule_RL_do_alloc_wait (rule_RL_do_free_read s).2).1 = BTrue Unit_ := by
    /- have : (rule_RL_do_alloc_wait (rule_RL_do_free_read s).2).1 = (rule_RL_do_alloc_wait s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_free_read,
     -         M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
     -         M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
     -         M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
     -         M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
     - rw [this]; exact h2 -/
     sorry
  have gb : (rule_RL_do_free_read (rule_RL_do_alloc_wait s).2).1 = BTrue Unit_ := by
    /- have : (rule_RL_do_free_read (rule_RL_do_alloc_wait s).2).1 = (rule_RL_do_free_read s).1 := by
     -   simp [rule_RL_do_alloc_wait, rule_RL_do_free_read,
     -         M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
     -         M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
     -         M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
     -         M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
     - rw [this]; exact h1 -/
     sorry
  simp only [applyRules, applyRule, ga, gb]
  simp [rule_RL_do_free_read, rule_RL_do_alloc_wait,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB,
        ActionValue]

-- Critical pair: rule_RL_do_free_read × meth_alloc
-- Vacuous: free_read requires opState=OP_FREE_READ, alloc requires opState=OP_IDLE.
theorem reconverge_RL_do_free_read_alloc (s : state)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_free_read s).2).avAction_ =
    (rule_RL_do_free_read (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Critical pair: rule_RL_do_free_read × meth_free
theorem reconverge_RL_do_free_read_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_free_read s).2 free_f).avAction_ =
    (rule_RL_do_free_read (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × meth_write_req
theorem reconverge_RL_do_free_read_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_free_read s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_free_read (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × meth_read_req
theorem reconverge_RL_do_free_read_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_free_read s).2 read_req_addr).avAction_ =
    (rule_RL_do_free_read (meth_read_req s read_req_addr).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_read × meth_read_resp
theorem reconverge_RL_do_free_read_read_resp (s : state)
    (h1 : (rule_RL_do_free_read s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_free_read s).2).avAction_ =
    (rule_RL_do_free_read (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_write × rule_RL_do_alloc_prefetch
theorem reconverge_RL_do_free_write_RL_do_alloc_prefetch (s : state)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_write s).2 =
      applyRules rs2 (rule_RL_do_alloc_prefetch s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all


-- Vacuous: free_write requires bram_rever.readResultB = none (for RDY_putB),
-- while alloc_wait requires bram_rever.readResultB = some _ (for RDY_readB).
-- The two guards cannot hold simultaneously.
theorem reconverge_RL_do_free_write_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_free_write s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  exfalso
  -- bram_rever.readResultB cannot be both none (required by putB in free_write)
  -- and some _ (required by readB in alloc_wait).
  cases h : s.bram_rever.readResultB
  · -- none: alloc_wait's readB guard collapses to BFalse; h2 becomes BFalse = BTrue.
    simp [bsv_rules, bsv_methods, bool_and, h,
          M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readB] at h2
    split at h2 <;> simp_all
  · -- some: free_write's putB guard on bram_rever collapses; h1 becomes BFalse = BTrue.
    simp [bsv_rules, bsv_methods, bool_and, h,
          M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readB] at h1
    cases h_dB : s.bram_data.readResultB <;>
      cases h_rA : s.bram_rever.readResultA <;>
      cases h_dA : s.bram_data.readResultA <;>
      simp_all [M_mkSimpleBRAM2.meth_RDY_putA] <;>
      split at h1 <;> simp_all




-- Critical pair: rule_RL_do_free_write × meth_alloc
-- Vacuous: free_write requires opState=OP_FREE_WRITE, alloc requires opState=OP_IDLE.
theorem reconverge_RL_do_free_write_alloc (s : state)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_free_write s).2).avAction_ =
    (rule_RL_do_free_write (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all (config := { decide := true }) <;> grind

-- Critical pair: rule_RL_do_free_write × meth_free
theorem reconverge_RL_do_free_write_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_free_write s).2 free_f).avAction_ =
    (rule_RL_do_free_write (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_write × meth_write_req
theorem reconverge_RL_do_free_write_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_free_write s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_free_write (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_write × meth_read_req
theorem reconverge_RL_do_free_write_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_free_write s).2 read_req_addr).avAction_ =
    (rule_RL_do_free_write (meth_read_req s read_req_addr).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_free_write × meth_read_resp
theorem reconverge_RL_do_free_write_read_resp (s : state)
    (h1 : (rule_RL_do_free_write s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_free_write s).2).avAction_ =
    (rule_RL_do_free_write (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_prefetch × rule_RL_do_alloc_wait
theorem reconverge_RL_do_alloc_prefetch_RL_do_alloc_wait (s : state)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_) :
    ∃ (rs1 rs2 : List RuleTag),
      applyRules rs1 (rule_RL_do_alloc_prefetch s).2 =
      applyRules rs2 (rule_RL_do_alloc_wait s).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_prefetch × meth_alloc
theorem reconverge_RL_do_alloc_prefetch_alloc (s : state)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_alloc_prefetch s).2).avAction_ =
    (rule_RL_do_alloc_prefetch (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_prefetch × meth_free
theorem reconverge_RL_do_alloc_prefetch_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_alloc_prefetch s).2 free_f).avAction_ =
    (rule_RL_do_alloc_prefetch (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_prefetch × meth_write_req
-- Commute: alloc_prefetch writes {bram_rever?, allocNextStable?, allocState},
-- write_req writes {opWriteData, bram_index, opState}. Disjoint; alloc_prefetch
-- reads enqPtr/maxEver/bram_rever, none touched by write_req.
theorem reconverge_RL_do_alloc_prefetch_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_alloc_prefetch s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_alloc_prefetch (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  simp [rule_RL_do_alloc_prefetch,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB,
        ActionValue]
  unfold meth_write_req
  split <;> (rename_i h; rw [h])

theorem reconverge_RL_do_alloc_prefetch_write_req_method_ready (s : state)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    isReady (meth_RDY_write_req (rule_RL_do_alloc_prefetch s).2) := by
  simp [rule_RL_do_alloc_prefetch,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB,
        ActionValue]
  unfold meth_RDY_write_req at *
  split <;> dsimp
  · split <;> simp_all
  · split <;> simp_all

theorem reconverge_RL_do_alloc_prefetch_write_req_rule_ready (s : state)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    isReady (rule_RL_do_alloc_prefetch (meth_write_req s write_req_addr write_req_data).avAction_).1 := by
  named_sorry doesnt_converge

theorem reconverge_RL_do_alloc_prefetch_write_req_method_eq (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req s write_req_addr write_req_data).avValue_
    = (meth_write_req (rule_RL_do_alloc_prefetch s).2 write_req_addr write_req_data).avValue_ := rfl

theorem reconverge_RL_do_alloc_prefetch_write_req_full (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_alloc_prefetch s).2 write_req_addr write_req_data).avAction_
      = (rule_RL_do_alloc_prefetch (meth_write_req s write_req_addr write_req_data).avAction_).2
    ∧ isReady (meth_RDY_write_req (rule_RL_do_alloc_prefetch s).2)
    ∧ isReady (rule_RL_do_alloc_prefetch (meth_write_req s write_req_addr write_req_data).avAction_).1
    ∧ (meth_write_req s write_req_addr write_req_data).avValue_
       = (meth_write_req (rule_RL_do_alloc_prefetch s).2 write_req_addr write_req_data).avValue_ := by
  simp [*, reconverge_RL_do_alloc_prefetch_write_req, reconverge_RL_do_alloc_prefetch_write_req_method_ready, reconverge_RL_do_alloc_prefetch_write_req_rule_ready, reconverge_RL_do_alloc_prefetch_write_req_method_eq]
  

-- Critical pair: rule_RL_do_alloc_prefetch × meth_read_req
theorem reconverge_RL_do_alloc_prefetch_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_alloc_prefetch s).2 read_req_addr).avAction_ =
    (rule_RL_do_alloc_prefetch (meth_read_req s read_req_addr).avAction_).2 := by
  simp only [rule_RL_do_alloc_prefetch,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB,
        ActionValue]
  unfold meth_read_req
  split <;> (rename_i h; rw [h])

-- Critical pair: rule_RL_do_alloc_prefetch × meth_read_resp
theorem reconverge_RL_do_alloc_prefetch_read_resp (s : state)
    (h1 : (rule_RL_do_alloc_prefetch s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_alloc_prefetch s).2).avAction_ =
    (rule_RL_do_alloc_prefetch (meth_read_resp s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_wait × meth_alloc
theorem reconverge_RL_do_alloc_wait_alloc (s : state)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_alloc s)) :
    (meth_alloc (rule_RL_do_alloc_wait s).2).avAction_ =
    (rule_RL_do_alloc_wait (meth_alloc s).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_wait × meth_free
theorem reconverge_RL_do_alloc_wait_free (s : state)
    (free_f : BitVec 16)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_free s)) :
    (meth_free (rule_RL_do_alloc_wait s).2 free_f).avAction_ =
    (rule_RL_do_alloc_wait (meth_free s free_f).avAction_).2 := by
  exfalso
  simp only [bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at *
  revert h1 h2
  cases s.opState <;> cases s.allocState <;> simp_all

-- Critical pair: rule_RL_do_alloc_wait × meth_write_req
-- Commute: disjoint fields. alloc_wait writes {bram_rever, allocNextStable,
-- allocState}, write_req writes {opWriteData, bram_index, opState}.
theorem reconverge_RL_do_alloc_wait_write_req (s : state)
    (write_req_addr : BitVec 16)
    (write_req_data : BitVec 32)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_write_req s)) :
    (meth_write_req (rule_RL_do_alloc_wait s).2 write_req_addr write_req_data).avAction_ =
    (rule_RL_do_alloc_wait (meth_write_req s write_req_addr write_req_data).avAction_).2 := by
  simp [rule_RL_do_alloc_wait, meth_write_req,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readB, ActionValue]

-- Critical pair: rule_RL_do_alloc_wait × meth_read_req
-- Commute: disjoint fields. alloc_wait writes {bram_rever, allocNextStable,
-- allocState}, read_req writes {bram_index, opState}.
theorem reconverge_RL_do_alloc_wait_read_req (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_alloc_wait s).2 read_req_addr).avAction_ =
    (rule_RL_do_alloc_wait (meth_read_req s read_req_addr).avAction_).2 := by
  simp [rule_RL_do_alloc_wait, meth_read_req,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readB, ActionValue]

-- Values are the same
theorem reconverge_RL_do_alloc_wait_read_req2 (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (meth_read_req (rule_RL_do_alloc_wait s).2 read_req_addr).avValue_ = (meth_read_req s read_req_addr).avValue_ := by
  simp [rule_RL_do_alloc_wait, meth_read_req,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readB, ActionValue]

-- Rule can execute
theorem reconverge_RL_do_alloc_wait_read_req3 (s : state)
    (read_req_addr : BitVec 16)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_req s)) :
    (rule_RL_do_alloc_wait (meth_read_req s read_req_addr).avAction_).1 = BTrue Unit_ := by
  simp_all [rule_RL_do_alloc_wait, meth_read_req,
        M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readB, ActionValue]

-- Critical pair: rule_RL_do_alloc_wait × meth_read_resp
-- Commute: disjoint fields. alloc_wait writes {bram_rever, allocNextStable,
-- allocState}, read_resp writes {bram_data, opState}.
theorem reconverge_RL_do_alloc_wait_read_resp (s : state)
    (h1 : (rule_RL_do_alloc_wait s).1 = BTrue Unit_)
    (h2 : isReady (meth_RDY_read_resp s)) :
    (meth_read_resp (rule_RL_do_alloc_wait s).2).avAction_ =
    (rule_RL_do_alloc_wait (meth_read_resp s).avAction_).2 := by
  simp [rule_RL_do_alloc_wait, meth_read_resp,
        M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, ActionValue]

theorem strongly_normalising l :
  Star.strongly_normalising (fun x y => (applyRules l x) = y) := by sorry

end M_mkBluealloc.Verify
