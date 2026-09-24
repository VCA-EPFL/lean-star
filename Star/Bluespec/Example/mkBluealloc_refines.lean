import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Example.Bluealloc_types
import Star.Bluespec.Lib.mkSimpleBRAM2
import Star.Bluespec.Example.mkBluealloc
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
open BluespecPrelude
open Bluealloc_types
open BluespecVerification
open ReachingStar Bluespec

set_option maxHeartbeats 1000000

-- ═══ Specification (fill in State, methods, and phi0) ═══

namespace M_mkBluealloc.Spec

-- Abstract state. `valid = false` is the POISONED state: any out-of-range
-- (undefined-behavior) access lands here, after which all bets are off — `phi0`
-- and every spec method become fully permissive (see `poisonWrap`).
structure State where
  valid : Bool
  store : BitVec 16 → BitVec 32
  numAllocated : Nat
  -- The set of currently-live stable handles (membership, not a count).  `alloc`
  -- hands back SOME unused handle (the impl picks which — see SpecModule.alloc);
  -- free/write/read are valid exactly on used handles.
  used : BitVec 16 → Bool
  pendingRead : Option (BitVec 32)

instance : Inhabited State where
  default := { valid := true, store := fun _ => 0, numAllocated := 0, used := fun _ => false, pendingRead := none }

-- alloc is NONDETERMINISTIC: it returns some currently-unused handle `v`.  The value
-- is chosen in the SpecModule relation; here we only give the resulting state update.
def alloc_upd (s : State) (v : BitVec 16) : State :=
  { s with numAllocated := s.numAllocated + 1, used := fun a => if a == v then true else s.used a }
def meth_RDY_alloc (s : State) : t_bool :=
  if s.numAllocated < 65535 ∧ s.pendingRead = none then BTrue Unit_ else BFalse Unit_

-- free/write_req/read_req take a stable handle; a non-live handle (`used = false`)
-- is undefined behavior, so they POISON the state (valid := false).
def meth_free (s : State) (addr : BitVec 16) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_, avAction_ :=
      if s.used addr then { s with numAllocated := s.numAllocated - 1, used := fun a => if a == addr then false else s.used a }
      else { s with valid := false } }
def meth_RDY_free (s : State) : t_bool :=
  if s.numAllocated > 0 ∧ s.pendingRead = none then BTrue Unit_ else BFalse Unit_

def meth_write_req (s : State) (addr : BitVec 16) (data : BitVec 32) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_, avAction_ :=
      if s.used addr then { s with store := fun a => if a == addr then data else s.store a }
      else { s with valid := false } }
def meth_RDY_write_req (s : State) : t_bool :=
  if s.pendingRead = none then BTrue Unit_ else BFalse Unit_

def meth_read_req (s : State) (addr : BitVec 16) : t_actionvalue_ unit_ State :=
  { avValue_ := Unit_, avAction_ :=
      if s.used addr then { s with pendingRead := some (s.store addr) }
      else { s with valid := false } }
def meth_RDY_read_req (s : State) : t_bool :=
  if s.pendingRead = none then BTrue Unit_ else BFalse Unit_

def meth_read_resp (s : State) : t_actionvalue_ (BitVec 32) State :=
  match s.pendingRead with
  | some d => { avValue_ := d, avAction_ := { s with pendingRead := none } }
  | none   => { avValue_ := 0, avAction_ := s }
def meth_RDY_read_resp (s : State) : t_bool :=
  match s.pendingRead with
  | some _ => BTrue Unit_
  | none   => BFalse Unit_

end M_mkBluealloc.Spec

namespace M_mkBluealloc.Refines

@[grind cases]
inductive Method : Type where
| alloc
| free
| write_req
| read_req
| read_resp

@[grind cases]
inductive Rule : Type where
| RL_do_read_index
| RL_do_write_index
| RL_do_free_lookup
| RL_do_free_read
| RL_do_free_write
| RL_do_alloc_prefetch
| RL_do_alloc_wait

-- Once the spec is poisoned (valid = false), a method keeps its footprint SHAPE
-- (right arity, but any value) and steps to ANY poisoned state — "all bets off",
-- the impl may do anything and still refine. When valid, it's the usual
-- `ofAVMethodK` behavior (which itself poisons on an out-of-range address).
def SpecModule : Bluespec.Module Empty Method where
  State := M_mkBluealloc.Spec.State
  methods
    | .alloc => fun e s s' => ∃ v, e = Footprint.arg0 v ∧
        (if s.valid then s.used v = false ∧ s' = M_mkBluealloc.Spec.alloc_upd s v ∧ M_mkBluealloc.Spec.meth_RDY_alloc s = BTrue Unit_ else s'.valid = false)
    | .free => fun e s s' => ∃ addr v, e = Footprint.arg1 addr v ∧
        (if s.valid then M_mkBluealloc.Spec.meth_free s addr = ⟨v, s'⟩ ∧ M_mkBluealloc.Spec.meth_RDY_free s = BTrue Unit_ else s'.valid = false)
    | .write_req => fun e s s' => ∃ addr data v, e = Footprint.arg2 addr data v ∧
        (if s.valid then M_mkBluealloc.Spec.meth_write_req s addr data = ⟨v, s'⟩ ∧ M_mkBluealloc.Spec.meth_RDY_write_req s = BTrue Unit_ else s'.valid = false)
    | .read_req => fun e s s' => ∃ addr v, e = Footprint.arg1 addr v ∧
        (if s.valid then M_mkBluealloc.Spec.meth_read_req s addr = ⟨v, s'⟩ ∧ M_mkBluealloc.Spec.meth_RDY_read_req s = BTrue Unit_ else s'.valid = false)
    | .read_resp => fun e s s' => ∃ v, e = Footprint.arg0 v ∧
        (if s.valid then M_mkBluealloc.Spec.meth_read_resp s = ⟨v, s'⟩ ∧ M_mkBluealloc.Spec.meth_RDY_read_resp s = BTrue Unit_ else s'.valid = false)
  rules := Empty.casesOn _

def ImplModule : Bluespec.Module Rule Method where
  State := M_mkBluealloc.state
  methods
    | .alloc => ofAVMethod0 M_mkBluealloc.meth_alloc M_mkBluealloc.meth_RDY_alloc
    | .free => ofAVMethod1 M_mkBluealloc.meth_free M_mkBluealloc.meth_RDY_free
    | .write_req => ofAVMethod2 M_mkBluealloc.meth_write_req M_mkBluealloc.meth_RDY_write_req
    | .read_req => ofAVMethod1 M_mkBluealloc.meth_read_req M_mkBluealloc.meth_RDY_read_req
    | .read_resp => ofAVMethod0 M_mkBluealloc.meth_read_resp M_mkBluealloc.meth_RDY_read_resp
  rules
    | .RL_do_read_index => ofRule M_mkBluealloc.rule_RL_do_read_index
    | .RL_do_write_index => ofRule M_mkBluealloc.rule_RL_do_write_index
    | .RL_do_free_lookup => ofRule M_mkBluealloc.rule_RL_do_free_lookup
    | .RL_do_free_read => ofRule M_mkBluealloc.rule_RL_do_free_read
    | .RL_do_free_write => ofRule M_mkBluealloc.rule_RL_do_free_write
    | .RL_do_alloc_prefetch => ofRule M_mkBluealloc.rule_RL_do_alloc_prefetch
    | .RL_do_alloc_wait => ofRule M_mkBluealloc.rule_RL_do_alloc_wait

-- The abstraction relation (the user's `phi0`); couples impl and spec state.
attribute [bsv_rules] M_mkBluealloc.rule_RL_do_read_index M_mkBluealloc.rule_RL_do_write_index M_mkBluealloc.rule_RL_do_free_lookup M_mkBluealloc.rule_RL_do_free_read M_mkBluealloc.rule_RL_do_free_write M_mkBluealloc.rule_RL_do_alloc_prefetch M_mkBluealloc.rule_RL_do_alloc_wait
attribute [bsv_methods] M_mkBluealloc.meth_alloc M_mkBluealloc.meth_RDY_alloc M_mkBluealloc.meth_free M_mkBluealloc.meth_RDY_free M_mkBluealloc.meth_write_req M_mkBluealloc.meth_RDY_write_req M_mkBluealloc.meth_read_req M_mkBluealloc.meth_RDY_read_req M_mkBluealloc.meth_read_resp M_mkBluealloc.meth_RDY_read_resp

-- Short-circuit lemmas so a `bool_and _ BFalse` collapses even when the other
-- conjunct is opaque (e.g. the alloc/read_req RDY nests `bool_not (enqPtr == …)`).
@[simp] theorem bool_and_false_right (b : t_bool) : bool_and b (BFalse Unit_) = BFalse Unit_ := by
  cases b <;> rfl
@[simp] theorem bool_and_false_left (b : t_bool) : bool_and (BFalse Unit_) b = BFalse Unit_ := rfl

-- Argument extraction from footprint equalities (HVector injectivity).
theorem Footprint.arg1_inj {A1 V : Type} {a b : A1} {v w : V}
    (h : Footprint.arg1 a v = Footprint.arg1 b w) : a = b := by
  simp only [Footprint.arg1, Footprint.mk.injEq, heq_eq_eq, true_and] at h
  injection h.1

theorem Footprint.arg2_inj {A1 A2 V : Type} {a1 b1 : A1} {a2 b2 : A2} {v w : V}
    (h : Footprint.arg2 a1 a2 v = Footprint.arg2 b1 b2 w) : a1 = b1 ∧ a2 = b2 := by
  simp only [Footprint.arg2, Footprint.mk.injEq, heq_eq_eq, true_and] at h
  obtain ⟨h1, -⟩ := h
  injection h1 with _ _ ha1 hrest
  injection hrest with _ _ ha2 _
  exact ⟨ha1, ha2⟩

theorem bool_and_eq_BTrue {a b : t_bool} {u : unit_} (h : bool_and a b = BTrue u) :
    a = BTrue Unit_ ∧ b = BTrue Unit_ := by
  cases a <;> cases b <;> simp_all [bool_and]

-- The alloc-method RDY buries `opState == OP_IDLE` as the second arg of an outer
-- `bool_and L2a (…)` with L2a opaque, so a plain `simp` can't short-circuit it.
-- Peel the conjunction structurally instead.
theorem alloc_RDY_opState {s : ImplModule.State}
    (h : M_mkBluealloc.meth_RDY_alloc s = BTrue Unit_) : s.opState = OP_IDLE Unit_ := by
  simp only [M_mkBluealloc.meth_RDY_alloc] at h
  have h2 := (bool_and_eq_BTrue (bool_and_eq_BTrue h).1).2
  cases hop : s.opState <;> simp_all [(. == .)]

def phi0 (si : ImplModule.State) (ss : SpecModule.State) : Prop :=
  -- Poisoned: all bets off — any impl state refines a poisoned spec.
  ss.valid = false ∨
  (ss.valid = true ∧
  si.allocState = AL_READY Unit_ ∧
  si.enqPtr.toNat = ss.numAllocated ∧
  ss.numAllocated ≤ si.maxEver.toNat ∧
  ((si.opState = OP_IDLE Unit_ ∧ ss.pendingRead = none ∧
    si.bram_data.readResultA = none ∧ si.bram_data.readResultB = none ∧
    si.bram_index.readResultA = none ∧ si.bram_index.readResultB = none ∧
    si.bram_rever.readResultA = none ∧ si.bram_rever.readResultB = none) ∨
   (si.opState = OP_READ_DATA Unit_ ∧
    (∃ d, ss.pendingRead = some d ∧ si.bram_data.readResultA = some d) ∧
    si.bram_data.readResultB = none ∧
    si.bram_index.readResultA = none ∧ si.bram_index.readResultB = none ∧
    si.bram_rever.readResultA = none ∧ si.bram_rever.readResultB = none)) ∧
  (∀ (s : BitVec 16), s.toNat < si.maxEver.toNat →
    let u := si.bram_index.memory.getD s.toNat default
    u.toNat < si.bram_data.memory.size ∧
    u.toNat < si.bram_rever.memory.size ∧
    si.bram_rever.memory.getD u.toNat default = s) ∧
  -- Nondeterministic-allocator abstraction: a stable handle is live (`used`) iff it was
  -- ever allocated and its unstable slot is currently in the live range [0, enqPtr).
  (∀ (s : BitVec 16), ss.used s = true ↔
    (s.toNat < si.maxEver.toNat ∧
     (si.bram_index.memory.getD s.toNat default).toNat < si.enqPtr.toNat)) ∧
  -- Data agreement over ALL ever-allocated handles (s < maxEver), not just live ones:
  -- a freed handle keeps `data[bram_index s] = store s` (free's swap maintains it), and a
  -- recycled `alloc` needs exactly this to re-establish data agreement for the reused handle.
  (∀ (s : BitVec 16), s.toNat < si.maxEver.toNat →
    si.bram_data.memory.getD (si.bram_index.memory.getD s.toNat default).toNat default = ss.store s) ∧
  65536 ≤ si.bram_index.memory.size ∧
  65536 ≤ si.bram_rever.memory.size ∧
  65536 ≤ si.bram_data.memory.size ∧
  (∀ (s : BitVec 16), s.toNat < si.maxEver.toNat →
    (si.bram_index.memory.getD s.toNat default).toNat < si.maxEver.toNat) ∧
  (∀ (s : BitVec 16), si.maxEver.toNat ≤ s.toNat → ss.store s = default) ∧
  (∀ (u : BitVec 16), si.maxEver.toNat ≤ u.toNat →
    si.bram_data.memory.getD u.toNat default = default) ∧
  (∀ (u : BitVec 16), u.toNat < si.maxEver.toNat →
    (si.bram_rever.memory.getD u.toNat default).toNat < si.maxEver.toNat ∧
    si.bram_index.memory.getD (si.bram_rever.memory.getD u.toNat default).toNat default = u) ∧
   -- Frontier invariant: the prefetched next handle is itself not currently live, so a
   -- fresh `alloc` can hand it back.  Fresh slot ⇒ it equals enqPtr (≥ maxEver, unused);
   -- recycled slot ⇒ its forward map is exactly enqPtr (so `used = false` via the bijection).
   ((si.maxEver.toNat ≤ si.enqPtr.toNat → si.allocNextStable = si.enqPtr) ∧
    (si.enqPtr.toNat < si.maxEver.toNat →
      si.allocNextStable.toNat < si.maxEver.toNat ∧
      (si.bram_index.memory.getD si.allocNextStable.toNat default).toNat = si.enqPtr.toNat)))

@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (v : BitVec 16), e.1 = .alloc ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (free_f : BitVec 16) (v : unit_), e.1 = .free ∧ e.2 = (Footprint.arg1 free_f v)) ∨ (∃ (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_), e.1 = .write_req ∧ e.2 = (Footprint.arg2 write_req_addr write_req_data v)) ∨ (∃ (read_req_addr : BitVec 16) (v : unit_), e.1 = .read_req ∧ e.2 = (Footprint.arg1 read_req_addr v)) ∨ (∃ (v : BitVec 32), e.1 = .read_resp ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;> (dsimp [ImplModule, Module.getMethod, ofAVMethod0, ofAVMethod1, ofAVMethod2] at h; grind)

@[local grind →] theorem SpecModule.get_method_cases :
  SpecModule.getMethod i e i' →
  (∃ (v : BitVec 16), e.1 = .alloc ∧ e.2 = (Footprint.arg0 v)) ∨ (∃ (free_f : BitVec 16) (v : unit_), e.1 = .free ∧ e.2 = (Footprint.arg1 free_f v)) ∨ (∃ (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_), e.1 = .write_req ∧ e.2 = (Footprint.arg2 write_req_addr write_req_data v)) ∨ (∃ (read_req_addr : BitVec 16) (v : unit_), e.1 = .read_req ∧ e.2 = (Footprint.arg1 read_req_addr v)) ∨ (∃ (v : BitVec 32), e.1 = .read_resp ∧ e.2 = (Footprint.arg0 v)) := by
  intro h
  obtain ⟨name, footprint⟩ := e
  cases name <;> (dsimp [SpecModule, Module.getMethod] at h; grind)

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  ImplModule.getRule .RL_do_read_index i i' ∨ ImplModule.getRule .RL_do_write_index i i' ∨ ImplModule.getRule .RL_do_free_lookup i i' ∨ ImplModule.getRule .RL_do_free_read i i' ∨ ImplModule.getRule .RL_do_free_write i i' ∨ ImplModule.getRule .RL_do_alloc_prefetch i i' ∨ ImplModule.getRule .RL_do_alloc_wait i i' := by
  intro h; obtain ⟨r, hr⟩ := h; cases r <;> tauto

@[local grind →] theorem commutes_RL_do_read_index_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_read_index_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_read_index_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_read_index_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_read_index_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_read_index_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_read_index_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_read_index a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  -- read_index touches {opState, bram_index, bram_data}; alloc_wait touches {allocState,
  -- allocNextStable, bram_rever}.  Disjoint ⇒ fire the other rule from each side to converge.
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_read_index a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_read_index a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.rule_RL_do_read_index a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_read_index, ?_⟩⟩
  · -- alloc_wait fires from c (allocState unchanged by read_index)
    refine Prod.ext ?_ rfl
    simp_all [bsv_rules]
  · -- read_index fires from b and reaches the same combined state
    refine Prod.ext ?_ ?_
    · simp_all [bsv_rules]
    · simp [bsv_rules]

@[local grind →] theorem commutes_RL_do_write_index_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_write_index_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_write_index_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_write_index_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_write_index_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_write_index_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_write_index_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_write_index a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_write_index a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_write_index a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.rule_RL_do_write_index a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_write_index, ?_⟩⟩
  · refine Prod.ext ?_ rfl
    simp_all [bsv_rules]
  · refine Prod.ext ?_ ?_
    · simp_all [bsv_rules]
    · simp [bsv_rules]

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_lookup_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_lookup a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_free_lookup a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_free_lookup a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  -- free_lookup uses port A of bram_rever (putA/BFalse = read-request to port A)
  -- alloc_wait uses port B of bram_rever (readB). Ports A and B are disjoint.
  refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.rule_RL_do_free_lookup a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_free_lookup, ?_⟩⟩
  · -- alloc_wait guard and effect from c: allocState/readResultB unchanged by free_lookup
    refine Prod.ext ?_ rfl
    simp_all [bsv_rules, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_RDY_readB]
  · refine Prod.ext ?_ ?_
    · -- free_lookup guard from b: readResultA/opState unchanged by alloc_wait
      simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA,
                M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_putB]
    · -- bram_rever: putA BFalse (sets readResultA) commutes with readB (clears readResultB)
      simp only [bsv_rules, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readB, ActionValue]

@[local grind →] theorem commutes_RL_do_free_read_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_read_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_read_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_read_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_free_read_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_read_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_read_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_read a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_free_read a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_free_read a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  -- free_read uses readA on bram_rever (port A latch); alloc_wait uses readB (port B). Disjoint.
  refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.rule_RL_do_free_read a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_free_read, ?_⟩⟩
  · refine Prod.ext ?_ rfl
    simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_RDY_readB]
  · refine Prod.ext ?_ ?_
    · -- free_read guard from b: readResultA (port A) unchanged by alloc_wait (readB = port B)
      simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_readA,
                M_mkSimpleBRAM2.meth_RDY_readB, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB]
    · -- bram_rever: readA (port A, clears readResultA) commutes with readB (port B, clears readResultB)
      simp only [bsv_rules, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, ActionValue]

@[local grind →] theorem commutes_RL_do_free_write_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_write_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_write_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_write_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_write_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_free_write_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_free_write_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_free_write a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  -- free_write requires meth_RDY_putB(bram_rever) = BTrue (readResultB = none)
  -- alloc_wait requires meth_RDY_readB(bram_rever) = BTrue (readResultB = some _)
  -- These are complementary — the pair cannot fire simultaneously from the same state.
  exfalso
  have hcg : (M_mkBluealloc.rule_RL_do_free_write a).1 = BTrue Unit_ := congrArg Prod.fst hc
  have hbg : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ := congrArg Prod.fst hb
  simp only [bsv_rules, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
    M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB, bool_and, (.==.),
    instBEqT_allocstate.beq] at hcg hbg
  -- readResultB determines the contradiction: free_write needs none, alloc_wait needs some.
  -- Case-split on all relevant fields so simp_all can reduce the nested bool_and matches.
  revert hcg hbg
  cases a.bram_rever.readResultB <;> cases a.bram_rever.readResultA <;>
    cases a.bram_data.readResultA <;> cases a.bram_data.readResultB <;>
    cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem commutes_RL_do_alloc_prefetch_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_prefetch a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_read_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_read_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_read_index a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_read_index a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  refine ⟨(M_mkBluealloc.rule_RL_do_read_index (M_mkBluealloc.rule_RL_do_alloc_wait a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_read_index, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩⟩
  · refine Prod.ext ?_ ?_
    · simp_all [bsv_rules]
    · simp [bsv_rules]
  · refine Prod.ext ?_ rfl
    simp_all [bsv_rules]

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_write_index a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_write_index a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  refine ⟨(M_mkBluealloc.rule_RL_do_write_index (M_mkBluealloc.rule_RL_do_alloc_wait a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_write_index, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩⟩
  · refine Prod.ext ?_ ?_
    · simp_all [bsv_rules]
    · simp [bsv_rules]
  · refine Prod.ext ?_ rfl
    simp_all [bsv_rules]

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_free_lookup {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_free_lookup a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_free_lookup a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_free_lookup a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  -- alloc_wait: readB on bram_rever (uses/clears readResultB)
  -- free_lookup: putA on bram_rever (sets readResultA) — disjoint ports
  refine ⟨(M_mkBluealloc.rule_RL_do_free_lookup (M_mkBluealloc.rule_RL_do_alloc_wait a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_free_lookup, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩⟩
  · refine Prod.ext ?_ ?_
    · -- free_lookup guard from c: readResultA and opState unchanged by alloc_wait (readB only touches readResultB)
      simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_putA,
                M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_putB]
    · -- bram_rever: readB (port B) commutes with putA BFalse (port A)
      simp only [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_putA, ActionValue]
  · refine Prod.ext ?_ rfl
    -- alloc_wait guard from b: allocState unchanged by free_lookup; readResultB unchanged by putA
    simp_all [bsv_rules, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_RDY_readB]

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_free_read {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_free_read a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  obtain ⟨hcg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ ∧
      c = (M_mkBluealloc.rule_RL_do_alloc_wait a).2 :=
    ⟨congrArg Prod.fst hc, (congrArg Prod.snd hc).symm⟩
  obtain ⟨hbg, rfl⟩ : (M_mkBluealloc.rule_RL_do_free_read a).1 = BTrue Unit_ ∧
      b = (M_mkBluealloc.rule_RL_do_free_read a).2 :=
    ⟨congrArg Prod.fst hb, (congrArg Prod.snd hb).symm⟩
  -- alloc_wait: readB on bram_rever (uses/clears readResultB)
  -- free_read: readA on bram_rever (uses/clears readResultA) — disjoint ports
  refine ⟨(M_mkBluealloc.rule_RL_do_free_read (M_mkBluealloc.rule_RL_do_alloc_wait a).2).2,
          Relation.ReflTransGen.single ⟨.RL_do_free_read, ?_⟩,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_wait, ?_⟩⟩
  · refine Prod.ext ?_ ?_
    · -- free_read guard from c: readResultA preserved by alloc_wait (readB only touches readResultB)
      simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_RDY_readA,
                M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB]
    · -- bram_rever: readB (port B) commutes with readA (port A)
      simp only [bsv_rules, M_mkSimpleBRAM2.meth_readB, M_mkSimpleBRAM2.meth_readA, ActionValue]
  · refine Prod.ext ?_ rfl
    -- alloc_wait guard from b: allocState unchanged; readResultB unchanged by readA (port A)
    simp_all [bsv_rules, M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_RDY_readB]

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_free_write {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_free_write a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  -- alloc_wait requires meth_RDY_readB(bram_rever) = BTrue (readResultB = some _)
  -- free_write requires meth_RDY_putB(bram_rever) = BTrue (readResultB = none)
  -- Contradictory guards — these two rules cannot fire from the same state.
  exfalso
  have hcg : (M_mkBluealloc.rule_RL_do_alloc_wait a).1 = BTrue Unit_ := congrArg Prod.fst hc
  have hbg : (M_mkBluealloc.rule_RL_do_free_write a).1 = BTrue Unit_ := congrArg Prod.fst hb
  simp only [bsv_rules, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
    M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB, bool_and, (.==.),
    instBEqT_allocstate.beq] at hcg hbg
  revert hcg hbg
  cases a.bram_rever.readResultB <;> cases a.bram_rever.readResultA <;>
    cases a.bram_data.readResultA <;> cases a.bram_data.readResultB <;>
    cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_alloc_prefetch {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_alloc_prefetch a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  exfalso
  simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hc hb
  revert hc hb
  cases a.opState <;> cases a.allocState <;> simp_all

@[local grind →] theorem commutes_RL_do_alloc_wait_RL_do_alloc_wait {a b c : ImplModule.State} :
  ImplModule.getRule .RL_do_alloc_wait a c →
  ImplModule.getRule .RL_do_alloc_wait a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by
  intro hc hb
  have hc' : _ = (BTrue Unit_, c) := hc
  have hb' : _ = (BTrue Unit_, b) := hb
  have hcb : c = b := congrArg Prod.snd (hc'.symm.trans hb')
  subst hcb
  exact ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

@[local grind →] theorem reconverge_RL_do_read_index_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_read_index s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_read_index s'' s''' := by
  -- Vacuous: alloc needs opState == OP_IDLE, do_read_index needs OP_READ_INDEX.
  intro hr hm
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨_, _, _, hrdy⟩ := hm
  have hop : s.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
  simp [ImplModule, Module.getRule, ofRule, bsv_rules, hop, (. == .), bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, Prod.mk.injEq] at hr

@[local grind →] theorem reconverge_RL_do_read_index_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_read_index s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_read_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_read_index_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_read_index s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_read_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_read_index_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_read_index s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_read_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_read_index_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_read_index s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_read_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_write_index_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_write_index s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_write_index s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨_, _, _, hrdy⟩ := hm
  have hop : s.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
  simp [ImplModule, Module.getRule, ofRule, bsv_rules, hop, (. == .), bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, Prod.mk.injEq] at hr

@[local grind →] theorem reconverge_RL_do_write_index_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_write_index s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_write_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_write_index_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_write_index s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_write_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_write_index_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_write_index s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_write_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_write_index_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_write_index s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_write_index s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_lookup_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_free_lookup s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_lookup s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨_, _, _, hrdy⟩ := hm
  have hop : s.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
  simp [ImplModule, Module.getRule, ofRule, bsv_rules, hop, (. == .), bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, Prod.mk.injEq] at hr

@[local grind →] theorem reconverge_RL_do_free_lookup_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_lookup s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_free_lookup s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_lookup_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_free_lookup s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_free_lookup s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_lookup_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_lookup s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_free_lookup s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_lookup_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_free_lookup s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_lookup s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_read_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_free_read s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_read s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨_, _, _, hrdy⟩ := hm
  have hop : s.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
  simp [ImplModule, Module.getRule, ofRule, bsv_rules, hop, (. == .), bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, Prod.mk.injEq] at hr

@[local grind →] theorem reconverge_RL_do_free_read_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_read s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_free_read s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_read_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_free_read s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_free_read s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_read_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_read s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_free_read s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_read_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_free_read s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_read s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_write_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_free_write s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_write s'' s''' := by
  intro hr hm
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨_, _, _, hrdy⟩ := hm
  have hop : s.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
  simp [ImplModule, Module.getRule, ofRule, bsv_rules, hop, (. == .), bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, Prod.mk.injEq] at hr

@[local grind →] theorem reconverge_RL_do_free_write_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_write s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_free_write s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_write_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_free_write s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_free_write s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_write_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_free_write s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_free_write s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_free_write_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_free_write s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_free_write s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_prefetch_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_prefetch_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_prefetch_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  -- Now vacuous: write_req requires allocState == AL_READY, alloc_prefetch requires AL_PREFETCH.
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_prefetch_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  -- Now vacuous: read_req requires allocState == AL_READY, alloc_prefetch requires AL_PREFETCH.
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_prefetch_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_wait_alloc (s s' s'' : ImplModule.State) (v : BitVec 16) :
  ImplModule.getRule .RL_do_alloc_wait s s' →
  ImplModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.alloc, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_wait s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_wait_free (s s' s'' : ImplModule.State) (free_f : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_wait s s' →
  ImplModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.free, Footprint.arg1 free_f v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_wait s'' s''' := by
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_wait_write_req (s s' s'' : ImplModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_wait s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_wait s'' s''' := by
  -- Now vacuous: write_req requires allocState == AL_READY, alloc_wait requires AL_WAIT.
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_wait_read_req (s s' s'' : ImplModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_wait s s' →
  ImplModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_wait s'' s''' := by
  -- Now vacuous: read_req requires allocState == AL_READY, alloc_wait requires AL_WAIT.
  intro hr hm
  exfalso
  simp only [ImplModule, Module.getRule, Module.getMethod, ofRule, ofAVMethod0, ofAVMethod1, ofAVMethod2, bsv_rules, bsv_methods, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr hm
  revert hr hm
  cases s.opState <;> cases s.allocState <;> simp_all

@[local grind →] theorem reconverge_RL_do_alloc_wait_read_resp (s s' s'' : ImplModule.State) (v : BitVec 32) :
  ImplModule.getRule .RL_do_alloc_wait s s' →
  ImplModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s'' →
  ∃ s''', ImplModule.getMethod s' ⟨.read_resp, Footprint.arg0 v⟩ s''' ∧ ImplModule.getRule .RL_do_alloc_wait s'' s''' := by
  -- Disjoint: alloc_wait touches {allocState, allocNextStable, bram_rever};
  -- read_resp touches {opState, bram_data}.  Commute by reordering.
  intro hr hm
  -- Decompose the rule firing into guard + effect.
  obtain ⟨hrg, rfl⟩ : (M_mkBluealloc.rule_RL_do_alloc_wait s).1 = BTrue Unit_ ∧
      s' = (M_mkBluealloc.rule_RL_do_alloc_wait s).2 :=
    ⟨congrArg Prod.fst hr, (congrArg Prod.snd hr).symm⟩
  -- Decompose the method: extract the read value, output state, and RDY.
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨v', hmeth, heq, hrdy⟩ := hm
  -- s'' is the post-read_resp state.
  have hs'' : s'' = (M_mkBluealloc.meth_read_resp s).avAction_ := by
    rw [hmeth]
  have hv' : v' = (M_mkBluealloc.meth_read_resp s).avValue_ := by
    rw [hmeth]
  subst hs'' hv'
  -- The two effect orders agree on the value and the final state (disjoint fields).
  refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.meth_read_resp s).avAction_).2, ?_, ?_⟩
  · -- read_resp fires from s' = (alloc_wait s).2 and produces the same value/state.
    refine ⟨(M_mkBluealloc.meth_read_resp s).avValue_, ?_, heq, ?_⟩
    · -- value & action-state both match (disjoint fields commute)
      simp [M_mkBluealloc.rule_RL_do_alloc_wait, M_mkBluealloc.meth_read_resp,
            M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, ActionValue]
    · -- RDY of read_resp depends only on opState/bram_data, untouched by alloc_wait
      rw [show (M_mkBluealloc.meth_RDY_read_resp (M_mkBluealloc.rule_RL_do_alloc_wait s).2)
            = M_mkBluealloc.meth_RDY_read_resp s from by
        unfold M_mkBluealloc.meth_RDY_read_resp M_mkBluealloc.rule_RL_do_alloc_wait
        rfl]
      exact hrdy
  · -- alloc_wait fires from s'' (guard depends on allocState, untouched by read_resp)
    show M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.meth_read_resp s).avAction_ = (BTrue Unit_, _)
    have hg : (M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.meth_read_resp s).avAction_).1
            = BTrue Unit_ := by
      rw [show (M_mkBluealloc.rule_RL_do_alloc_wait (M_mkBluealloc.meth_read_resp s).avAction_).1
            = (M_mkBluealloc.rule_RL_do_alloc_wait s).1 from by
        unfold M_mkBluealloc.rule_RL_do_alloc_wait M_mkBluealloc.meth_read_resp
        rfl]
      exact hrg
    exact Prod.ext hg rfl

-- BRAM array helpers (shared by the reach_phi0_again_* proofs below).
theorem setIB_same {α : Type} (a : Array α) (i : Nat) (v d : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i d = v := by
  simp [Array.setIfInBounds, h, Array.getD]
theorem setIB_diff {α : Type} (a : Array α) (i j : Nat) (v d : α) (h_ne : i ≠ j) :
    (a.setIfInBounds i v).getD j d = a.getD j d := by
  unfold Array.setIfInBounds; split
  · rename_i h_lt; unfold Array.getD
    have h_sz : (a.set i v h_lt).size = a.size := Array.size_set ..
    by_cases h_j : j < a.size
    · simp [h_sz, h_j]; exact Array.getElem_set_ne h_lt (by omega) h_ne
    · simp [h_sz, h_j]
  · rfl
theorem setIB_size {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.setIfInBounds i v).size = a.size := by
  unfold Array.setIfInBounds; split
  · exact Array.size_set ..
  · rfl

@[local grind →] theorem phi0_indistinguishable_alloc (i i' : ImplModule.State) (s : SpecModule.State) (v : BitVec 16) :
  phi0 i s →
  ImplModule.getMethod i ⟨.alloc, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s' := by
  intro hp hm
  -- Extract the impl alloc value: v = i.allocNextStable, plus RDY.
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨v', hmeth, hfp, hrdy⟩ := hm
  have hv : v = i.allocNextStable := by
    have hv' : v' = i.allocNextStable := by simp [bsv_methods] at hmeth; exact hmeth.1.symm
    have hvv : v = v' := by
      simp only [Footprint.arg0, Footprint.mk.injEq, heq_eq_eq] at hfp; tauto
    rw [hvv, hv']
  rcases hp with h_poison | h_valid
  · exact ⟨{ s with valid := false }, v, rfl, by simp [h_poison]⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    -- pendingRead = none (alloc RDY forces opState = OP_IDLE; the READ_DATA arm is impossible).
    have h_pend : s.pendingRead = none := by
      rcases h_op_cases with ⟨-, hpd, -⟩ | ⟨h_op_rd, -⟩
      · exact hpd
      · exfalso
        have := alloc_RDY_opState hrdy
        rw [h_op_rd] at this
        simp [(. == .)] at this
    -- enqPtr ≠ 65535, hence numAllocated < 65535.
    have h_ne : i.enqPtr ≠ 65535 := by
      intro hh
      simp only [M_mkBluealloc.meth_RDY_alloc] at hrdy
      have h2' := (bool_and_eq_BTrue (bool_and_eq_BTrue (bool_and_eq_BTrue hrdy).1).1).2
      rw [hh] at h2'
      simp [(. == .), bool_not, bitvec_simp] at h2'
    have h_num : s.numAllocated < 65535 := by rw [← h_enq]; bv_omega
    -- s.used v = false: split on whether the frontier slot is fresh or recycled.
    have h_used_v : s.used v = false := by
      by_contra hu
      have hu' : s.used v = true := by simpa using hu
      rw [h_used v] at hu'
      obtain ⟨hv_max, hv_live⟩ := hu'
      by_cases hcmp : i.maxEver.toNat ≤ i.enqPtr.toNat
      · -- fresh: allocNextStable = enqPtr, so index[v] = index[allocNextStable].toNat = enqPtr,
        -- not < enqPtr.  But v = allocNextStable ≥ maxEver > v.toNat contradicts hv_max.
        have := h_frontier.1 hcmp  -- allocNextStable = enqPtr
        rw [hv] at hv_max
        -- v.toNat = enqPtr.toNat ≥ maxEver.toNat, contradicting v.toNat < maxEver.
        rw [this] at hv_max
        omega
      · -- recycled: index[allocNextStable] = enqPtr, so index[v].toNat = enqPtr.toNat,
        -- contradicting hv_live : index[v].toNat < enqPtr.toNat.
        have hlt : i.enqPtr.toNat < i.maxEver.toNat := by omega
        have := (h_frontier.2 hlt).2  -- index[allocNextStable].toNat = enqPtr.toNat
        rw [hv] at hv_live
        rw [this] at hv_live
        omega
    refine ⟨M_mkBluealloc.Spec.alloc_upd s v, v, rfl, ?_⟩
    rw [if_pos h_vtrue]
    exact ⟨h_used_v, rfl, by simp [M_mkBluealloc.Spec.meth_RDY_alloc, h_num, h_pend]⟩

@[local grind →] theorem phi0_indistinguishable_free (i i' : ImplModule.State) (s : SpecModule.State) (free_f : BitVec 16) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.free, Footprint.arg1 free_f v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s' := by
  intro hp hm
  rcases hp with h_poison | h_valid
  · exact ⟨{ s with valid := false }, free_f, v, rfl, by simp [h_poison]⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, -, h_op_cases, -⟩ := h_valid
    dsimp [ImplModule, Module.getMethod, ofAVMethod1] at hm
    obtain ⟨_, _, _, _, hrdy⟩ := hm
    rcases h_op_cases with ⟨h_op, h_pend, -⟩ | ⟨h_op, -⟩
    · simp [isReady, bsv_methods, h_op, h_alloc, (. == .),
            instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA] at hrdy
      have h_ne : i.enqPtr ≠ 0 := by intro hh; simp [hh, bool_not] at hrdy
      have h_num : 0 < s.numAllocated := by rw [← h_enq]; bv_omega
      refine ⟨(M_mkBluealloc.Spec.meth_free s free_f).avAction_, free_f, v, rfl, ?_⟩
      rw [if_pos h_vtrue]; cases v
      exact ⟨rfl, by simp [M_mkBluealloc.Spec.meth_RDY_free, h_num, h_pend]⟩
    · simp [isReady, bsv_methods, h_op, (. == .), bool_and] at hrdy

@[local grind →] theorem phi0_indistinguishable_write_req (i i' : ImplModule.State) (s : SpecModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s' := by
  intro hp hm
  rcases hp with h_poison | h_valid
  · -- poisoned spec accepts any event, steps to a poisoned state
    exact ⟨{ s with valid := false }, write_req_addr, write_req_data, v, rfl, by simp [h_poison]⟩
  · obtain ⟨h_vtrue, -, -, -, h_op_cases, -⟩ := h_valid
    have h_pend : s.pendingRead = none := by
      rcases h_op_cases with ⟨-, hpd, -⟩ | ⟨h_op_rd, -⟩
      · exact hpd
      · exfalso
        dsimp [ImplModule, Module.getMethod, ofAVMethod2] at hm
        obtain ⟨_, _, _, _, _, hrdy⟩ := hm
        simp [isReady, bsv_methods, h_op_rd, (. == .), bool_and] at hrdy
    refine ⟨(M_mkBluealloc.Spec.meth_write_req s write_req_addr write_req_data).avAction_,
            write_req_addr, write_req_data, v, rfl, ?_⟩
    rw [if_pos h_vtrue]
    cases v
    exact ⟨rfl, by simp [M_mkBluealloc.Spec.meth_RDY_write_req, h_pend]⟩

@[local grind →] theorem phi0_indistinguishable_read_req (i i' : ImplModule.State) (s : SpecModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.read_req, Footprint.arg1 read_req_addr v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s' := by
  intro hp hm
  rcases hp with h_poison | h_valid
  · exact ⟨{ s with valid := false }, read_req_addr, v, rfl, by simp [h_poison]⟩
  · obtain ⟨h_vtrue, -, -, -, h_op_cases, -⟩ := h_valid
    have h_pend : s.pendingRead = none := by
      rcases h_op_cases with ⟨-, hpd, -⟩ | ⟨h_op_rd, -⟩
      · exact hpd
      · exfalso
        dsimp [ImplModule, Module.getMethod, ofAVMethod1] at hm
        obtain ⟨_, _, _, _, hrdy⟩ := hm
        simp [isReady, bsv_methods, h_op_rd, (. == .), bool_and] at hrdy
    refine ⟨(M_mkBluealloc.Spec.meth_read_req s read_req_addr).avAction_, read_req_addr, v, rfl, ?_⟩
    rw [if_pos h_vtrue]
    cases v
    exact ⟨rfl, by simp [M_mkBluealloc.Spec.meth_RDY_read_req, h_pend]⟩

@[local grind →] theorem phi0_indistinguishable_read_resp (i i' : ImplModule.State) (s : SpecModule.State) (v : BitVec 32) :
  phi0 i s →
  ImplModule.getMethod i ⟨.read_resp, Footprint.arg0 v⟩ i' →
  ∃ s', SpecModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s' := by
  intro hp hm
  rcases hp with h_poison | h_valid
  · exact ⟨{ s with valid := false }, v, rfl, by simp [h_poison]⟩
  · obtain ⟨h_vtrue, -, -, -, h_op_cases, -⟩ := h_valid
    dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
    obtain ⟨v', hmeth, heq, hrdy⟩ := hm
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨-, ⟨d, h_pend, h_resA⟩, -⟩
    · exfalso
      simp [isReady, bsv_methods, h_op, (. == .), bool_and] at hrdy
    · have hvd : v' = d := by
        simp [bsv_methods, M_mkSimpleBRAM2.meth_readA, h_resA, ActionValue] at hmeth
        exact hmeth.1.symm
      refine ⟨(M_mkBluealloc.Spec.meth_read_resp s).avAction_, v', heq, ?_⟩
      rw [if_pos h_vtrue]
      refine ⟨?_, by simp [M_mkBluealloc.Spec.meth_RDY_read_resp, h_pend]⟩
      simp [M_mkBluealloc.Spec.meth_read_resp, h_pend, hvd]

@[local grind →] theorem reach_phi0_again_alloc (i i' : ImplModule.State) (s s' : SpecModule.State) (v : BitVec 16) :
  phi0 i s →
  ImplModule.getMethod i ⟨.alloc, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.alloc, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hp hm hsm
  -- Decompose impl method: i' = (meth_alloc i).avAction_, v = i.allocNextStable, RDY.
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨vi, hmeth, hfp, hrdy⟩ := hm
  have hi' : i' = (M_mkBluealloc.meth_alloc i).avAction_ := by rw [hmeth]
  -- Decompose spec method.
  dsimp [SpecModule, Module.getMethod] at hsm
  obtain ⟨v', hfp', hsbody⟩ := hsm
  rcases hp with h_poison | h_valid
  · rw [if_neg (by simp [h_poison])] at hsbody
    exact ⟨i', Relation.ReflTransGen.refl, Or.inl hsbody⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    rw [if_pos h_vtrue] at hsbody
    obtain ⟨h_used_v, hs'_eq, -⟩ := hsbody
    -- v = i.allocNextStable.
    have hv : v = i.allocNextStable := by
      have hv0 : vi = i.allocNextStable := by simp [bsv_methods] at hmeth; exact hmeth.1.symm
      have : v = vi := by simp only [Footprint.arg0, Footprint.mk.injEq, heq_eq_eq] at hfp; tauto
      rw [this, hv0]
    have hv' : v' = i.allocNextStable := by
      have : v' = v := by simp only [Footprint.arg0, Footprint.mk.injEq, heq_eq_eq] at hfp'; tauto
      rw [this, hv]
    subst hs'_eq
    -- alloc RDY forces opState = OP_IDLE.
    have h_op : i.opState = OP_IDLE Unit_ := alloc_RDY_opState hrdy
    obtain ⟨h_pend, h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩ : s.pendingRead = none ∧
        i.bram_data.readResultA = none ∧ i.bram_data.readResultB = none ∧
        i.bram_index.readResultA = none ∧ i.bram_index.readResultB = none ∧
        i.bram_rever.readResultA = none ∧ i.bram_rever.readResultB = none := by
      rcases h_op_cases with ⟨_, rest⟩ | ⟨h_op_rd, _⟩
      · exact rest
      · simp [h_op] at h_op_rd
    -- enqPtr ≠ 65535 (from RDY) ⇒ no overflow on +1.
    have h_enq_ne : i.enqPtr ≠ 65535 := by
      intro hh
      simp only [M_mkBluealloc.meth_RDY_alloc] at hrdy
      have h2' := (bool_and_eq_BTrue (bool_and_eq_BTrue (bool_and_eq_BTrue hrdy).1).1).2
      rw [hh] at h2'
      simp [(. == .), bool_not, bitvec_simp] at h2'
    have h_enq_toNat : (i.enqPtr + 1#16).toNat = i.enqPtr.toNat + 1 := by bv_omega
    subst hi'
    -- Common index bounds.
    have h_enq_lt_idx_sz : i.enqPtr.toNat < i.bram_index.memory.size := by
      have := i.enqPtr.isLt; omega
    have h_enq_lt_rev_sz : i.enqPtr.toNat < i.bram_rever.memory.size := by
      have := i.enqPtr.isLt; omega
    by_cases h_fresh : i.enqPtr < i.maxEver
    · -- RECYCLED case: enqPtr < maxEver, so allocNextStable is a recycled handle
      -- (bram_index[allocNextStable] = enqPtr, and allocNextStable < maxEver).
      obtain ⟨h_v_max, h_idx_v⟩ := h_frontier.2 h_fresh
      have h_if1_rec : (if i.enqPtr < i.maxEver then BTrue Unit_ else BFalse Unit_) = BTrue Unit_ := if_pos h_fresh
      have h_bn_rec : bool_not (if i.enqPtr < i.maxEver then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ := by
        rw [h_if1_rec]; rfl
      -- recycled alloc writes NO BRAM and does not bump maxEver.
      have hma : (M_mkBluealloc.meth_alloc i).avAction_
          = { i with enqPtr := i.enqPtr + 1#16, allocState := AL_PREFETCH Unit_ } := by
        simp only [M_mkBluealloc.meth_alloc]; rw [h_bn_rec]; rfl
      by_cases h_full : i.enqPtr.toNat + 1 = i.maxEver.toNat
      · -- enqPtr+1 = maxEver: the next prefetch is FRESH (single alloc_prefetch step, BTrue arm).
        -- maxEver = enqPtr+1, so from the post-meth_alloc state alloc_prefetch sees
        -- ¬(enqPtr+1 < maxEver) and takes the BTrue arm (allocNextStable := enqPtr+1, AL_READY).
        have h_max_eq : i.maxEver = i.enqPtr + 1#16 :=
          BitVec.eq_of_toNat_eq (by rw [h_enq_toNat]; omega)
        have h_bn2 : bool_not (if (M_mkBluealloc.meth_alloc i).avAction_.enqPtr
              < (M_mkBluealloc.meth_alloc i).avAction_.maxEver then BTrue Unit_ else BFalse Unit_)
            = BTrue Unit_ := by
          rw [hma]; simp only; rw [h_max_eq, if_neg (by bv_omega)]; rfl
        refine ⟨(M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).2,
          Relation.ReflTransGen.single ⟨.RL_do_alloc_prefetch, ?_⟩, ?_⟩
        · -- prefetch guard fires: allocState=AL_PREFETCH, opState=OP_IDLE, RDY_putB rever.
          have h_aS : (M_mkBluealloc.meth_alloc i).avAction_.allocState = AL_PREFETCH Unit_ := by rw [hma]
          have h_oS : (M_mkBluealloc.meth_alloc i).avAction_.opState = OP_IDLE Unit_ := by rw [hma]; exact h_op
          have h_rB' : (M_mkBluealloc.meth_alloc i).avAction_.bram_rever.readResultB = none := by rw [hma]; exact h_rB
          show M_mkBluealloc.rule_RL_do_alloc_prefetch _ = (BTrue Unit_, _)
          have h_guard_eq :
              (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_alloc_prefetch, h_aS, h_oS, M_mkSimpleBRAM2.meth_RDY_putB, h_rB',
                  bool_and, (.==.), instBEqT_allocstate.beq]
          exact Prod.ext h_guard_eq rfl
        · -- phi0 of the post-prefetch state si2 = {i with enqPtr:=enqPtr+1, allocNextStable:=enqPtr+1, AL_READY}.
          generalize h_si2 : (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).2 = si2
          have hsi2 : si2 = { (M_mkBluealloc.meth_alloc i).avAction_ with
              allocNextStable := (M_mkBluealloc.meth_alloc i).avAction_.enqPtr,
              allocState := AL_READY Unit_ } := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_prefetch]; rw [h_bn2]
          have h_si2_allocState : si2.allocState = AL_READY Unit_ := by rw [hsi2]
          have h_si2_enqPtr : si2.enqPtr = i.enqPtr + 1#16 := by rw [hsi2]; simp only; rw [hma]
          have h_si2_maxEver : si2.maxEver = i.maxEver := by rw [hsi2]; simp only; rw [hma]
          have h_si2_opState : si2.opState = i.opState := by rw [hsi2]; simp only; rw [hma]
          have h_si2_bramData : si2.bram_data = i.bram_data := by rw [hsi2]; simp only; rw [hma]
          have h_si2_bramIndex : si2.bram_index = i.bram_index := by rw [hsi2]; simp only; rw [hma]
          have h_si2_bramRever : si2.bram_rever = i.bram_rever := by rw [hsi2]; simp only; rw [hma]
          have h_si2_allocNext : si2.allocNextStable = i.enqPtr + 1#16 := by rw [hsi2]; simp only; rw [hma]
          have h_v'_max : v'.toNat < i.maxEver.toNat := by rw [hv']; exact h_v_max
          have h_idx_v' : (i.bram_index.memory.getD v'.toNat default).toNat = i.enqPtr.toNat := by
            rw [hv']; exact h_idx_v
          right
          refine ⟨h_vtrue, h_si2_allocState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_si2_enqPtr, h_enq_toNat]; simp [M_mkBluealloc.Spec.alloc_upd, h_enq]
          · rw [h_si2_maxEver]; simp only [M_mkBluealloc.Spec.alloc_upd]; omega
          · -- op-disjunction: still OP_IDLE; all latches none.
            left
            rw [h_si2_opState, h_si2_bramData, h_si2_bramIndex, h_si2_bramRever]
            exact ⟨h_op, by simp [M_mkBluealloc.Spec.alloc_upd, h_pend], h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩
          · rw [h_si2_bramIndex, h_si2_bramData, h_si2_bramRever, h_si2_maxEver]; exact h_bij1
          · -- used↔live: v' (recycled) added; range now [0, enqPtr+1).
            intro t
            rw [h_si2_bramIndex, h_si2_enqPtr, h_si2_maxEver, h_enq_toNat]
            simp only [M_mkBluealloc.Spec.alloc_upd]
            by_cases h_tv : t = v'
            · subst h_tv
              refine iff_of_true ?_ ⟨h_v'_max, by rw [h_idx_v']; omega⟩
              simp [BEq.rfl]
            · have h_tne : (t == v') = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; exact h_tv
              rw [if_neg (by rw [h_tne]; exact Bool.false_ne_true), h_used t]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                by_contra h_ge
                have h_eq : (i.bram_index.memory.getD t.toNat default).toNat = i.enqPtr.toNat := by omega
                obtain ⟨-, -, h_rev_t⟩ := h_bij1 t h1
                obtain ⟨-, -, h_rev_v⟩ := h_bij1 v' h_v'_max
                apply h_tv
                rw [← h_rev_t, ← h_rev_v, h_eq, h_idx_v']
          · rw [h_si2_bramIndex, h_si2_bramData, h_si2_maxEver]
            intro t h_t; simp only [M_mkBluealloc.Spec.alloc_upd]; exact h_data t h_t
          · rw [h_si2_bramIndex]; exact h_isz
          · rw [h_si2_bramRever]; exact h_rsz
          · rw [h_si2_bramData]; exact h_dsz
          · rw [h_si2_bramIndex, h_si2_maxEver]; exact h_idxlt
          · rw [h_si2_maxEver]; intro t h_t; simp only [M_mkBluealloc.Spec.alloc_upd]; exact h_stdef t h_t
          · rw [h_si2_bramData, h_si2_maxEver]; exact h_datdef
          · rw [h_si2_bramIndex, h_si2_bramRever, h_si2_maxEver]; exact h_bij2
          · -- frontier: maxEver=enqPtr+1=enqPtr', allocNextStable=enqPtr+1.
            rw [h_si2_maxEver, h_si2_enqPtr, h_si2_allocNext]
            exact ⟨fun _ => rfl, fun h => absurd h (by rw [h_max_eq]; bv_omega)⟩
      · -- enqPtr+1 < maxEver: the next prefetch is RECYCLED (alloc_prefetch BFalse arm then alloc_wait).
        have h_le_lt : i.enqPtr.toNat + 1 < i.maxEver.toNat := by bv_omega
        have h_lt_bv : i.enqPtr + 1#16 < i.maxEver := by bv_omega
        have h_enq1_lt_max : (i.enqPtr + 1#16).toNat < i.maxEver.toNat := by rw [h_enq_toNat]; exact h_le_lt
        -- w = bram_rever[enqPtr+1]: the recycled handle for the next slot.
        set w := i.bram_rever.memory.getD (i.enqPtr + 1#16).toNat default with hw_def
        obtain ⟨h_w_max, h_idx_w⟩ := h_bij2 (i.enqPtr + 1#16) h_enq1_lt_max
        -- prefetch takes BFalse arm (enqPtr+1 < maxEver ⇒ bool_not (if BTrue) = BFalse).
        have h_bn2 : bool_not (if (M_mkBluealloc.meth_alloc i).avAction_.enqPtr
              < (M_mkBluealloc.meth_alloc i).avAction_.maxEver then BTrue Unit_ else BFalse Unit_)
            = BFalse Unit_ := by
          rw [hma]; simp only; rw [if_pos h_lt_bv]; rfl
        generalize h_sip : (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).2 = sip
        have hsip : sip = { { (M_mkBluealloc.meth_alloc i).avAction_ with
              bram_rever := (M_mkSimpleBRAM2.meth_putB (M_mkBluealloc.meth_alloc i).avAction_.bram_rever
                              (BFalse Unit_) (M_mkBluealloc.meth_alloc i).avAction_.enqPtr default).avAction_ } with
              allocState := AL_WAIT Unit_ } := by
          rw [← h_sip]; simp only [M_mkBluealloc.rule_RL_do_alloc_prefetch]; rw [h_bn2]
        have h_sip_allocState : sip.allocState = AL_WAIT Unit_ := by rw [hsip]
        have h_sip_enqPtr : sip.enqPtr = i.enqPtr + 1#16 := by rw [hsip]; simp only; rw [hma]
        have h_sip_maxEver : sip.maxEver = i.maxEver := by rw [hsip]; simp only; rw [hma]
        have h_sip_opState : sip.opState = i.opState := by rw [hsip]; simp only; rw [hma]
        have h_sip_bramData : sip.bram_data = i.bram_data := by rw [hsip]; simp only; rw [hma]
        have h_sip_bramIndex : sip.bram_index = i.bram_index := by rw [hsip]; simp only; rw [hma]
        have h_sip_rrB : sip.bram_rever.readResultB = some w := by
          rw [hsip]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB, hw_def]
        -- fire prefetch then wait
        refine ⟨(M_mkBluealloc.rule_RL_do_alloc_wait sip).2,
          Relation.ReflTransGen.tail (b := sip)
            (Relation.ReflTransGen.single ⟨.RL_do_alloc_prefetch, ?_⟩) ⟨.RL_do_alloc_wait, ?_⟩, ?_⟩
        · -- prefetch guard fires; target is sip (= the generalized result).
          show M_mkBluealloc.rule_RL_do_alloc_prefetch _ = (BTrue Unit_, _)
          have h_aS : (M_mkBluealloc.meth_alloc i).avAction_.allocState = AL_PREFETCH Unit_ := by rw [hma]
          have h_oS : (M_mkBluealloc.meth_alloc i).avAction_.opState = OP_IDLE Unit_ := by rw [hma]; exact h_op
          have h_rB' : (M_mkBluealloc.meth_alloc i).avAction_.bram_rever.readResultB = none := by rw [hma]; exact h_rB
          have h_guard_eq :
              (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_alloc_prefetch, h_aS, h_oS, M_mkSimpleBRAM2.meth_RDY_putB, h_rB',
                  bool_and, (.==.), instBEqT_allocstate.beq]
          exact Prod.ext h_guard_eq h_sip
        · -- wait guard fires: AL_WAIT, RDY_readB (readResultB = some w).
          show M_mkBluealloc.rule_RL_do_alloc_wait _ = (BTrue Unit_, _)
          have h_guard_w : (M_mkBluealloc.rule_RL_do_alloc_wait sip).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_alloc_wait, h_sip_allocState, M_mkSimpleBRAM2.meth_RDY_readB,
                  h_sip_rrB, bool_and, (.==.), instBEqT_allocstate.beq]
          exact Prod.ext h_guard_w rfl
        · -- phi0 of the post-wait state si2.
          generalize h_si2 : (M_mkBluealloc.rule_RL_do_alloc_wait sip).2 = si2
          have h_si2_allocState : si2.allocState = AL_READY Unit_ := by
            rw [← h_si2]; simp [M_mkBluealloc.rule_RL_do_alloc_wait]
          have h_si2_enqPtr : si2.enqPtr = i.enqPtr + 1#16 := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait]; rw [h_sip_enqPtr]
          have h_si2_maxEver : si2.maxEver = i.maxEver := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait]; rw [h_sip_maxEver]
          have h_si2_opState : si2.opState = i.opState := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait]; rw [h_sip_opState]
          have h_si2_bramData : si2.bram_data = i.bram_data := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait]; rw [h_sip_bramData]
          have h_si2_bramIndex : si2.bram_index = i.bram_index := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait]; rw [h_sip_bramIndex]
          have h_si2_allocNext : si2.allocNextStable = w := by
            rw [← h_si2]; simp only [M_mkBluealloc.rule_RL_do_alloc_wait, M_mkSimpleBRAM2.meth_readB]
            rw [h_sip_rrB]; rfl
          have h_si2_bramRever : si2.bram_rever = i.bram_rever := by
            rw [← h_si2]
            simp only [M_mkBluealloc.rule_RL_do_alloc_wait, M_mkSimpleBRAM2.meth_readB]
            rw [hsip]; simp only; rw [hma]
            simp only [M_mkSimpleBRAM2.meth_putB]
            rw [← h_rB]
          have h_v'_max : v'.toNat < i.maxEver.toNat := by rw [hv']; exact h_v_max
          have h_idx_v' : (i.bram_index.memory.getD v'.toNat default).toNat = i.enqPtr.toNat := by
            rw [hv']; exact h_idx_v
          right
          refine ⟨h_vtrue, h_si2_allocState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_si2_enqPtr, h_enq_toNat]; simp [M_mkBluealloc.Spec.alloc_upd, h_enq]
          · rw [h_si2_maxEver]; simp only [M_mkBluealloc.Spec.alloc_upd]; omega
          · left
            rw [h_si2_opState, h_si2_bramData, h_si2_bramIndex, h_si2_bramRever]
            exact ⟨h_op, by simp [M_mkBluealloc.Spec.alloc_upd, h_pend], h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩
          · rw [h_si2_bramIndex, h_si2_bramData, h_si2_bramRever, h_si2_maxEver]; exact h_bij1
          · -- used↔live: v' (recycled) added; range now [0, enqPtr+1). Identical to the single-step case.
            intro t
            rw [h_si2_bramIndex, h_si2_enqPtr, h_si2_maxEver, h_enq_toNat]
            simp only [M_mkBluealloc.Spec.alloc_upd]
            by_cases h_tv : t = v'
            · subst h_tv
              refine iff_of_true ?_ ⟨h_v'_max, by rw [h_idx_v']; omega⟩
              simp [BEq.rfl]
            · have h_tne : (t == v') = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; exact h_tv
              rw [if_neg (by rw [h_tne]; exact Bool.false_ne_true), h_used t]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                by_contra h_ge
                have h_eq : (i.bram_index.memory.getD t.toNat default).toNat = i.enqPtr.toNat := by omega
                obtain ⟨-, -, h_rev_t⟩ := h_bij1 t h1
                obtain ⟨-, -, h_rev_v⟩ := h_bij1 v' h_v'_max
                apply h_tv
                rw [← h_rev_t, ← h_rev_v, h_eq, h_idx_v']
          · rw [h_si2_bramIndex, h_si2_bramData, h_si2_maxEver]
            intro t h_t; simp only [M_mkBluealloc.Spec.alloc_upd]; exact h_data t h_t
          · rw [h_si2_bramIndex]; exact h_isz
          · rw [h_si2_bramRever]; exact h_rsz
          · rw [h_si2_bramData]; exact h_dsz
          · rw [h_si2_bramIndex, h_si2_maxEver]; exact h_idxlt
          · rw [h_si2_maxEver]; intro t h_t; simp only [M_mkBluealloc.Spec.alloc_upd]; exact h_stdef t h_t
          · rw [h_si2_bramData, h_si2_maxEver]; exact h_datdef
          · rw [h_si2_bramIndex, h_si2_bramRever, h_si2_maxEver]; exact h_bij2
          · -- frontier: enqPtr+1 < maxEver (recycled branch); allocNextStable = w with bram_index[w] = enqPtr+1.
            rw [h_si2_maxEver, h_si2_enqPtr, h_si2_bramIndex, h_si2_allocNext]
            refine ⟨fun h => absurd h (by bv_omega), fun _ => ⟨h_w_max, ?_⟩⟩
            exact congrArg BitVec.toNat h_idx_w
    · -- FRESH case: enqPtr ≥ maxEver ⇒ allocNextStable = enqPtr = v.
      have h_not_lt : ¬ (i.enqPtr < i.maxEver) := h_fresh
      have h_enq_ge_max : i.maxEver.toNat ≤ i.enqPtr.toNat := by bv_omega
      have h_enq_eq_max : i.enqPtr.toNat = i.maxEver.toNat := by omega
      -- frontier (fresh side) gives allocNextStable = enqPtr, hence v = enqPtr.
      have h_v_enq : v = i.enqPtr := by rw [hv]; exact h_frontier.1 h_enq_ge_max
      have h_not_lt' : ¬ (i.enqPtr + 1#16 < i.enqPtr + 1#16) := by bv_omega
      have h_enq1_not_lt_max : ¬ (i.enqPtr + 1#16 < i.maxEver) := by bv_omega
      have h_if1 : (if i.enqPtr < i.maxEver then BTrue Unit_ else BFalse Unit_) = BFalse Unit_ :=
        if_neg h_not_lt
      -- one alloc_prefetch step → AL_READY.
      refine ⟨(M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).2,
        Relation.ReflTransGen.single ⟨.RL_do_alloc_prefetch, ?_⟩, ?_⟩
      · -- the alloc_prefetch rule fires from post-meth_alloc state.
        have h_post_rB : (M_mkBluealloc.meth_alloc i).avAction_.bram_rever.readResultB = none := by
          simp only [M_mkBluealloc.meth_alloc]
          split
          · rename_i h_b; split at h_b
            · simp_all [M_mkSimpleBRAM2.meth_putB, h_rB]
            · exact h_rB
          · exact h_rB
        have h_allocState : (M_mkBluealloc.meth_alloc i).avAction_.allocState = AL_PREFETCH Unit_ := by
          simp [M_mkBluealloc.meth_alloc]
        have h_opState : (M_mkBluealloc.meth_alloc i).avAction_.opState = OP_IDLE Unit_ := by
          simp [M_mkBluealloc.meth_alloc]; exact h_op
        show M_mkBluealloc.rule_RL_do_alloc_prefetch _ = (BTrue Unit_, _)
        have h_guard_eq :
            (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).1 = BTrue Unit_ := by
          simp [M_mkBluealloc.rule_RL_do_alloc_prefetch, h_allocState, h_opState,
                M_mkSimpleBRAM2.meth_RDY_putB, h_post_rB, bool_and,
                (.==.), instBEqT_allocstate.beq]
        exact Prod.ext h_guard_eq rfl
      · -- phi0 of the post-prefetch state against alloc_upd s v.
        -- Explicit form of the post-meth_alloc state (fresh = BTrue arm of every inner match,
        -- since bool_not (if enqPtr < maxEver ..) = bool_not BFalse = BTrue).
        have h_bn : bool_not (if i.enqPtr < i.maxEver then BTrue Unit_ else BFalse Unit_)
            = BTrue Unit_ := by rw [h_if1]; rfl
        have hma : (M_mkBluealloc.meth_alloc i).avAction_ =
            { i with
              bram_index := (M_mkSimpleBRAM2.meth_putB i.bram_index (BTrue Unit_) i.enqPtr i.enqPtr).avAction_,
              bram_rever := (M_mkSimpleBRAM2.meth_putB i.bram_rever (BTrue Unit_) i.enqPtr i.enqPtr).avAction_,
              maxEver := i.enqPtr + 1#16,
              enqPtr := i.enqPtr + 1#16,
              allocState := AL_PREFETCH Unit_ } := by
          simp only [M_mkBluealloc.meth_alloc]; rw [h_bn]; rfl
        -- The post-prefetch state: alloc_prefetch sees enqPtr+1 ≥ maxEver=enqPtr+1, takes BTrue arm.
        have h_bn2 : bool_not (if (M_mkBluealloc.meth_alloc i).avAction_.enqPtr
              < (M_mkBluealloc.meth_alloc i).avAction_.maxEver then BTrue Unit_ else BFalse Unit_)
            = BTrue Unit_ := by
          rw [hma]; simp only; rw [if_neg h_not_lt']; rfl
        generalize h_si2 :
          (M_mkBluealloc.rule_RL_do_alloc_prefetch (M_mkBluealloc.meth_alloc i).avAction_).2 = si2
        have hsi2 : si2 = { (M_mkBluealloc.meth_alloc i).avAction_ with
            allocNextStable := (M_mkBluealloc.meth_alloc i).avAction_.enqPtr,
            allocState := AL_READY Unit_ } := by
          rw [← h_si2]
          simp only [M_mkBluealloc.rule_RL_do_alloc_prefetch]; rw [h_bn2]
        have h_si2_allocState : si2.allocState = AL_READY Unit_ := by rw [hsi2]
        have h_si2_enqPtr : si2.enqPtr = i.enqPtr + 1#16 := by rw [hsi2]; simp only; rw [hma]
        have h_si2_maxEver : si2.maxEver = i.enqPtr + 1#16 := by rw [hsi2]; simp only; rw [hma]
        have h_si2_opState : si2.opState = i.opState := by rw [hsi2]; simp only; rw [hma]
        have h_si2_bramIndex_mem : si2.bram_index.memory =
            i.bram_index.memory.setIfInBounds i.enqPtr.toNat i.enqPtr := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_bramData : si2.bram_data = i.bram_data := by rw [hsi2]; simp only; rw [hma]
        have h_si2_bramRever_mem : si2.bram_rever.memory =
            i.bram_rever.memory.setIfInBounds i.enqPtr.toNat i.enqPtr := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_iA : si2.bram_index.readResultA = i.bram_index.readResultA := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_iB : si2.bram_index.readResultB = i.bram_index.readResultB := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_rA : si2.bram_rever.readResultA = i.bram_rever.readResultA := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_rB : si2.bram_rever.readResultB = i.bram_rever.readResultB := by
          rw [hsi2]; simp only; rw [hma]; simp [M_mkSimpleBRAM2.meth_putB]
        have h_si2_allocNext : si2.allocNextStable = i.enqPtr + 1#16 := by
          rw [hsi2]; simp only; rw [hma]
        -- Now build the new phi0.  s' = alloc_upd s v with v = enqPtr.
        right
        refine ⟨h_vtrue, h_si2_allocState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- enqPtr.toNat = numAllocated + 1
          rw [h_si2_enqPtr, h_enq_toNat]
          simp [M_mkBluealloc.Spec.alloc_upd, h_enq]
        · -- numAllocated+1 ≤ maxEver' = enqPtr+1
          rw [h_si2_maxEver, h_enq_toNat]
          simp [M_mkBluealloc.Spec.alloc_upd, ← h_enq]
        · -- op-disjunction: still OP_IDLE.
          left
          refine ⟨h_si2_opState.trans h_op, by simp [M_mkBluealloc.Spec.alloc_upd, h_pend], ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_si2_bramData]; exact h_dA
          · rw [h_si2_bramData]; exact h_dB
          · rw [h_si2_iA]; exact h_iA
          · rw [h_si2_iB]; exact h_iB
          · rw [h_si2_rA]; exact h_rA
          · rw [h_si2_rB]; exact h_rB
        · -- bij1
          intro t h_t
          rw [h_si2_maxEver, h_enq_toNat] at h_t
          rw [h_si2_bramIndex_mem, h_si2_bramData, h_si2_bramRever_mem]
          by_cases h_t_new : t.toNat = i.enqPtr.toNat
          · have h_idx : (i.bram_index.memory.setIfInBounds i.enqPtr.toNat i.enqPtr).getD t.toNat default = i.enqPtr := by
              rw [h_t_new]; exact setIB_same _ _ _ _ h_enq_lt_idx_sz
            have h_t_eq : t = i.enqPtr := BitVec.eq_of_toNat_eq h_t_new
            refine ⟨?_, ?_, ?_⟩
            · rw [h_idx]; have := i.enqPtr.isLt; omega
            · rw [h_idx, setIB_size]; have := i.enqPtr.isLt; omega
            · rw [h_idx, h_t_eq]; exact setIB_same _ _ _ _ h_enq_lt_rev_sz
          · have h_t_old : t.toNat < i.maxEver.toNat := by omega
            obtain ⟨hb1, hb2, hb3⟩ := h_bij1 t h_t_old
            have h_idx : (i.bram_index.memory.setIfInBounds i.enqPtr.toNat i.enqPtr).getD t.toNat default
                = i.bram_index.memory.getD t.toNat default := setIB_diff _ _ _ _ _ (Ne.symm h_t_new)
            have h_u_old : (i.bram_index.memory.getD t.toNat default).toNat < i.maxEver.toNat := h_idxlt t h_t_old
            have h_u_ne : (i.bram_index.memory.getD t.toNat default).toNat ≠ i.enqPtr.toNat := by omega
            refine ⟨?_, ?_, ?_⟩
            · rw [h_idx]; exact hb1
            · rw [h_idx, setIB_size]; exact hb2
            · rw [h_idx, setIB_diff _ _ _ _ _ (Ne.symm h_u_ne)]; exact hb3
        · -- used↔live: v=enqPtr added; range now [0, enqPtr+1).
          intro t
          rw [h_si2_bramIndex_mem, h_si2_enqPtr, h_si2_maxEver, h_enq_toNat]
          have h_v'_enq : v' = i.enqPtr := by rw [hv', ← hv, h_v_enq]
          simp only [M_mkBluealloc.Spec.alloc_upd, h_v'_enq]
          by_cases h_t_new : t.toNat = i.enqPtr.toNat
          · have h_te : t = i.enqPtr := BitVec.eq_of_toNat_eq h_t_new
            subst h_te
            rw [setIB_same _ _ _ _ h_enq_lt_idx_sz]
            simp only [BEq.rfl]
            exact iff_of_true rfl ⟨by omega, by omega⟩
          · have h_tne : (t == i.enqPtr) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro hh; exact h_t_new (congrArg BitVec.toNat hh)
            rw [setIB_diff _ _ _ _ _ (Ne.symm h_t_new)]
            simp only [h_tne]; rw [if_neg (by decide)]
            rw [h_used t]
            constructor
            · rintro ⟨hm1, hm2⟩; exact ⟨by omega, by omega⟩
            · rintro ⟨hm1, hm2⟩
              have h_u_old := h_idxlt t (by omega)
              exact ⟨by omega, by omega⟩
        · -- data agreement over all s < maxEver' (= enqPtr+1); alloc_upd leaves store unchanged.
          intro t h_t
          rw [h_si2_maxEver, h_enq_toNat] at h_t
          rw [h_si2_bramIndex_mem, h_si2_bramData]
          simp only [M_mkBluealloc.Spec.alloc_upd]
          by_cases h_t_new : t.toNat = i.enqPtr.toNat
          · have h_t_eq : t = i.enqPtr := BitVec.eq_of_toNat_eq h_t_new
            rw [h_t_eq, setIB_same _ _ _ _ h_enq_lt_idx_sz,
                h_datdef i.enqPtr (by omega), h_stdef i.enqPtr (by omega)]
          · rw [setIB_diff _ _ _ _ _ (Ne.symm h_t_new)]
            exact h_data t (by omega)
        · rw [h_si2_bramIndex_mem, setIB_size]; exact h_isz
        · rw [h_si2_bramRever_mem, setIB_size]; exact h_rsz
        · rw [h_si2_bramData]; exact h_dsz
        · -- idxlt
          intro t h_t
          rw [h_si2_maxEver, h_enq_toNat] at h_t
          rw [h_si2_bramIndex_mem, h_si2_maxEver, h_enq_toNat]
          by_cases h_t_new : t.toNat = i.enqPtr.toNat
          · rw [h_t_new, setIB_same _ _ _ _ h_enq_lt_idx_sz]; omega
          · have h_t_old : t.toNat < i.maxEver.toNat := by omega
            rw [setIB_diff _ _ _ _ _ (Ne.symm h_t_new)]
            have := h_idxlt t h_t_old; omega
        · -- store pristine: ≥ maxEver' = enqPtr+1; alloc_upd leaves store unchanged.
          intro t h_t
          rw [h_si2_maxEver, h_enq_toNat] at h_t
          simp only [M_mkBluealloc.Spec.alloc_upd]
          exact h_stdef t (by omega)
        · -- data pristine: ≥ maxEver'.
          intro u h_u
          rw [h_si2_maxEver, h_enq_toNat] at h_u
          rw [h_si2_bramData]
          exact h_datdef u (by omega)
        · -- bij2 (inverse): new slot enqPtr, old slots preserved.
          intro u h_u
          rw [h_si2_maxEver, h_enq_toNat] at h_u
          rw [h_si2_bramIndex_mem, h_si2_bramRever_mem, h_si2_maxEver, h_enq_toNat]
          by_cases h_u_new : u.toNat = i.enqPtr.toNat
          · have h_u_eq : u = i.enqPtr := BitVec.eq_of_toNat_eq h_u_new
            rw [h_u_eq, setIB_same _ _ _ _ h_enq_lt_rev_sz]
            refine ⟨by omega, ?_⟩
            rw [setIB_same _ _ _ _ h_enq_lt_idx_sz]
          · have h_u_old : u.toNat < i.maxEver.toNat := by omega
            rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_new)]
            obtain ⟨h_rev_lt, h_idx_eq⟩ := h_bij2 u h_u_old
            have h_rev_ne : (i.bram_rever.memory.getD u.toNat default).toNat ≠ i.enqPtr.toNat := by omega
            rw [setIB_diff _ _ _ _ _ (Ne.symm h_rev_ne)]
            exact ⟨by omega, h_idx_eq⟩
        · -- frontier: new state has maxEver' = enqPtr' = enqPtr+1, so the ≥ branch
          -- requires allocNextStable' = enqPtr'.  But alloc_prefetch left allocNextStable = enqPtr,
          -- NOT enqPtr+1.  This is the AL_PREFETCH→AL_READY identity arm: allocNextStable stays enqPtr.
          rw [h_si2_maxEver, h_si2_enqPtr, h_si2_allocNext]
          exact ⟨fun _ => rfl, fun h => absurd h (by bv_omega)⟩

@[local grind →] theorem reach_phi0_again_free (i i' : ImplModule.State) (s s' : SpecModule.State) (free_f : BitVec 16) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.free, Footprint.arg1 free_f v⟩ i' →
  SpecModule.getMethod s ⟨.free, Footprint.arg1 free_f v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hp hm hsm
  -- Decompose impl method: i' = (meth_free i free_f).avAction_, RDY holds.
  dsimp [ImplModule, Module.getMethod, ofAVMethod1] at hm
  obtain ⟨a1, vi, hmeth, hfp, hrdy⟩ := hm
  have ha1 : a1 = free_f := Footprint.arg1_inj hfp.symm
  subst a1
  have hi' : i' = (M_mkBluealloc.meth_free i free_f).avAction_ := by rw [hmeth]
  -- Decompose spec method.
  dsimp [SpecModule, Module.getMethod] at hsm
  obtain ⟨a1', v'', hfp', hsbody⟩ := hsm
  have ha1' : a1' = free_f := Footprint.arg1_inj hfp'.symm
  subst a1'
  rcases hp with h_poison | h_valid
  · -- poisoned: s' poisoned ⇒ phi0 via Or.inl for ANY impl state (just stay put).
    rw [if_neg (by simp [h_poison])] at hsbody
    exact ⟨i', Relation.ReflTransGen.refl, Or.inl hsbody⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    have h_op : i.opState = OP_IDLE Unit_ := by
      rcases h_op_cases with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exfalso
        simp [isReady, bsv_methods, M_mkBluealloc.meth_RDY_free, h, (. == .),
              bool_and] at hrdy
    obtain ⟨h_pend, h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩ : s.pendingRead = none ∧
        i.bram_data.readResultA = none ∧ i.bram_data.readResultB = none ∧
        i.bram_index.readResultA = none ∧ i.bram_index.readResultB = none ∧
        i.bram_rever.readResultA = none ∧ i.bram_rever.readResultB = none := by
      rcases h_op_cases with ⟨_, rest⟩ | ⟨h_op_rd, _⟩
      · exact rest
      · simp [h_op] at h_op_rd
    -- enqPtr ≠ 0 (from RDY).
    have h_enq_ne_zero : i.enqPtr ≠ 0#16 := by
      intro hh
      simp [isReady, bsv_methods, M_mkBluealloc.meth_RDY_free, bool_and, bool_not, h_alloc, h_op, hh,
            (. == .), instBEqT_allocstate.beq] at hrdy
    have h_enq_pos : 0 < i.enqPtr.toNat := by
      have : i.enqPtr.toNat ≠ 0 := fun h => h_enq_ne_zero (BitVec.eq_of_toNat_eq h)
      omega
    have h_enq_sub_toNat : (i.enqPtr - 1#16).toNat = i.enqPtr.toNat - 1 := by bv_omega
    have h_enq_le_max : i.enqPtr.toNat ≤ i.maxEver.toNat := by rw [h_enq]; exact h_le
    have h_enq_sub_lt_max : (i.enqPtr - 1#16).toNat < i.maxEver.toNat := by
      rw [h_enq_sub_toNat]; omega
    have h_enq_sub_lt_max_bv : i.enqPtr - 1#16 < i.maxEver := h_enq_sub_lt_max
    have h_enq_sub_lt_65536 : (i.enqPtr - 1#16).toNat < 65536 := (i.enqPtr - 1#16).isLt
    subst hi'
    -- The spec body: split poison vs live handle.
    rw [if_pos h_vtrue] at hsbody
    simp only [M_mkBluealloc.Spec.meth_free] at hsbody
    obtain ⟨hsmeth, -⟩ := hsbody
    by_cases h_use : s.used free_f
    · -- LIVE handle: run the full 5-rule FSM and prove the rich phi0.
      rw [if_pos h_use] at hsmeth
      have hs' : s' = { s with numAllocated := s.numAllocated - 1, used := fun a => if a == free_f then false else s.used a } := (congrArg t_actionvalue_.avAction_ hsmeth).symm
      subst hs'
      -- u_freed and addr-related bounds (replaces old h_addr_alloc).
      have h_addr_max : free_f.toNat < i.maxEver.toNat := ((h_used free_f).1 h_use).1
      have h_uaddr_lt_enq : (i.bram_index.memory.getD free_f.toNat default).toNat < i.enqPtr.toNat :=
        ((h_used free_f).1 h_use).2
      -- u_freed = bram_index[addr]
      set u_freed : BitVec 16 := i.bram_index.memory.getD free_f.toNat default with hu_freed_def
      have h_u_freed_lt_max : u_freed.toNat < i.maxEver.toNat := h_idxlt free_f h_addr_max
      have h_u_freed_lt_65536 : u_freed.toNat < 65536 := u_freed.isLt
      have h_u_freed_lt_idx_sz : u_freed.toNat < i.bram_index.memory.size := by omega
      have h_u_freed_lt_rev_sz : u_freed.toNat < i.bram_rever.memory.size := by omega
      have h_u_freed_lt_data_sz : u_freed.toNat < i.bram_data.memory.size := by omega
      -- s_last = bram_rever[enqPtr-1]
      set s_last : BitVec 16 := i.bram_rever.memory.getD (i.enqPtr - 1#16).toNat default with hs_last_def
      obtain ⟨h_s_last_lt_max, h_idx_s_last⟩ := h_bij2 (i.enqPtr - 1#16) h_enq_sub_lt_max
      -- The post-meth_free state.
      set sif : ImplModule.State := (M_mkBluealloc.meth_free i free_f).avAction_ with hsif_def
      -- 5-rule chain intermediates.
      set si2 := (M_mkBluealloc.rule_RL_do_free_lookup sif).2 with hsi2_def
      set si3 := (M_mkBluealloc.rule_RL_do_free_read si2).2 with hsi3_def
      set si4 := (M_mkBluealloc.rule_RL_do_free_write si3).2 with hsi4_def
      set si5 := (M_mkBluealloc.rule_RL_do_alloc_prefetch si4).2 with hsi5_def
      set si6 := (M_mkBluealloc.rule_RL_do_alloc_wait si5).2 with hsi6_def
      -- Final-state field facts (ported from old proof).
      have h_si6_allocState : si6.allocState = AL_READY Unit_ := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait]
      have h_si6_enqPtr : si6.enqPtr = i.enqPtr - 1#16 := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · rfl
      have h_si6_maxEver : si6.maxEver = i.maxEver := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · rfl
      have h_si6_opState : si6.opState = OP_IDLE Unit_ := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · rfl
      have h_enq_sub_lt_rev_sz : (i.enqPtr - 1#16).toNat < i.bram_rever.memory.size := by
        rw [h_enq_sub_toNat]; omega
      have h_si6_allocNext : si6.allocNextStable = free_f := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, M_mkSimpleBRAM2.meth_readB, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods,
                   M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
                   M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b
          simp [bool_not] at h_b
        · simp only [ActionValue, Option.getD_some]
          rw [setIB_same _ _ _ _ (by rw [setIB_size]; exact h_enq_sub_lt_rev_sz)]
      have h_si6_readResults :
          si6.bram_data.readResultA = none ∧ si6.bram_data.readResultB = none ∧
          si6.bram_index.readResultA = none ∧ si6.bram_index.readResultB = none ∧
          si6.bram_rever.readResultA = none ∧ si6.bram_rever.readResultB = none := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods,
                   M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
                   M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB, ActionValue]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b
          simp [bool_not] at h_b
        · simp_all [h_dA, h_dB, h_iA, h_iB, h_rA, h_rB]
      -- BRAM memories after the chain.
      set d_last : BitVec 32 := i.bram_data.memory.getD (i.enqPtr - 1#16).toNat default with hd_last_def
      set d_freed : BitVec 32 := i.bram_data.memory.getD u_freed.toNat default with hd_freed_def
      have arr_eq_local : ∀ {α : Type} [Inhabited α] (a : Array α) (i : Nat) (d : α),
          a.getD i d = (a[i]?.getD d) := by
        intros; unfold Array.getD; split <;> simp_all
      have h_si6_bramData_mem : si6.bram_data.memory =
          (i.bram_data.memory.setIfInBounds u_freed.toNat d_last).setIfInBounds
            (i.enqPtr - 1#16).toNat d_freed := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods,
                   M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
                   M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · simp only [ActionValue]
          simp [u_freed, d_last, d_freed, arr_eq_local]
      have h_si6_bramRever_mem : si6.bram_rever.memory =
          (i.bram_rever.memory.setIfInBounds u_freed.toNat s_last).setIfInBounds
            (i.enqPtr - 1#16).toNat free_f := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods,
                   M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
                   M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · simp only [ActionValue]
          simp [u_freed, s_last, arr_eq_local]
      have h_si6_bramIndex_mem : si6.bram_index.memory =
          (i.bram_index.memory.setIfInBounds s_last.toNat u_freed).setIfInBounds
            free_f.toNat (i.enqPtr - 1#16) := by
        simp only [si6, M_mkBluealloc.rule_RL_do_alloc_wait, si5,
                   M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                   si3, M_mkBluealloc.rule_RL_do_free_read, si2,
                   M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods,
                   M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB,
                   M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_readB]
        split
        · rename_i h_b
          exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b; simp [bool_not] at h_b
        · simp only [ActionValue]
          simp [u_freed, s_last, arr_eq_local]
      -- bij/data facts pulled out for use below.
      have h_rev_u_freed : i.bram_rever.memory.getD u_freed.toNat default = free_f :=
        (h_bij1 free_f h_addr_max).2.2
      have h_data_u_freed : i.bram_data.memory.getD u_freed.toNat default = s.store free_f :=
        h_data free_f h_addr_max
      have h_data_enq_sub : i.bram_data.memory.getD (i.enqPtr - 1#16).toNat default = s.store s_last := by
        have := h_data s_last h_s_last_lt_max
        rw [h_idx_s_last] at this; exact this
      -- Combined bijection+data invariant for the final state, for each s < maxEver.
      -- (Ported from the old proof; new phi0 splits this into bij1 (first 3) + data (4th).)
      have h_combined : ∀ (t : BitVec 16), t.toNat < i.maxEver.toNat →
          (let u := si6.bram_index.memory.getD t.toNat default
           u.toNat < si6.bram_data.memory.size ∧
           u.toNat < si6.bram_rever.memory.size ∧
           si6.bram_rever.memory.getD u.toNat default = t ∧
           si6.bram_data.memory.getD u.toNat default = s.store t) := by
        intro t h_t
        simp only
        rw [h_si6_bramIndex_mem, h_si6_bramRever_mem, h_si6_bramData_mem]
        by_cases h_s_addr : t = free_f
        · -- t = addr: new bram_index[addr] = enqPtr-1.
          subst h_s_addr
          have h_idx_eq : ((i.bram_index.memory.setIfInBounds s_last.toNat u_freed).setIfInBounds
              t.toNat (i.enqPtr - 1#16)).getD t.toNat default = i.enqPtr - 1#16 :=
            setIB_same _ _ _ _ (by rw [setIB_size]; omega)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [h_idx_eq, setIB_size, setIB_size]
            have : (i.enqPtr - 1#16).toNat < 65536 := h_enq_sub_lt_65536; omega
          · rw [h_idx_eq, setIB_size, setIB_size]
            have : (i.enqPtr - 1#16).toNat < 65536 := h_enq_sub_lt_65536; omega
          · rw [h_idx_eq]
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
          · rw [h_idx_eq]
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
            exact h_data_u_freed
        · by_cases h_s_slast : t = s_last
          · -- t = s_last: new bram_index[s_last] = u_freed.
            rw [h_s_slast]
            have h_s_last_lt_idx_sz : s_last.toNat < i.bram_index.memory.size := by omega
            have h_s_ne_addr : s_last.toNat ≠ free_f.toNat := by
              intro h; apply h_s_addr; rw [h_s_slast]; exact BitVec.eq_of_toNat_eq h
            have h_idx_eq : ((i.bram_index.memory.setIfInBounds s_last.toNat u_freed).setIfInBounds
                free_f.toNat (i.enqPtr - 1#16)).getD s_last.toNat default = u_freed := by
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              exact setIB_same _ _ _ _ h_s_last_lt_idx_sz
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [h_idx_eq, setIB_size, setIB_size]; omega
            · rw [h_idx_eq, setIB_size, setIB_size]; omega
            · rw [h_idx_eq]
              by_cases h_uf_enq : u_freed.toNat = (i.enqPtr - 1#16).toNat
              · rw [h_uf_enq]
                rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
                have h_rev_eq : i.bram_rever.memory.getD u_freed.toNat default = s_last := by rw [h_uf_enq]
                rw [h_rev_u_freed] at h_rev_eq; exact h_rev_eq
              · rw [setIB_diff _ _ _ _ _ (Ne.symm h_uf_enq)]
                exact setIB_same _ _ _ _ h_u_freed_lt_rev_sz
            · rw [h_idx_eq]
              by_cases h_uf_enq : u_freed.toNat = (i.enqPtr - 1#16).toNat
              · rw [h_uf_enq]
                rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
                have h_rev_eq : i.bram_rever.memory.getD u_freed.toNat default = s_last := by rw [h_uf_enq]
                rw [h_rev_u_freed] at h_rev_eq
                rw [← h_rev_eq]; exact h_data_u_freed
              · rw [setIB_diff _ _ _ _ _ (Ne.symm h_uf_enq)]
                rw [setIB_same _ _ _ _ h_u_freed_lt_data_sz]
                exact h_data_enq_sub
          · -- t ∉ {addr, s_last}: bram_index[t] unchanged.
            have h_s_ne_addr : t.toNat ≠ free_f.toNat := fun h => h_s_addr (BitVec.eq_of_toNat_eq h)
            have h_s_ne_slast : t.toNat ≠ s_last.toNat := fun h => h_s_slast (BitVec.eq_of_toNat_eq h)
            have h_idx_eq : ((i.bram_index.memory.setIfInBounds s_last.toNat u_freed).setIfInBounds
                free_f.toNat (i.enqPtr - 1#16)).getD t.toNat default =
                  i.bram_index.memory.getD t.toNat default := by
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_slast)]
            obtain ⟨h_u_data_bnd, h_u_rever_bnd, h_rev⟩ := h_bij1 t h_t
            have h_dat := h_data t h_t
            have h_u_ne_ufreed : (i.bram_index.memory.getD t.toNat default).toNat ≠ u_freed.toNat := by
              intro h_eq
              apply h_s_ne_addr
              have : i.bram_rever.memory.getD u_freed.toNat default = t := by rw [← h_eq]; exact h_rev
              rw [this] at h_rev_u_freed
              exact congrArg BitVec.toNat h_rev_u_freed
            have h_u_ne_enqsub : (i.bram_index.memory.getD t.toNat default).toNat ≠
                (i.enqPtr - 1#16).toNat := by
              intro h_eq
              apply h_s_ne_slast
              have h_bv : i.bram_rever.memory.getD (i.enqPtr - 1#16).toNat default = t := by
                rw [← h_eq]; exact h_rev
              have h_seq : t = s_last := by
                rw [show s_last = i.bram_rever.memory.getD (i.enqPtr - 1#16).toNat default from rfl]
                exact h_bv.symm
              exact congrArg BitVec.toNat h_seq
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [h_idx_eq, setIB_size, setIB_size]; exact h_u_data_bnd
            · rw [h_idx_eq, setIB_size, setIB_size]; exact h_u_rever_bnd
            · rw [h_idx_eq]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_enqsub)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_ufreed)]
              exact h_rev
            · rw [h_idx_eq]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_enqsub)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_ufreed)]
              exact h_dat
      -- Build the chain + phi0.
      refine ⟨si6, ?_, ?_⟩
      · -- 5-step chain via ReflTransGen.tail.
        refine Relation.ReflTransGen.tail (b := si5)
          (Relation.ReflTransGen.tail (b := si4)
            (Relation.ReflTransGen.tail (b := si3)
              (Relation.ReflTransGen.tail (b := si2)
                (Relation.ReflTransGen.single ⟨.RL_do_free_lookup, ?_⟩)
                ⟨.RL_do_free_read, ?_⟩)
              ⟨.RL_do_free_write, ?_⟩)
            ⟨.RL_do_alloc_prefetch, ?_⟩)
          ⟨.RL_do_alloc_wait, ?_⟩
        · -- free_lookup fires from post-meth_free state.
          show M_mkBluealloc.rule_RL_do_free_lookup _ = (BTrue Unit_, _)
          have hg : (M_mkBluealloc.rule_RL_do_free_lookup sif).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free,
                  M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_putA,
                  M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_putA,
                  bool_and, (. == .),
                  h_dA, h_dB, h_iA, h_iB, h_rA, h_rB]
          exact Prod.ext hg rfl
        · -- free_read fires from si2.
          show M_mkBluealloc.rule_RL_do_free_read _ = (BTrue Unit_, _)
          have hg : (M_mkBluealloc.rule_RL_do_free_read si2).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_free_read, si2, M_mkBluealloc.rule_RL_do_free_lookup,
                  sif, M_mkBluealloc.meth_free,
                  M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
                  M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
                  M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA,
                  bool_and, (. == .),
                  h_dA, h_dB, h_iA, h_iB, h_rA, h_rB]
          exact Prod.ext hg rfl
        · -- free_write fires from si3.
          show M_mkBluealloc.rule_RL_do_free_write _ = (BTrue Unit_, _)
          have hg : (M_mkBluealloc.rule_RL_do_free_write si3).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_free_write, si3, M_mkBluealloc.rule_RL_do_free_read,
                  si2, M_mkBluealloc.rule_RL_do_free_lookup, sif, M_mkBluealloc.meth_free,
                  M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB,
                  M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB,
                  M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readA,
                  M_mkSimpleBRAM2.meth_readB,
                  bool_and, (. == .),
                  h_dA, h_dB, h_iA, h_iB, h_rA, h_rB]
          exact Prod.ext hg rfl
        · -- alloc_prefetch fires from si4 (AL_PREFETCH, OP_IDLE after free_write, BFalse arm).
          show M_mkBluealloc.rule_RL_do_alloc_prefetch _ = (BTrue Unit_, _)
          have hg : (M_mkBluealloc.rule_RL_do_alloc_prefetch si4).1 = BTrue Unit_ := by
            simp only [M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                       si3, M_mkBluealloc.rule_RL_do_free_read, si2, M_mkBluealloc.rule_RL_do_free_lookup,
                       sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods, (. == .),
                       instBEqT_allocstate.beq, bool_and,
                       M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_putA, M_mkSimpleBRAM2.meth_readA,
                       M_mkSimpleBRAM2.meth_putB, M_mkSimpleBRAM2.meth_readB]
            split <;> (try split) <;> first | rfl | simp_all [h_dA, h_dB, h_iA, h_iB, h_rA, h_rB]
          exact Prod.ext hg rfl
        · -- alloc_wait fires from si5 (AL_WAIT, readResultB some).
          show M_mkBluealloc.rule_RL_do_alloc_wait _ = (BTrue Unit_, _)
          have h_al : si5.allocState = AL_WAIT Unit_ := by
            simp only [si5, M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                       si3, M_mkBluealloc.rule_RL_do_free_read, si2, M_mkBluealloc.rule_RL_do_free_lookup,
                       sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods]
            split
            · rename_i h_b
              exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b
              simp [bool_not] at h_b
            · rfl
          have h_revB_some : ∃ v, si5.bram_rever.readResultB = some v := by
            simp only [si5, M_mkBluealloc.rule_RL_do_alloc_prefetch, si4, M_mkBluealloc.rule_RL_do_free_write,
                       si3, M_mkBluealloc.rule_RL_do_free_read, si2, M_mkBluealloc.rule_RL_do_free_lookup,
                       sif, M_mkBluealloc.meth_free, bsv_rules, bsv_methods, M_mkSimpleBRAM2.meth_putB]
            split
            · rename_i h_b
              exfalso; rw [if_pos (show i.enqPtr - 1 < i.maxEver from h_enq_sub_lt_max_bv)] at h_b
              simp [bool_not] at h_b
            · exact ⟨_, rfl⟩
          obtain ⟨v, h_revB⟩ := h_revB_some
          have hg : (M_mkBluealloc.rule_RL_do_alloc_wait si5).1 = BTrue Unit_ := by
            simp [M_mkBluealloc.rule_RL_do_alloc_wait, h_al, h_revB, (. == .),
                  instBEqT_allocstate.beq, bool_and,
                  M_mkSimpleBRAM2.meth_RDY_readB]
          exact Prod.ext hg rfl
      · -- phi0 of si6 against s'.
        right
        refine ⟨h_vtrue, h_si6_allocState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- enqPtr.toNat = numAllocated - 1
          rw [h_si6_enqPtr, h_enq_sub_toNat, h_enq]
        · -- numAllocated - 1 ≤ maxEver
          rw [h_si6_maxEver]; show s.numAllocated - 1 ≤ i.maxEver.toNat; omega
        · -- op-disjunction: inl
          obtain ⟨h6_dA, h6_dB, h6_iA, h6_iB, h6_rA, h6_rB⟩ := h_si6_readResults
          left
          exact ⟨h_si6_opState, h_pend, h6_dA, h6_dB, h6_iA, h6_iB, h6_rA, h6_rB⟩
        · -- bij1: first three conjuncts of the combined invariant.
          intro t h_t
          rw [h_si6_maxEver] at h_t
          obtain ⟨h1, h2, h3, _⟩ := h_combined t h_t
          exact ⟨h1, h2, h3⟩
        · -- used↔live: spec removed free_f; impl index swapped (s_last↔free_f slots),
          -- enqPtr decremented to enqPtr-1.
          -- Injectivity of bram_index over [0,maxEver) via the bijection rever∘index = id.
          have h_inj : ∀ (a b : BitVec 16), a.toNat < i.maxEver.toNat → b.toNat < i.maxEver.toNat →
              (i.bram_index.memory.getD a.toNat default).toNat
                = (i.bram_index.memory.getD b.toNat default).toNat → a = b := by
            intro a b ha hb h_eq
            have ha3 := (h_bij1 a ha).2.2
            have hb3 := (h_bij1 b hb).2.2
            have h_eqb : i.bram_index.memory.getD a.toNat default
                = i.bram_index.memory.getD b.toNat default := BitVec.eq_of_toNat_eq h_eq
            rw [h_eqb] at ha3; rw [hb3] at ha3; exact ha3.symm
          -- s_last is live (index[s_last] = enqPtr-1 < enqPtr).
          have h_idx_slast_lt : (i.bram_index.memory.getD s_last.toNat default).toNat < i.enqPtr.toNat := by
            rw [h_idx_s_last, h_enq_sub_toNat]; omega
          intro t
          rw [h_si6_bramIndex_mem, h_si6_enqPtr, h_si6_maxEver, h_enq_sub_toNat]
          by_cases h_t_addr : t = free_f
          · -- t = free_f: not live; new_index[free_f] = enqPtr-1, not < enqPtr-1.
            subst h_t_addr
            simp only [beq_self_eq_true, if_true]
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
            rw [h_enq_sub_toNat]
            exact iff_of_false (by simp) (by intro ⟨_, h⟩; omega)
          · have h_tne : (t == free_f) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h_t_addr
            simp only [h_tne, Bool.false_eq_true, if_false]
            by_cases h_t_slast : t = s_last
            · -- t = s_last: new_index[s_last] = u_freed; live (s.used s_last = true), u_freed < enqPtr-1.
              rw [h_t_slast]
              have h_s_ne_addr : s_last.toNat ≠ free_f.toNat := by
                intro h; apply h_t_addr; rw [h_t_slast]; exact BitVec.eq_of_toNat_eq h
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              rw [setIB_same _ _ _ _ (by omega)]
              -- s.used s_last = true.
              have h_used_t : s.used s_last = true := (h_used s_last).2 ⟨h_s_last_lt_max, h_idx_slast_lt⟩
              -- u_freed ≠ enqPtr-1 (else free_f = s_last by injectivity).
              have h_uf_ne : u_freed.toNat ≠ (i.enqPtr - 1#16).toNat := by
                intro h_eq
                apply h_s_ne_addr
                have hfs : free_f = s_last := by
                  apply h_inj free_f s_last h_addr_max h_s_last_lt_max
                  rw [← hu_freed_def, h_eq, h_idx_s_last]
                exact (congrArg BitVec.toNat hfs).symm
              have h_uf_lt : u_freed.toNat < i.enqPtr.toNat - 1 := by
                rw [h_enq_sub_toNat] at h_uf_ne; omega
              exact iff_of_true h_used_t ⟨h_s_last_lt_max, h_uf_lt⟩
            · -- else: new_index[t] = index[t]; reduce to h_used with enqPtr ↔ enqPtr-1.
              have h_s_ne_addr : t.toNat ≠ free_f.toNat := fun h => h_t_addr (BitVec.eq_of_toNat_eq h)
              have h_s_ne_slast : t.toNat ≠ s_last.toNat := fun h => h_t_slast (BitVec.eq_of_toNat_eq h)
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_slast)]
              rw [h_used t]
              constructor
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                -- index[t] ≠ enqPtr-1 (else t = s_last by injectivity).
                have h_ne : (i.bram_index.memory.getD t.toNat default).toNat ≠ (i.enqPtr - 1#16).toNat := by
                  intro h_eq
                  apply h_t_slast
                  apply h_inj t s_last h1 h_s_last_lt_max
                  rw [h_eq, h_idx_s_last]
                rw [h_enq_sub_toNat] at h_ne; omega
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by omega⟩
        · -- data: fourth conjunct of the combined invariant.
          intro t h_t
          rw [h_si6_maxEver] at h_t
          exact (h_combined t h_t).2.2.2
        · rw [h_si6_bramIndex_mem, setIB_size, setIB_size]; exact h_isz
        · rw [h_si6_bramRever_mem, setIB_size, setIB_size]; exact h_rsz
        · rw [h_si6_bramData_mem, setIB_size, setIB_size]; exact h_dsz
        · -- idxlt: for t < maxEver, new bram_index[t] < maxEver.
          intro t h_t
          rw [h_si6_maxEver] at h_t
          rw [h_si6_maxEver, h_si6_bramIndex_mem]
          by_cases h_s_addr : t = free_f
          · subst h_s_addr
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
            rw [h_enq_sub_toNat]; omega
          · by_cases h_s_slast : t = s_last
            · rw [h_s_slast]
              have h_s_ne_addr : s_last.toNat ≠ free_f.toNat := by
                intro h; apply h_s_addr; rw [h_s_slast]; exact BitVec.eq_of_toNat_eq h
              have h_s_last_lt_idx_sz : s_last.toNat < i.bram_index.memory.size := by omega
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              rw [setIB_same _ _ _ _ h_s_last_lt_idx_sz]
              exact h_u_freed_lt_max
            · have h_s_ne_addr : t.toNat ≠ free_f.toNat := fun h => h_s_addr (BitVec.eq_of_toNat_eq h)
              have h_s_ne_slast : t.toNat ≠ s_last.toNat := fun h => h_s_slast (BitVec.eq_of_toNat_eq h)
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_slast)]
              exact h_idxlt t h_t
        · -- stdef: spec store unchanged, maxEver unchanged.
          intro t h_t
          rw [h_si6_maxEver] at h_t
          show s.store t = default
          exact h_stdef t h_t
        · -- datdef: for u ≥ maxEver, bram_data[u] unchanged.
          intro u h_u
          rw [h_si6_maxEver] at h_u
          rw [h_si6_bramData_mem]
          have h_u_ne_enqsub : u.toNat ≠ (i.enqPtr - 1#16).toNat := by omega
          have h_u_ne_ufreed : u.toNat ≠ u_freed.toNat := by omega
          rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_enqsub)]
          rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_ufreed)]
          exact h_datdef u h_u
        · -- bij2: for u < maxEver, bram_rever[u] stable < maxEver and bram_index[bram_rever[u]] = u.
          intro u h_u
          rw [h_si6_maxEver] at h_u
          rw [h_si6_maxEver, h_si6_bramRever_mem, h_si6_bramIndex_mem]
          by_cases h_u_enqsub : u = i.enqPtr - 1#16
          · subst h_u_enqsub
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
            refine ⟨h_addr_max, ?_⟩
            rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
          · by_cases h_u_ufreed : u = u_freed
            · subst h_u_ufreed
              have h_uf_ne_enqsub : u_freed.toNat ≠ (i.enqPtr - 1#16).toNat := by
                intro h_eq; apply h_u_enqsub; exact BitVec.eq_of_toNat_eq h_eq
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_uf_ne_enqsub)]
              rw [setIB_same _ _ _ _ h_u_freed_lt_rev_sz]
              refine ⟨h_s_last_lt_max, ?_⟩
              by_cases h_sl_addr : s_last.toNat = free_f.toNat
              · rw [h_sl_addr]
                rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
                have h_step : i.bram_index.memory.getD s_last.toNat default = u_freed := by rw [h_sl_addr]
                have h_step2 : i.bram_index.memory.getD s_last.toNat default = i.enqPtr - 1#16 := h_idx_s_last
                rw [h_step] at h_step2; exact h_step2.symm
              · rw [setIB_diff _ _ _ _ _ (Ne.symm h_sl_addr)]
                rw [setIB_same _ _ _ _ (by omega)]
            · have h_u_ne_enqsub : u.toNat ≠ (i.enqPtr - 1#16).toNat :=
                fun h => h_u_enqsub (BitVec.eq_of_toNat_eq h)
              have h_u_ne_ufreed : u.toNat ≠ u_freed.toNat :=
                fun h => h_u_ufreed (BitVec.eq_of_toNat_eq h)
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_enqsub)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_u_ne_ufreed)]
              obtain ⟨h_rev_lt, h_idx_eq⟩ := h_bij2 u h_u
              refine ⟨h_rev_lt, ?_⟩
              generalize hs_def : i.bram_rever.memory.getD u.toNat default = z at *
              have h_s_ne_slast : z ≠ s_last := by
                intro h_eq
                apply h_u_enqsub
                rw [h_eq] at h_idx_eq
                have hh : i.bram_index.memory.getD s_last.toNat default = i.enqPtr - 1#16 := h_idx_s_last
                rw [← h_idx_eq]; exact hh
              have h_s_ne_addr : z ≠ free_f := by
                intro h_eq
                apply h_u_ufreed
                rw [h_eq] at h_idx_eq
                rw [← h_idx_eq]
              have h_s_ne_slast_toNat : z.toNat ≠ s_last.toNat :=
                fun h => h_s_ne_slast (BitVec.eq_of_toNat_eq h)
              have h_s_ne_addr_toNat : z.toNat ≠ free_f.toNat :=
                fun h => h_s_ne_addr (BitVec.eq_of_toNat_eq h)
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_addr_toNat)]
              rw [setIB_diff _ _ _ _ _ (Ne.symm h_s_ne_slast_toNat)]
              exact h_idx_eq
        · -- frontier: enqPtr' = enqPtr-1 < maxEver, allocNextStable = free_f (the recycled handle).
          rw [h_si6_maxEver, h_si6_enqPtr, h_si6_bramIndex_mem, h_si6_allocNext]
          refine ⟨fun h => absurd h (by bv_omega), fun _ => ⟨h_addr_max, ?_⟩⟩
          rw [setIB_same _ _ _ _ (by rw [setIB_size]; omega)]
    · -- POISON handle: s' = {s with valid := false}; phi0 via Or.inl.
      rw [if_neg h_use] at hsmeth
      have hs' : s' = { s with valid := false } := (congrArg t_actionvalue_.avAction_ hsmeth).symm
      exact ⟨(M_mkBluealloc.meth_free i free_f).avAction_, Relation.ReflTransGen.refl,
        Or.inl (by rw [hs'])⟩

@[local grind →] theorem reach_phi0_again_write_req (i i' : ImplModule.State) (s s' : SpecModule.State) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ i' →
  SpecModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hp hm hsm
  -- Decompose impl method.
  dsimp [ImplModule, Module.getMethod, ofAVMethod2] at hm
  obtain ⟨a1, a2, vi, hmeth, hfp, hrdy⟩ := hm
  obtain ⟨ha1, ha2⟩ := Footprint.arg2_inj hfp.symm
  subst a1; subst a2
  have hi' : i' = (M_mkBluealloc.meth_write_req i write_req_addr write_req_data).avAction_ := by rw [hmeth]
  -- Decompose spec method.
  dsimp [SpecModule, Module.getMethod] at hsm
  obtain ⟨a1', a2', v'', hfp', hsbody⟩ := hsm
  obtain ⟨ha1', ha2'⟩ := Footprint.arg2_inj hfp'.symm
  subst a1'; subst a2'
  rcases hp with h_poison | h_valid
  · rw [if_neg (by simp [h_poison])] at hsbody
    exact ⟨i', Relation.ReflTransGen.refl, Or.inl hsbody⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    have h_op : i.opState = OP_IDLE Unit_ := by
      rcases h_op_cases with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exfalso
        simp [isReady, bsv_methods, M_mkBluealloc.meth_RDY_write_req, h, (. == .),
              bool_and] at hrdy
    obtain ⟨h_pend, h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩ : s.pendingRead = none ∧
        i.bram_data.readResultA = none ∧ i.bram_data.readResultB = none ∧
        i.bram_index.readResultA = none ∧ i.bram_index.readResultB = none ∧
        i.bram_rever.readResultA = none ∧ i.bram_rever.readResultB = none := by
      rcases h_op_cases with ⟨_, rest⟩ | ⟨h_op_rd, _⟩
      · exact rest
      · simp [h_op] at h_op_rd
    subst hi'
    refine ⟨(M_mkBluealloc.rule_RL_do_write_index
        (M_mkBluealloc.meth_write_req i write_req_addr write_req_data).avAction_).2,
      Relation.ReflTransGen.single ⟨.RL_do_write_index, ?_⟩, ?_⟩
    · simp [ImplModule, Module.getRule, ofRule, M_mkBluealloc.rule_RL_do_write_index,
        M_mkBluealloc.meth_write_req, isReady, (. == .), bool_and, bitvec_simp,
        M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_putA,
        h_dA, h_iA]
    · rw [if_pos h_vtrue] at hsbody
      simp only [M_mkBluealloc.Spec.meth_write_req] at hsbody
      obtain ⟨hsmeth, -⟩ := hsbody
      by_cases h_use : s.used write_req_addr
      · rw [if_pos h_use] at hsmeth
        have hs' : s' = { s with store := fun a => if a == write_req_addr then write_req_data else s.store a } :=
          (congrArg t_actionvalue_.avAction_ hsmeth).symm
        subst hs'
        -- u_addr := index[addr] is in-bounds (live handle).
        have h_addr_max : write_req_addr.toNat < i.maxEver.toNat := ((h_used write_req_addr).1 h_use).1
        have h_uaddr_bnd : (i.bram_index.memory.getD write_req_addr.toNat default).toNat
            < i.bram_data.memory.size := (h_bij1 write_req_addr h_addr_max).1
        right
        simp only [M_mkBluealloc.rule_RL_do_write_index, M_mkBluealloc.meth_write_req,
          M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_putA, ActionValue]
        refine ⟨h_vtrue, h_alloc, h_enq, h_le, ?_, ?_, h_used, ?_, h_isz, h_rsz,
          by rw [setIB_size]; exact h_dsz, h_idxlt, ?_, ?_, h_bij2, h_frontier⟩
        · -- op-disjunction: back to OP_IDLE.
          left
          refine ⟨trivial, h_pend, h_dA, h_dB, ?_, h_iB, h_rA, h_rB⟩
          simp
        · -- bij1: bram_index/bram_rever unchanged; bram_data.size unchanged.
          intro t h_t
          obtain ⟨hb1, hb2, hb3⟩ := h_bij1 t h_t
          exact ⟨by rw [setIB_size]; exact hb1, hb2, hb3⟩
        · -- data-on-used: the BRAM write at index[addr].
          intro t h_t_use
          have h_t_max : t.toNat < i.maxEver.toNat := h_t_use
          by_cases h_eq : t = write_req_addr
          · subst h_eq
            simp only [BEq.rfl, if_true, Option.getD_some]
            exact setIB_same _ _ _ _ h_uaddr_bnd
          · -- t ≠ addr ⇒ index[t] ≠ index[addr] (injectivity via bijection rever∘index = id).
            have h_idx_ne : (i.bram_index.memory.getD t.toNat default).toNat
                ≠ (i.bram_index.memory.getD write_req_addr.toNat default).toNat := by
              intro hh
              apply h_eq
              have ht := (h_bij1 t h_t_max).2.2
              have ha := (h_bij1 write_req_addr h_addr_max).2.2
              have : i.bram_rever.memory.getD (i.bram_index.memory.getD t.toNat default).toNat default
                   = i.bram_rever.memory.getD (i.bram_index.memory.getD write_req_addr.toNat default).toNat default := by
                rw [hh]
              rw [ht, ha] at this; exact this
            have h_tne : (t == write_req_addr) = false := by simp [h_eq]
            simp only [h_tne, if_false, Option.getD_some]
            rw [setIB_diff _ _ _ _ _ (Ne.symm h_idx_ne)]
            exact h_data t h_t_use
        · -- store pristine: store updated only at addr, which is < maxEver, so ≥ maxEver untouched.
          intro t h_t_ge
          have h_tne : (t == write_req_addr) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro hh; rw [hh] at h_t_ge; omega
          simp only [h_tne, if_false]; exact h_stdef t h_t_ge
        · -- data pristine: ≥ maxEver. index[addr] < maxEver, so the write doesn't touch ≥ maxEver.
          intro u h_u_ge
          have h_idx_lt : (i.bram_index.memory.getD write_req_addr.toNat default).toNat < i.maxEver.toNat :=
            h_idxlt write_req_addr h_addr_max
          simp only [Option.getD_some]
          rw [setIB_diff _ _ _ _ _ (by omega)]
          exact h_datdef u h_u_ge
      · rw [if_neg h_use] at hsmeth
        left
        have : s' = { s with valid := false } := (congrArg t_actionvalue_.avAction_ hsmeth).symm
        rw [this]

@[local grind →] theorem reach_phi0_again_read_req (i i' : ImplModule.State) (s s' : SpecModule.State) (read_req_addr : BitVec 16) (v : unit_) :
  phi0 i s →
  ImplModule.getMethod i ⟨.read_req, Footprint.arg1 read_req_addr v⟩ i' →
  SpecModule.getMethod s ⟨.read_req, Footprint.arg1 read_req_addr v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hp hm hsm
  -- Decompose impl method: i' = (meth_read_req i addr).avAction_, RDY holds.
  dsimp [ImplModule, Module.getMethod, ofAVMethod1] at hm
  obtain ⟨a1, vi, hmeth, hfp, hrdy⟩ := hm
  have ha1 : a1 = read_req_addr := Footprint.arg1_inj hfp.symm
  subst a1
  have hi' : i' = (M_mkBluealloc.meth_read_req i read_req_addr).avAction_ := by rw [hmeth]
  -- Decompose spec method.
  dsimp [SpecModule, Module.getMethod] at hsm
  obtain ⟨a1', v'', hfp', hsbody⟩ := hsm
  have ha1' : a1' = read_req_addr := Footprint.arg1_inj hfp'.symm
  subst a1'
  -- Extract phi0 facts.  read_req RDY forces opState = OP_IDLE.
  rcases hp with h_poison | h_valid
  · -- poisoned: s' poisoned ⇒ phi0 via Or.inl for ANY impl state (just stay put).
    rw [if_neg (by simp [h_poison])] at hsbody
    exact ⟨i', Relation.ReflTransGen.refl, Or.inl hsbody⟩
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    have h_op : i.opState = OP_IDLE Unit_ := by
      rcases h_op_cases with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exfalso
        simp [isReady, bsv_methods, M_mkBluealloc.meth_RDY_read_req, h, (. == .),
              bool_and] at hrdy
    obtain ⟨h_pend, h_dA, h_dB, h_iA, h_iB, h_rA, h_rB⟩ : s.pendingRead = none ∧
        i.bram_data.readResultA = none ∧ i.bram_data.readResultB = none ∧
        i.bram_index.readResultA = none ∧ i.bram_index.readResultB = none ∧
        i.bram_rever.readResultA = none ∧ i.bram_rever.readResultB = none := by
      rcases h_op_cases with ⟨_, rest⟩ | ⟨h_op_rd, _⟩
      · exact rest
      · simp [h_op] at h_op_rd
    subst hi'
    refine ⟨(M_mkBluealloc.rule_RL_do_read_index (M_mkBluealloc.meth_read_req i read_req_addr).avAction_).2,
      Relation.ReflTransGen.single ⟨.RL_do_read_index, ?_⟩, ?_⟩
    · -- the do_read_index rule fires from the post-read_req state
      simp [ImplModule, Module.getRule, ofRule, M_mkBluealloc.rule_RL_do_read_index,
        M_mkBluealloc.meth_read_req, isReady, (. == .), bool_and, bitvec_simp,
        M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_putA,
        h_dA, h_iA]
    · -- phi0 of the post-rule impl state against s'.
      -- Split on whether the spec handle was live.
      rw [if_pos h_vtrue] at hsbody
      simp only [M_mkBluealloc.Spec.meth_read_req] at hsbody
      obtain ⟨hsmeth, -⟩ := hsbody
      by_cases h_use : s.used read_req_addr
      · -- live handle: s'.pendingRead = some (s.store addr); impl latches the matching data.
        rw [if_pos h_use] at hsmeth
        have hs' : s' = { s with pendingRead := some (s.store read_req_addr) } :=
          (congrArg t_actionvalue_.avAction_ hsmeth).symm
        -- index[addr] is in live range, so data-on-used gives the latched value.
        have h_addr_live : s.used read_req_addr = true := h_use
        have h_data_addr := h_data read_req_addr ((h_used read_req_addr).1 h_use).1
        -- post-rule impl: opState=OP_READ_DATA, bram_data.readResultA = some(data[index[addr]]).
        right
        subst hs'
        simp only [M_mkBluealloc.rule_RL_do_read_index, M_mkBluealloc.meth_read_req,
          M_mkSimpleBRAM2.meth_readA, M_mkSimpleBRAM2.meth_putA, ActionValue]
        refine ⟨h_vtrue, h_alloc, h_enq, h_le, ?_, ?_, ?_, ?_, h_isz, h_rsz, h_dsz, h_idxlt,
          h_stdef, h_datdef, h_bij2, h_frontier⟩
        · -- op-disjunction: OP_READ_DATA with pendingRead = some, data latched.
          right
          refine ⟨trivial, ⟨s.store read_req_addr, rfl, ?_⟩, h_dB, ?_, h_iB, h_rA, h_rB⟩
          · -- the latched value equals s.store addr via data-on-used.
            simp only [Option.getD_some]
            exact congrArg some h_data_addr
          · simp
        · exact h_bij1
        · exact h_used
        · exact h_data
      · -- non-live handle: spec poisons.  phi0 via Or.inl.
        rw [if_neg h_use] at hsmeth
        left
        have : s' = { s with valid := false } := (congrArg t_actionvalue_.avAction_ hsmeth).symm
        rw [this]

@[local grind →] theorem reach_phi0_again_read_resp (i i' : ImplModule.State) (s s' : SpecModule.State) (v : BitVec 32) :
  phi0 i s →
  ImplModule.getMethod i ⟨.read_resp, Footprint.arg0 v⟩ i' →
  SpecModule.getMethod s ⟨.read_resp, Footprint.arg0 v⟩ s' →
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ phi0 i'' s' := by
  intro hp hm hsm
  -- Decompose the impl method: i' = (meth_read_resp i).avAction_, RDY holds.
  dsimp [ImplModule, Module.getMethod, ofAVMethod0] at hm
  obtain ⟨vi, hmeth, -, hrdy⟩ := hm
  have hi' : i' = (M_mkBluealloc.meth_read_resp i).avAction_ := by rw [hmeth]
  -- Decompose the spec method.
  dsimp [SpecModule, Module.getMethod] at hsm
  obtain ⟨v', -, hsbody⟩ := hsm
  refine ⟨i', Relation.ReflTransGen.refl, ?_⟩
  rcases hp with h_poison | h_valid
  · -- Spec was already poisoned ⇒ spec stays poisoned ⇒ phi0 via the left disjunct.
    rw [if_neg (by simp [h_poison])] at hsbody
    exact Or.inl hsbody
  · obtain ⟨h_vtrue, h_alloc, h_enq, h_le, h_op_cases, h_bij1, h_used, h_data,
      h_isz, h_rsz, h_dsz, h_idxlt, h_stdef, h_datdef, h_bij2, h_frontier⟩ := h_valid
    rw [if_pos h_vtrue] at hsbody
    obtain ⟨hsmeth, hsrdy⟩ := hsbody
    -- RDY of impl read_resp forces opState = OP_READ_DATA, so use the inr op-case.
    rcases h_op_cases with ⟨h_op, _⟩ | ⟨h_op, ⟨d, h_pend, h_resA⟩, h_dB, h_iA, h_iB, h_rA, h_rB⟩
    · exfalso
      simp [isReady, bsv_methods, M_mkBluealloc.meth_RDY_read_resp, h_op, (. == .),
            bool_and] at hrdy
    · -- s' is meth_read_resp s = consume pendingRead; impl i' sets opState := OP_IDLE,
      -- clears bram_data.readResultA; memory unchanged.
      have hs'_eq : s' = (M_mkBluealloc.Spec.meth_read_resp s).avAction_ := by
        rw [M_mkBluealloc.Spec.meth_read_resp, h_pend] at hsmeth ⊢; rw [hsmeth]
      have hs'_pend : s'.pendingRead = none := by
        rw [hs'_eq]; simp [M_mkBluealloc.Spec.meth_read_resp, h_pend]
      have hs'_store : s'.store = s.store := by
        rw [hs'_eq]; simp [M_mkBluealloc.Spec.meth_read_resp, h_pend]
      have hs'_used : s'.used = s.used := by
        rw [hs'_eq]; simp [M_mkBluealloc.Spec.meth_read_resp, h_pend]
      have hs'_valid : s'.valid = true := by
        rw [hs'_eq]; simp [M_mkBluealloc.Spec.meth_read_resp, h_pend, h_vtrue]
      have hs'_num : s'.numAllocated = s.numAllocated := by
        rw [hs'_eq]; simp [M_mkBluealloc.Spec.meth_read_resp, h_pend]
      -- impl post-state field facts
      subst hi'
      right
      rw [hs'_num]
      refine ⟨hs'_valid, h_alloc,
        by simpa [M_mkBluealloc.meth_read_resp] using h_enq,
        by simpa [M_mkBluealloc.meth_read_resp] using h_le, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- op-disjunction: now OP_IDLE, pendingRead consumed.
        left
        refine ⟨?_, hs'_pend, ?_, h_dB, h_iA, h_iB, h_rA, h_rB⟩
        · simp [M_mkBluealloc.meth_read_resp]
        · simp [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA]
      · -- bij1: bram_index/bram_data/bram_rever memory unchanged
        simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_bij1
      · -- used↔live: memory/enqPtr/maxEver unchanged
        rw [hs'_used]; simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_used
      · -- data agreement (memory + store unchanged by read_resp)
        rw [hs'_store]
        simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_data
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_isz
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_rsz
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_dsz
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_idxlt
      · -- store pristine
        rw [hs'_store]; simpa [M_mkBluealloc.meth_read_resp] using h_stdef
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_datdef
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_bij2
      · simpa [M_mkBluealloc.meth_read_resp, M_mkSimpleBRAM2.meth_readA] using h_frontier

@[local grind →] theorem phi0_reaches_phi0_RL_do_read_index (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_read_index i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_write_index (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_write_index i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_free_lookup (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_free_lookup i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_free_read (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_free_read i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_free_write (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_free_write i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_alloc_prefetch (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_alloc_prefetch i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

@[local grind →] theorem phi0_reaches_phi0_RL_do_alloc_wait (i i' : ImplModule.State) (s : SpecModule.State) :
  phi0 i s → ImplModule.getRule .RL_do_alloc_wait i i' → phi0 i' s := by
  intro hp hr
  rcases hp with h_poison | h_valid
  · exact Or.inl h_poison
  · exfalso
    obtain ⟨-, h_alloc, -, -, h_op_cases, -⟩ := h_valid
    simp only [ImplModule, Module.getRule, ofRule, bsv_rules, isReady, (.==.), instBEqT_allocstate.beq, bool_and, bitvec_simp, M_mkSimpleBRAM2.meth_RDY_putA, M_mkSimpleBRAM2.meth_RDY_putB, M_mkSimpleBRAM2.meth_RDY_readA, M_mkSimpleBRAM2.meth_RDY_readB] at hr
    rcases h_op_cases with ⟨h_op, -⟩ | ⟨h_op, -⟩ <;> simp_all [h_alloc, h_op]

-- Termination measure: op-FSM progress (×3) + alloc-FSM progress.
-- Each rule strictly decreases exactly one component and leaves the other fixed.
def opMeasure : t_opstate → Nat
  | OP_FREE_LOOKUP _ => 3
  | OP_FREE_READ _ => 2
  | OP_FREE_WRITE _ => 1
  | OP_WRITE_INDEX _ => 1
  | OP_READ_INDEX _ => 1
  | OP_IDLE _ => 0
  | OP_READ_DATA _ => 0

def allocMeasure : t_allocstate → Nat
  | AL_PREFETCH _ => 2
  | AL_WAIT _ => 1
  | AL_READY _ => 0

def blueMeasure (s : ImplModule.State) : Nat := opMeasure s.opState * 3 + allocMeasure s.allocState

theorem getARule_decreasing {a b : ImplModule.State} (h : ImplModule.getARule a b) :
    blueMeasure b < blueMeasure a := by
  obtain ⟨r, hr⟩ := h
  cases r <;>
    (simp only [ImplModule, Module.getRule, ofRule, bsv_rules, Prod.mk.injEq] at hr
     obtain ⟨hg, hb⟩ := hr
     subst hb
     cases hop : a.opState <;> cases hal : a.allocState <;>
       simp_all [blueMeasure, opMeasure, allocMeasure, hop, hal, (. == .),
                 instBEqT_allocstate.beq, bool_and, bool_not, bitvec_simp] <;>
       first
         | omega
         | (by_cases hc : a.enqPtr < a.maxEver <;>
             (try simp_all [opMeasure, allocMeasure, bitvec_simp]) <;> omega)
         | (-- RL_do_alloc_prefetch: result state has a match _ : discriminant containing
            -- (if a.enqPtr < a.maxEver then BTrue else BFalse).
            -- rw resolves the if inside the match _ : discriminant; simp then closes each branch.
            by_cases hlt : a.enqPtr < a.maxEver
            · rw [show (if a.enqPtr < a.maxEver then (BTrue Unit_ : t_bool) else BFalse Unit_) =
                    BTrue Unit_ from if_pos hlt]
              simp [opMeasure, allocMeasure, bool_not]
            · rw [show (if a.enqPtr < a.maxEver then (BTrue Unit_ : t_bool) else BFalse Unit_) =
                    BFalse Unit_ from if_neg hlt]
              simp [opMeasure, allocMeasure, bool_not]))

theorem rules_strongly_normalising : strongly_normalising ImplModule.getARule := by
  have key : ∀ n a, blueMeasure a = n → strongly_normalising' ImplModule.getARule a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      apply strongly_normalising'.step
      intro b hb
      exact ih (blueMeasure b) (ha ▸ getARule_decreasing hb) b rfl
  exact fun a => key (blueMeasure a) a rfl

-- ──────────────────────────────────────────────────────────────────────
-- Below: fixed generic boilerplate (closes `refines` via enough_star).
-- ──────────────────────────────────────────────────────────────────────

attribute [local grind →] commutes_weakly' Module.getARule relation_method relation_flush_method'
attribute [grind cases] Event

def mkBluealloc_refinement : StructuredRefinement where
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
        ∧ φ_ind phi0 ImplModule.getARule i' s' := enough_star mkBluealloc_refinement

#print axioms refines

end M_mkBluealloc.Refines
