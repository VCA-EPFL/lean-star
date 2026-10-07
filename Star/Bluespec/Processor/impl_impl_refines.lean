import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Processor.Params_types
import Star.Bluespec.Processor.RVUtil
import Star.Bluespec.Lib.mkSimpleBRAM
import Star.Bluespec.Lib.mkFIFO
import Star.Bluespec.Processor.mktop_pipelined
import Star.Bluespec.Processor.mktop_pipelined_free
import Star.Bluespec.Processor.isa_hide_fetch
import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecVerification
open BluespecPrelude
open Params_types
open BluespecVerification
open ReachingStar Bluespec

set_option maxHeartbeats 1000000

/-!
`mktop_pipelined_free` (fetch as a free-running rule) refines `HideFetch.WrappedModule`
(`mktop_pipelined` with `doFetch` wrapped as an internal rule), in lockstep: apart from fetch the
two modules are textually identical. Composed with `HideFetch.trace_inclusion`, this gives trace
inclusion of `mktop_pipelined_free` in the ISA spec with fetch hidden.
-/

namespace M_mktop_pipelined_free.Impl

structure State where
  m : M_mktop_pipelined_free.state
deriving Inhabited

def liftState : M_mktop_pipelined_free.state → State :=
  fun s => { m := s }

def accState : State → M_mktop_pipelined_free.state :=
  fun s => s.m

def liftRule : (M_mktop_pipelined_free.state → t_bool × M_mktop_pipelined_free.state) → (State → t_bool × State) := Bluespec.liftRule liftState accState

def meth_getCommitInst (s : State) : t_actionvalue_ t_commitinst State :=
  let a := M_mktop_pipelined_free.meth_getCommitInst s.m
  { a with avAction_ := liftState a.avAction_ }
def meth_RDY_getCommitInst (s : State) : t_bool := M_mktop_pipelined_free.meth_RDY_getCommitInst s.m

end M_mktop_pipelined_free.Impl

namespace M_mktop_pipelined_free.Refines

abbrev Method := M_mktop_pipelined.HideFetch.Method

@[grind cases]
inductive RuleImpl : Type where
| RL_requestI
| RL_responseI
| RL_requestD
| RL_responseD
| RL_fetch
| RL_decode
| RL_execute
| RL_writeback

abbrev SpecModule := M_mktop_pipelined.HideFetch.WrappedModule

def ImplModule : Bluespec.Module RuleImpl Method where
  State := M_mktop_pipelined_free.Impl.State
  methods
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined_free.Impl.meth_getCommitInst M_mktop_pipelined_free.Impl.meth_RDY_getCommitInst
  rules
    | .RL_requestI => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_requestI
    | .RL_responseI => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_responseI
    | .RL_requestD => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_requestD
    | .RL_responseD => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_responseD
    | .RL_fetch => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_fetch
    | .RL_decode => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_decode
    | .RL_execute => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_execute
    | .RL_writeback => ofRule <| M_mktop_pipelined_free.Impl.liftRule M_mktop_pipelined_free.rule_RL_writeback

def phi (si : ImplModule.State) (ss : SpecModule.State) : Prop :=
  si.m.iMem = ss.iMem ∧ si.m.dMem = ss.dMem ∧ si.m.ireq = ss.ireq ∧
  si.m.dreq = ss.dreq ∧ si.m.toImem = ss.toImem ∧ si.m.fromImem = ss.fromImem ∧ si.m.toDmem = ss.toDmem ∧ si.m.fromDmem = ss.fromDmem ∧ si.m.f2d = ss.f2d ∧ si.m.d2e = ss.d2e ∧ si.m.e2w = ss.e2w ∧ si.m.retiredInst = ss.retiredInst ∧ si.m.pc = ss.pc ∧ si.m.ep = ss.ep ∧ si.m.hcf = ss.hcf ∧ si.m.rf = ss.rf ∧ si.m.sb = ss.sb

/-- Field-wise conversion between the two (identical) state layouts. -/
def conv (s : M_mktop_pipelined_free.state) : M_mktop_pipelined.state :=
  { iMem := s.iMem, dMem := s.dMem, ireq := s.ireq, dreq := s.dreq, toImem := s.toImem,
    fromImem := s.fromImem, toDmem := s.toDmem, fromDmem := s.fromDmem, f2d := s.f2d, d2e := s.d2e,
    e2w := s.e2w, retiredInst := s.retiredInst, pc := s.pc, ep := s.ep, hcf := s.hcf, rf := s.rf, sb := s.sb }

theorem phi_iff {i : ImplModule.State} {s : SpecModule.State} : phi i s ↔ s = conv i.m := by
  rcases i with ⟨⟨⟩⟩; rcases s with ⟨⟩
  simp only [phi, conv]
  grind

theorem lift_sim {rs : M_mktop_pipelined.state → t_bool × M_mktop_pipelined.state}
    {ri : M_mktop_pipelined_free.state → t_bool × M_mktop_pipelined_free.state}
    (hcomm : ∀ x, rs (conv x) = ((ri x).1, conv (ri x).2))
    {i i' : ImplModule.State} {s : SpecModule.State} (hphi : s = conv i.m)
    (h : ofRule (M_mktop_pipelined_free.Impl.liftRule ri) i i') :
    ofRule rs s (conv i'.m) := by
  simp only [ofRule, M_mktop_pipelined_free.Impl.liftRule, Bluespec.liftRule,
    M_mktop_pipelined_free.Impl.accState] at *
  rw [hphi, hcomm]
  rcases hri : ri i.m with ⟨f, x⟩
  rw [hri] at h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem requestI_comm (x) : M_mktop_pipelined.rule_RL_requestI (conv x) =
    ((M_mktop_pipelined_free.rule_RL_requestI x).1, conv (M_mktop_pipelined_free.rule_RL_requestI x).2) := rfl
theorem responseI_comm (x) : M_mktop_pipelined.rule_RL_responseI (conv x) =
    ((M_mktop_pipelined_free.rule_RL_responseI x).1, conv (M_mktop_pipelined_free.rule_RL_responseI x).2) := rfl
theorem requestD_comm (x) : M_mktop_pipelined.rule_RL_requestD (conv x) =
    ((M_mktop_pipelined_free.rule_RL_requestD x).1, conv (M_mktop_pipelined_free.rule_RL_requestD x).2) := rfl
theorem responseD_comm (x) : M_mktop_pipelined.rule_RL_responseD (conv x) =
    ((M_mktop_pipelined_free.rule_RL_responseD x).1, conv (M_mktop_pipelined_free.rule_RL_responseD x).2) := rfl
theorem decode_comm (x) : M_mktop_pipelined.rule_RL_decode (conv x) =
    ((M_mktop_pipelined_free.rule_RL_decode x).1, conv (M_mktop_pipelined_free.rule_RL_decode x).2) := rfl
theorem execute_comm (x) : M_mktop_pipelined.rule_RL_execute (conv x) =
    ((M_mktop_pipelined_free.rule_RL_execute x).1, conv (M_mktop_pipelined_free.rule_RL_execute x).2) := rfl
theorem writeback_comm (x) : M_mktop_pipelined.rule_RL_writeback (conv x) =
    ((M_mktop_pipelined_free.rule_RL_writeback x).1, conv (M_mktop_pipelined_free.rule_RL_writeback x).2) := rfl

theorem step_sim {i i' : ImplModule.State} {s : SpecModule.State} (hphi : phi i s)
    (h : ImplModule.getARule i i') : ∃ s', SpecModule.getARule s s' ∧ phi i' s' := by
  rw [phi_iff] at hphi
  obtain ⟨r, hr⟩ := h
  refine ⟨conv i'.m, ?_, phi_iff.mpr rfl⟩
  cases r
  · exact ⟨.RL_requestI, lift_sim requestI_comm hphi hr⟩
  · exact ⟨.RL_responseI, lift_sim responseI_comm hphi hr⟩
  · exact ⟨.RL_requestD, lift_sim requestD_comm hphi hr⟩
  · exact ⟨.RL_responseD, lift_sim responseD_comm hphi hr⟩
  · refine ⟨.RL_callFetch, Or.inl ?_⟩
    simp only [Module.getRule, ImplModule, ofRule, M_mktop_pipelined_free.Impl.liftRule, Bluespec.liftRule,
      M_mktop_pipelined_free.Impl.accState] at hr
    rcases hri : M_mktop_pipelined_free.rule_RL_fetch i.m with ⟨f, x⟩
    rw [hri] at hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp only [ofRule, M_mktop_pipelined.HideFetch.rule_RL_callFetch, hphi, Prod.mk.injEq]
    simp only [M_mktop_pipelined_free.rule_RL_fetch, Prod.mk.injEq] at hri
    obtain ⟨hg, rfl⟩ := hri
    refine ⟨?_, rfl⟩
    simp only [M_mktop_pipelined.meth_RDY_doFetch, conv]
    revert hg
    generalize bitvec1_to_bool (bit_not (bool_to_bitvec1 i.m.hcf)) = c
    generalize M_mkFIFO.meth_RDY_enq i.m.f2d = a
    generalize M_mkFIFO.meth_RDY_enq i.m.toImem = b
    cases c <;> cases a <;> cases b <;> simp [bool_and]
  · exact ⟨.RL_decode, lift_sim decode_comm hphi hr⟩
  · exact ⟨.RL_execute, lift_sim execute_comm hphi hr⟩
  · exact ⟨.RL_writeback, lift_sim writeback_comm hphi hr⟩

theorem steps_sim {i i' : ImplModule.State} {s : SpecModule.State} (hphi : phi i s)
    (h : trans_refl ImplModule.getARule i i') :
    ∃ s', trans_refl SpecModule.getARule s s' ∧ phi i' s' := by
  induction h generalizing s with
  | refl => exact ⟨s, .refl, hphi⟩
  | step hab _ ih =>
    obtain ⟨s₁, hs₁, hphi₁⟩ := step_sim hphi hab
    obtain ⟨s₂, hs₂, hphi₂⟩ := ih hphi₁
    exact ⟨s₂, .step hs₁ hs₂, hphi₂⟩

theorem method_sim {i i' : ImplModule.State} {s : SpecModule.State} {e : Event Method} (hphi : phi i s)
    (h : ImplModule.getMethod i e i') : ∃ s', SpecModule.getMethod s e s' ∧ phi i' s' := by
  rw [phi_iff] at hphi
  rcases e with ⟨⟨⟩, fp⟩
  obtain ⟨v, hv, rfl, hrdy⟩ := h
  refine ⟨conv i'.m, ⟨v, ?_, rfl, ?_⟩, phi_iff.mpr rfl⟩
  · simp only [M_mktop_pipelined_free.Impl.meth_getCommitInst] at hv
    subst hphi
    cases hv
    rfl
  · rw [← hrdy, hphi]
    rfl

/-- Lockstep simulation. The spec side needs `star_extend` (not `star`): the spec must take its own
internal rules (e.g. `RL_callFetch` for an impl `RL_fetch`) to keep up with the impl. -/
theorem refines {i i' : ImplModule.State} {s : SpecModule.State} {l : List (Event Method)} :
  phi i s →
  star_extend ImplModule.getARule ImplModule.getMethod i l i' →
  ∃ s', star_extend SpecModule.getARule SpecModule.getMethod s l s'
        ∧ phi i' s' := by
  intro hphi h
  induction h with
  | refl => exact ⟨s, .refl _, hphi⟩
  | step_int _ _ _ _ htr ih =>
    obtain ⟨s₁, hs₁, hphi₁⟩ := ih
    obtain ⟨s₂, hs₂, hphi₂⟩ := steps_sim hphi₁ htr
    exact ⟨s₂, .step_int _ _ _ _ hs₁ hs₂, hphi₂⟩
  | step_ext _ _ _ _ _ hm ih =>
    obtain ⟨s₁, hs₁, hphi₁⟩ := ih
    obtain ⟨s₂, hs₂, hphi₂⟩ := method_sim hphi₁ hm
    exact ⟨s₂, .step_ext _ _ _ _ _ hs₁ hs₂, hphi₂⟩

/-- Reset states of the free pipeline: those whose image under `conv` is a reset state of
`mktop_pipelined`. -/
def init (i : ImplModule.State) : Prop := M_mktop_pipelined.Refines.ImplModule.init (conv i.m)

/-- Trace inclusion from reset: every trace of `mktop_pipelined_free` is a trace of the ISA spec with
fetch as a plain internal rule (`FetchSpecModule`), started with the same `pc`, registers and memories, no pending commit
records, and halted iff the pipeline is. -/
theorem trace_inclusion (l : List (Event Method)) (i : ImplModule.State) (h : init i) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    ∃ s', star_extend M_mktop_pipelined.HideFetch.FetchSpecModule.getARule
      M_mktop_pipelined.HideFetch.FetchSpecModule.getMethod
      (⟨i.m.pc, bool_to_bitvec1 i.m.hcf, i.m.rf, i.m.iMem.memory, i.m.dMem.memory, []⟩ :
        M_mktop_pipelined.Spec.State) l s' := by
  rintro ⟨i', hi⟩
  obtain ⟨s', hs', -⟩ := refines (phi_iff.mpr rfl) hi
  obtain ⟨t, ht⟩ := M_mktop_pipelined.HideFetch.trace_inclusion l (conv i.m) h ⟨s', hs'⟩
  exact ⟨t, M_mktop_pipelined.HideFetch.hidden_refines_fetch ht⟩

#print axioms refines
#print axioms trace_inclusion

end M_mktop_pipelined_free.Refines
