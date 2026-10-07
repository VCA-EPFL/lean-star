import Star.Bluespec.Processor.mktop_pipelined_refines
open BluespecPrelude
open Params_types
open ReachingStar Bluespec

/-!
A direct forward simulation for `mktop_pipelined` against the ISA spec, without the flushing
framework (`StructuredRefinementUpto` / `enough_star_upto'`).

The relation `R i s` says: `i` is reachable, it drains by rules to a flushed state `f` matching
`s₀` (`phi0 f s₀`), and the spec state is `s₀` advanced by `k` ISA steps. The spec is allowed to
run ahead because every `doFetch` of the implementation is matched by a *real* spec `stepOne`:

* a right-path fetch: `f` becomes `doFetch_run`'s flushed state for `stepOne s₀`, `k` unchanged;
* a wrong-path fetch (absorbed by a redirect) or an implementation stutter: `f` is unchanged and
  `k` grows by one.

Commits only ever come from the drained prefix, so the spec's extra steps just append further
commit records behind the ones the implementation will produce.

The simulation therefore targets `SpecNS`, the spec *without* the `doFetch` stutter. It implies
trace inclusion for every combination of stuttering / non-stuttering implementation and spec.
-/

namespace M_mktop_pipelined.Refines.Direct

open M_mktop_pipelined.Spec (stepOne)

/-- The ISA spec without the `doFetch` stutter. -/
def SpecNS : Bluespec.Module Empty Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.Spec.meth_doFetch M_mktop_pipelined.Spec.meth_RDY_doFecth
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules := Empty.casesOn _

/-- The pipeline without the `doFetch` stutter. -/
def ImplNS : Bluespec.Module Rule Method where
  State := M_mktop_pipelined.state
  methods
    | .doFetch => ofAVMethod0 M_mktop_pipelined.meth_doFetch M_mktop_pipelined.meth_RDY_doFetch
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules := ImplModule.rules

local notation "RTG" => Relation.ReflTransGen ImplModule.getARule

-- ─── The ISA spec only appends to `output` ────────────────────────────

theorem stepOne_output (s : M_mktop_pipelined.Spec.State) :
    ∃ c, (stepOne s).output = s.output ++ [c] ∧
      ∀ o, stepOne { s with output := o } = { stepOne s with output := o ++ [c] } :=
  ⟨_, rfl, fun _ => rfl⟩

theorem iterate_output (k : Nat) (s : M_mktop_pipelined.Spec.State) :
    ∃ ex, (stepOne^[k] s).output = s.output ++ ex ∧
      ∀ o, stepOne^[k] { s with output := o } = { stepOne^[k] s with output := o ++ ex } := by
  induction k with
  | zero => exact ⟨[], by simp, fun o => by simp⟩
  | succ k ih =>
    obtain ⟨ex, h1, h2⟩ := ih
    obtain ⟨c, h3, h4⟩ := stepOne_output (stepOne^[k] s)
    refine ⟨ex ++ [c], ?_, fun o => ?_⟩
    · rw [Function.iterate_succ_apply', h3, h1, List.append_assoc]
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h2, h4, List.append_assoc]

/-- A commit read from `s₀` is still at the head after any number of further ISA steps. -/
theorem spec_getCommitInst_iterate {s₀ s₀' : M_mktop_pipelined.Spec.State} {fp : Footprint} (k : Nat)
    (h : SpecModule.getMethod s₀ ⟨.getCommitInst, fp⟩ s₀') :
    SpecNS.getMethod (stepOne^[k] s₀) ⟨.getCommitInst, fp⟩ (stepOne^[k] s₀') := by
  obtain ⟨w, hw, hfp, hrdy⟩ := h
  obtain ⟨ex, h1, h2⟩ := iterate_output k s₀
  rcases hq : s₀.output with _ | ⟨x, xs⟩
  · simp [M_mktop_pipelined.Spec.meth_RDY_getCommitInst, hq] at hrdy
  have hs : s₀' = { s₀ with output := xs } := by
    have := congrArg (·.avAction_) hw
    simp only [M_mktop_pipelined.Spec.meth_getCommitInst, hq, List.tail!] at this
    exact this.symm
  have hw' : w = x := by
    have := congrArg (·.avValue_) hw
    simp only [M_mktop_pipelined.Spec.meth_getCommitInst, hq, List.head!] at this
    exact this.symm
  subst hs hw'
  refine ⟨w, ?_, hfp, ?_⟩
  · simp only [M_mktop_pipelined.Spec.meth_getCommitInst, h1, hq, List.cons_append, List.head!, List.tail!]
    rw [h2 xs]
  · simp [M_mktop_pipelined.Spec.meth_RDY_getCommitInst, h1, hq]

-- ─── Draining ──────────────────────────────────────────────────────────

theorem reachable_rtg {a b : ImplModule.State} (hR : ImplModule.reachable a) (h : RTG a b) :
    ImplModule.reachable b := by
  induction h with
  | refl => exact hR
  | tail _ hbc ih => exact ImplModule.reachable_rule ih hbc

/-- Flushed states are the unique normal form: any rule path from a reachable state can still be
continued to the flushed state that state drains to. -/
theorem to_flush {a b f : ImplModule.State} {s₀ : SpecModule.State} (hR : ImplModule.reachable a)
    (hab : RTG a b) (haf : RTG a f) (hf : phi0 f s₀) : RTG b f := by
  obtain ⟨d, hbd, hfd⟩ := StructuredRefinementUpto.rules_confluent mktop_pipelined_refinement hR
    (trans_refl_equiv.mpr hab) (trans_refl_equiv.mpr haf)
  rw [trans_refl_equiv] at hbd hfd
  rwa [phi0_rtg hf hfd] at hbd

-- ─── Pushing methods along rule paths ──────────────────────────────────

theorem getCommitInst_step {a b c : ImplModule.State} {v : t_commitinst} (hab : ImplModule.getARule a b)
    (hm : ImplModule.getMethod a ⟨.getCommitInst, Footprint.arg0 v⟩ c) :
    ∃ d, ImplModule.getMethod b ⟨.getCommitInst, Footprint.arg0 v⟩ d ∧ ImplModule.getARule c d := by
  obtain ⟨r, hr⟩ := hab
  have lift : ∀ {r'}, (∃ d, ImplModule.getMethod b ⟨.getCommitInst, Footprint.arg0 v⟩ d ∧ ImplModule.getRule r' c d) →
      ∃ d, ImplModule.getMethod b ⟨.getCommitInst, Footprint.arg0 v⟩ d ∧ ImplModule.getARule c d :=
    fun ⟨d, hd, hcd⟩ => ⟨d, hd, ⟨_, hcd⟩⟩
  cases r
  · exact lift (reconverge_RL_requestI_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_responseI_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_requestD_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_responseD_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_decode_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_execute_getCommitInst _ _ _ v hr hm)
  · exact lift (reconverge_RL_writeback_getCommitInst _ _ _ v hr hm)

theorem push_getCommitInst {a b c : ImplModule.State} {v : t_commitinst} (hab : RTG a b)
    (hm : ImplModule.getMethod a ⟨.getCommitInst, Footprint.arg0 v⟩ c) :
    ∃ d, ImplModule.getMethod b ⟨.getCommitInst, Footprint.arg0 v⟩ d ∧ RTG c d := by
  induction hab with
  | refl => exact ⟨c, hm, .refl⟩
  | tail _ hbb' ih =>
    obtain ⟨d, hd, hcd⟩ := ih
    obtain ⟨d', hd', hdd'⟩ := getCommitInst_step hbb' hd
    exact ⟨d', hd', hcd.tail hdd'⟩

/-- A fetch commutes with a rule, except against a redirecting `RL_execute`, where the fetch is on the
wrong path and is absorbed: both sides meet again by rules alone. -/
theorem doFetch_step {a b c : ImplModule.State} {v : unit_} (hR : ImplModule.reachable a)
    (hab : ImplModule.getARule a b) (hm : ImplModule.getMethod a ⟨.doFetch, Footprint.arg0 v⟩ c) :
    (∃ d, ImplModule.getMethod b ⟨.doFetch, Footprint.arg0 v⟩ d ∧ ImplModule.getARule c d) ∨
      (∃ j, RTG b j ∧ RTG c j) := by
  obtain ⟨r, hr⟩ := hab
  have lift : ∀ {r'}, (∃ d, ImplModule.getMethod b ⟨.doFetch, Footprint.arg0 v⟩ d ∧ ImplModule.getRule r' c d) →
      (∃ d, ImplModule.getMethod b ⟨.doFetch, Footprint.arg0 v⟩ d ∧ ImplModule.getARule c d) ∨
        (∃ j, RTG b j ∧ RTG c j) :=
    fun ⟨d, hd, hcd⟩ => .inl ⟨d, hd, ⟨_, hcd⟩⟩
  cases r
  · exact lift (reconverge_RL_requestI_doFetch _ _ _ v hr hm)
  · exact lift (reconverge_RL_responseI_doFetch _ _ _ v hr hm)
  · exact lift (reconverge_RL_requestD_doFetch _ _ _ v hr hm)
  · exact lift (reconverge_RL_responseD_doFetch _ _ _ v hr hm)
  · exact lift (reconverge_RL_decode_doFetch _ _ _ v hr hm)
  · rcases reconverge_RL_execute_doFetch _ _ _ v hr hm with h | h | h
    · exact lift h
    · exact .inr h
    · exact absurd hR h
  · exact lift (reconverge_RL_writeback_doFetch _ _ _ v hr hm)

/-- Push a fetch from `a` to the flushed state `f` that `a` drains to: either the fetch can still be
taken at `f` (right path), or it is absorbed and the post-fetch state drains to `f` itself. -/
theorem push_doFetch {a b f c : ImplModule.State} {s₀ : SpecModule.State} {v : unit_}
    (hR : ImplModule.reachable a) (hab : RTG a b) (hbf : RTG b f) (hf : phi0 f s₀)
    (hm : ImplModule.getMethod a ⟨.doFetch, Footprint.arg0 v⟩ c) :
    (∃ d, ImplModule.getMethod b ⟨.doFetch, Footprint.arg0 v⟩ d ∧ RTG c d) ∨ RTG c f := by
  induction hab with
  | refl => exact .inl ⟨c, hm, .refl⟩
  | @tail b' b hab' hb'b ih =>
    rcases ih (.head hb'b hbf) with ⟨d, hd, hcd⟩ | h
    · rcases doFetch_step (reachable_rtg hR hab') hb'b hd with ⟨d', hd', hdd'⟩ | ⟨j, hbj, hdj⟩
      · exact .inl ⟨d', hd', hcd.tail hdd'⟩
      · exact .inr (hcd.trans (hdj.trans (to_flush (reachable_rtg hR (hab'.tail hb'b)) hbj hbf hf)))
    · exact .inr h

-- ─── The relation and its preservation ─────────────────────────────────

def R (i : ImplModule.State) (s : M_mktop_pipelined.Spec.State) : Prop :=
  ImplModule.reachable i ∧ ∃ f s₀ k, RTG i f ∧ phi0 f s₀ ∧ s = stepOne^[k] s₀

theorem R_rule {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} (h : R i s)
    (hr : ImplModule.getARule i i') : R i' s := by
  obtain ⟨hR, f, s₀, k, hif, hf, rfl⟩ := h
  exact ⟨ImplModule.reachable_rule hR hr, f, s₀, k, to_flush hR (.single hr) hif hf, hf, rfl⟩

theorem R_rules {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} (h : R i s)
    (hr : trans_refl ImplModule.getARule i i') : R i' s := by
  induction hr with
  | refl => exact h
  | step hab _ ih => exact ih (R_rule h hab)

theorem R_doFetch {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} {v : unit_} (h : R i s)
    (hm : ImplModule.getMethod i ⟨.doFetch, Footprint.arg0 v⟩ i') :
    ∃ s', SpecNS.getMethod s ⟨.doFetch, Footprint.arg0 v⟩ s' ∧ R i' s' := by
  obtain ⟨hR, f, s₀, k, hif, hf, rfl⟩ := h
  refine ⟨stepOne (stepOne^[k] s₀), ⟨Unit_, rfl, by cases v; rfl, rfl⟩,
    ImplModule.reachable_method hR hm, ?_⟩
  -- the spec is one step further ahead of an unchanged flush point
  have ahead : RTG i' f → ∃ f' s₀' k', RTG i' f' ∧ phi0 f' s₀' ∧ stepOne (stepOne^[k] s₀) = stepOne^[k'] s₀' :=
    fun h => ⟨f, s₀, k + 1, h, hf, (Function.iterate_succ_apply' _ _ _).symm⟩
  rcases push_doFetch hR hif .refl hf hm with ⟨d, hd, hid⟩ | h
  · dsimp only [ImplModule, Module.getMethod, orStutter0, ofAVMethod0] at hd
    rcases hd with ⟨w, hw, -, -⟩ | ⟨-, rfl⟩
    · -- right path: the flush point advances by one ISA step
      obtain rfl : d = (M_mktop_pipelined.meth_doFetch f).avAction_ := (congrArg (·.avAction_) hw).symm
      obtain ⟨f', hdf', hf'⟩ := doFetch_run f s₀ hf
      exact ⟨f', stepOne s₀, k, hid.trans hdf', hf',
        (Function.iterate_succ_apply' _ _ _).symm.trans (Function.iterate_succ_apply _ _ _)⟩
    · exact ahead hid
  · exact ahead h

theorem R_getCommitInst {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} {v : t_commitinst}
    (h : R i s) (hm : ImplModule.getMethod i ⟨.getCommitInst, Footprint.arg0 v⟩ i') :
    ∃ s', SpecNS.getMethod s ⟨.getCommitInst, Footprint.arg0 v⟩ s' ∧ R i' s' := by
  obtain ⟨hR, f, s₀, k, hif, hf, rfl⟩ := h
  obtain ⟨d, hfd, hid⟩ := push_getCommitInst hif hm
  obtain ⟨s₀', hs₀, f', hdf', hf'⟩ := phi0_simulates_getCommitInst f f d s₀ v hf .refl hfd
  exact ⟨stepOne^[k] s₀', spec_getCommitInst_iterate k hs₀,
    ImplModule.reachable_method hR hm, f', s₀', k, hid.trans hdf', hf', rfl⟩

theorem R_method {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} {e : Event Method}
    (h : R i s) (hm : ImplModule.getMethod i e i') : ∃ s', SpecNS.getMethod s e s' ∧ R i' s' := by
  obtain ⟨name, fp⟩ := e
  rcases ImplModule.get_method_cases hm with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ <;>
    dsimp only at h1 h2 <;> subst h1 h2
  · exact R_doFetch h hm
  · exact R_getCommitInst h hm

/-- `R` is a forward simulation: every implementation run (rules and methods) is matched by a
method-only run of the stutter-free spec over the same trace. -/
theorem simulation {i i' : ImplModule.State} {s : M_mktop_pipelined.Spec.State} {l : List (Event Method)} :
    R i s → star_extend ImplModule.getARule ImplModule.getMethod i l i' →
    ∃ s', star SpecNS.getMethod s l s' ∧ R i' s' := by
  intro h hi
  induction hi with
  | refl => exact ⟨s, .refl _, h⟩
  | step_int _ _ _ _ htr ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih
    exact ⟨s₁, hs₁, R_rules h₁ htr⟩
  | step_ext _ _ _ _ _ hm ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih
    obtain ⟨s₂, hs₂, h₂⟩ := R_method h₁ hm
    exact ⟨s₂, .step _ _ _ _ _ hs₁ hs₂, h₂⟩

theorem R_init (i : ImplModule.State) (h : ImplModule.init i) (halted : BitVec 1) :
    R i ⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ :=
  ⟨⟨i, h, .refl⟩, i, _, 0, .refl, phi0_init i h halted, rfl⟩

-- ─── Trace inclusion ───────────────────────────────────────────────────

/-- The (stuttering) pipeline refines the stutter-free spec. -/
theorem trace_inclusion (l : List (Event Method)) (i : ImplModule.State) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    spec_behaviour SpecNS.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : M_mktop_pipelined.Spec.State) := by
  rintro ⟨i', hi⟩
  obtain ⟨s', hs', -⟩ := simulation (R_init i h halted) hi
  exact ⟨s', hs'⟩

-- ─── Corollaries: dropping the stutter on either side ─────────────────

theorem star_SpecNS {s s' : M_mktop_pipelined.Spec.State} {l : List (Event Method)} :
    star SpecNS.getMethod s l s' → star SpecModule.getMethod s l s' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step _ _ _ e _ hm ih =>
    refine .step _ _ _ _ _ ih ?_
    obtain ⟨_ | _, fp⟩ := e
    · exact Or.inl hm
    · exact hm

theorem star_extend_ImplNS {i i' : M_mktop_pipelined.state} {l : List (Event Method)} :
    star_extend ImplNS.getARule ImplNS.getMethod i l i' →
    star_extend ImplModule.getARule ImplModule.getMethod i l i' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step_int _ _ _ _ htr ih => exact .step_int _ _ _ _ ih htr
  | step_ext _ _ _ e _ hm ih =>
    refine .step_ext _ _ _ _ _ ih ?_
    obtain ⟨_ | _, fp⟩ := e
    · exact Or.inl hm
    · exact hm

/-- Neither side stutters. -/
theorem trace_inclusion_ns (l : List (Event Method)) (i : M_mktop_pipelined.state) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplNS.getARule ImplNS.getMethod l i →
    spec_behaviour SpecNS.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : M_mktop_pipelined.Spec.State) :=
  fun ⟨i', hi⟩ => trace_inclusion l i h halted ⟨i', star_extend_ImplNS hi⟩

/-- The original statement (`Refines.trace_inclusion`), re-derived without the flushing framework. -/
theorem trace_inclusion_orig (l : List (Event Method)) (i : ImplModule.State) (h : ImplModule.init i)
    (halted : BitVec 1) :
    imp_behaviour ImplModule.getARule ImplModule.getMethod l i →
    spec_behaviour SpecModule.getMethod l
      (⟨i.pc, halted, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SpecModule.State) := by
  intro hi
  obtain ⟨s', hs'⟩ := trace_inclusion l i h halted hi
  exact ⟨s', star_SpecNS hs'⟩

#print axioms simulation
#print axioms trace_inclusion
#print axioms trace_inclusion_ns
#print axioms trace_inclusion_orig

end M_mktop_pipelined.Refines.Direct
