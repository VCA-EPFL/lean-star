import Star.Bluespec.Processor.mktop_pipelined_refines
open BluespecPrelude
open ReachingStar Bluespec

/-!
Hiding `doFetch`.

`M_mktop_pipelined.Refines` proves the pipeline refines the ISA spec with `doFetch` as an external
(stuttering) method on both sides. Here `doFetch` becomes an internal rule `RL_callFetch` on both
sides, leaving `getCommitInst` as the only observable method:

* `WrappedModule`: the pipeline with fetch as a rule;
* `HiddenSpecModule`: the ISA spec with fetch as a rule.

`WrappedModule` cannot be verified directly with `StructuredRefinementUpto`: `RL_callFetch` is always
enabled, so its rules are not strongly normalising. Instead, a run of `WrappedModule` is turned back
into a run of the method-based pipeline (`unhide`), `Refines.trace_inclusion` is applied, and the
resulting ISA run is hidden again (`hide_fetch`).
-/

namespace M_mktop_pipelined.HideFetch

open M_mktop_pipelined.Refines (SpecModule ImplModule)

@[grind cases]
inductive Method : Type where
| getCommitInst

@[grind cases]
inductive SpecRule : Type where
| RL_callFetch

@[grind cases]
inductive WrappedRule : Type where
| RL_requestI
| RL_responseI
| RL_requestD
| RL_responseD
| RL_callFetch
| RL_decode
| RL_execute
| RL_writeback

def isa_callFetch (s : M_mktop_pipelined.Spec.State) : t_bool × M_mktop_pipelined.Spec.State :=
  (M_mktop_pipelined.Spec.meth_RDY_doFecth s, (M_mktop_pipelined.Spec.meth_doFetch s).avAction_)

def HiddenSpecModule : Bluespec.Module SpecRule Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules
    | .RL_callFetch => orStutterRl <| ofRule isa_callFetch

/-- The ISA spec with fetch as a plain (non-stuttering) internal rule. -/
def FetchSpecModule : Bluespec.Module SpecRule Method where
  State := M_mktop_pipelined.Spec.State
  methods
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.Spec.meth_getCommitInst M_mktop_pipelined.Spec.meth_RDY_getCommitInst
  rules
    | .RL_callFetch => ofRule isa_callFetch

def rule_RL_callFetch (s : M_mktop_pipelined.state) : t_bool × M_mktop_pipelined.state :=
  (M_mktop_pipelined.meth_RDY_doFetch s, (M_mktop_pipelined.meth_doFetch s).avAction_)

def WrappedModule : Bluespec.Module WrappedRule Method where
  State := M_mktop_pipelined.state
  methods
    | .getCommitInst => ofAVMethod0 M_mktop_pipelined.meth_getCommitInst M_mktop_pipelined.meth_RDY_getCommitInst
  rules
    | .RL_requestI => ofRule M_mktop_pipelined.rule_RL_requestI
    | .RL_responseI => ofRule M_mktop_pipelined.rule_RL_responseI
    | .RL_requestD => ofRule M_mktop_pipelined.rule_RL_requestD
    | .RL_responseD => ofRule M_mktop_pipelined.rule_RL_responseD
    | .RL_callFetch => orStutterRl <| ofRule rule_RL_callFetch
    | .RL_decode => ofRule M_mktop_pipelined.rule_RL_decode
    | .RL_execute => ofRule M_mktop_pipelined.rule_RL_execute
    | .RL_writeback => ofRule M_mktop_pipelined.rule_RL_writeback

/-- Erase a `doFetch` event; keep a `getCommitInst` event with the same footprint. -/
def hideEvent : Event M_mktop_pipelined.Refines.Method → Option (Event Method)
  | ⟨.doFetch, _⟩ => none
  | ⟨.getCommitInst, fp⟩ => some ⟨.getCommitInst, fp⟩

def hide (l : List (Event M_mktop_pipelined.Refines.Method)) : List (Event Method) :=
  l.filterMap hideEvent

@[simp] theorem hide_append (l₁ l₂ : List (Event M_mktop_pipelined.Refines.Method)) :
    hide (l₁ ++ l₂) = hide l₁ ++ hide l₂ := List.filterMap_append

-- ─── Spec side: hiding ─────────────────────────────────────────────────

theorem hide_fetch {s s' : SpecModule.State} {l : List (Event M_mktop_pipelined.Refines.Method)} :
    star SpecModule.getMethod s l s' →
    star_extend HiddenSpecModule.getARule HiddenSpecModule.getMethod s (hide l) s' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step s₂ s₃ l e _ hm ih =>
    obtain ⟨name, fp⟩ := e
    cases name
    · -- `doFetch` becomes zero or one internal `RL_callFetch` step.
      have hr : trans_refl HiddenSpecModule.getARule s₂ s₃ := by
        rcases hm with ⟨v, hv, -, -⟩ | ⟨-, rfl⟩
        · refine .step ⟨.RL_callFetch, Or.inl ?_⟩ .refl
          simp only [ofRule, isa_callFetch, M_mktop_pipelined.Spec.meth_RDY_doFecth, hv]
        · exact .refl
      exact .step_int _ _ _ _ ih hr
    · -- `getCommitInst` is the same method on both sides.
      exact .step_ext _ _ _ _ _ ih hm

-- ─── Spec side: dropping the fetch stutter ───────────────────────────

theorem unstutter_rules {s s' : M_mktop_pipelined.Spec.State} :
    trans_refl HiddenSpecModule.getARule s s' → trans_refl FetchSpecModule.getARule s s' := by
  intro h
  induction h with
  | refl => exact .refl
  | step hab _ ih =>
    obtain ⟨⟨⟩, hab | rfl⟩ := hab
    · exact .step ⟨.RL_callFetch, hab⟩ ih
    · exact ih

/-- `HiddenSpecModule` refines `FetchSpecModule`: a stuttering `RL_callFetch` is matched by no step. -/
theorem hidden_refines_fetch {s s' : M_mktop_pipelined.Spec.State} {l : List (Event Method)} :
    star_extend HiddenSpecModule.getARule HiddenSpecModule.getMethod s l s' →
    star_extend FetchSpecModule.getARule FetchSpecModule.getMethod s l s' := by
  intro h
  induction h with
  | refl => exact .refl _
  | step_int _ _ _ _ htr ih => exact .step_int _ _ _ _ ih (unstutter_rules htr)
  | step_ext _ _ _ _ _ hm ih => exact .step_ext _ _ _ _ _ ih hm

-- ─── Implementation side: unhiding ─────────────────────────────────────

theorem star_extend_append {A E} {rule : ReachingStar.Rule A} {method : ReachingStar.Method A E}
    {s t u : A} {l₁ l₂ : List E} :
    star_extend rule method s l₁ t → star_extend rule method t l₂ u →
    star_extend rule method s (l₂ ++ l₁) u := by
  intro h₁ h₂
  induction h₂ with
  | refl => exact h₁
  | step_int _ _ _ _ hr ih => exact .step_int _ _ _ _ ih hr
  | step_ext _ _ _ _ _ hm ih => exact .step_ext _ _ _ _ _ ih hm

/-- One `WrappedModule` rule step is a pipeline run whose events are all `doFetch`. -/
theorem unhide_rule {a b : M_mktop_pipelined.state} (h : WrappedModule.getARule a b) :
    ∃ l', star_extend ImplModule.getARule ImplModule.getMethod a l' b ∧ hide l' = [] := by
  obtain ⟨r, hr⟩ := h
  have rule : ∀ r', ImplModule.getRule r' a b →
      ∃ l', star_extend ImplModule.getARule ImplModule.getMethod a l' b ∧ hide l' = [] :=
    fun r' h => ⟨[], .step_int _ _ _ _ (.refl _) (.step ⟨r', h⟩ .refl), rfl⟩
  cases r
  · exact rule .RL_requestI hr
  · exact rule .RL_responseI hr
  · exact rule .RL_requestD hr
  · exact rule .RL_responseD hr
  · rcases hr with hr | rfl
    · simp only [ofRule, rule_RL_callFetch, Prod.mk.injEq] at hr
      obtain ⟨hrdy, rfl⟩ := hr
      refine ⟨[⟨.doFetch, Footprint.arg0 (M_mktop_pipelined.meth_doFetch a).avValue_⟩],
        .step_ext _ _ _ _ _ (.refl _) (Or.inl ⟨_, rfl, rfl, hrdy⟩), rfl⟩
    · exact ⟨[], .refl _, rfl⟩
  · exact rule .RL_decode hr
  · exact rule .RL_execute hr
  · exact rule .RL_writeback hr

theorem unhide_rules {a b : M_mktop_pipelined.state} (h : trans_refl WrappedModule.getARule a b) :
    ∃ l', star_extend ImplModule.getARule ImplModule.getMethod a l' b ∧ hide l' = [] := by
  induction h with
  | refl => exact ⟨[], .refl _, rfl⟩
  | step hab _ ih =>
    obtain ⟨l₁, h₁, hh₁⟩ := unhide_rule hab
    obtain ⟨l₂, h₂, hh₂⟩ := ih
    exact ⟨l₂ ++ l₁, star_extend_append h₁ h₂, by simp [hh₁, hh₂]⟩

/-- Every `WrappedModule` run over `l` is a run of the method-based pipeline over some `l'` whose
non-`doFetch` events are exactly `l`. -/
theorem unhide {a b : M_mktop_pipelined.state} {l : List (Event Method)} :
    star_extend WrappedModule.getARule WrappedModule.getMethod a l b →
    ∃ l', star_extend ImplModule.getARule ImplModule.getMethod a l' b ∧ hide l' = l := by
  intro h
  induction h with
  | refl => exact ⟨[], .refl _, rfl⟩
  | step_int _ _ _ _ htr ih =>
    obtain ⟨l₁, h₁, hh₁⟩ := ih
    obtain ⟨l₂, h₂, hh₂⟩ := unhide_rules htr
    exact ⟨l₂ ++ l₁, star_extend_append h₁ h₂, by simp [hh₁, hh₂]⟩
  | step_ext l _ _ e _ hm ih =>
    obtain ⟨l₁, h₁, hh₁⟩ := ih
    obtain ⟨⟨⟩, fp⟩ := e
    exact ⟨⟨.getCommitInst, fp⟩ :: l₁, .step_ext _ _ _ _ _ h₁ hm, by simp [hide, hideEvent, ← hh₁]⟩

-- ─── Composition ───────────────────────────────────────────────────────

/-- Trace inclusion from reset, with fetch hidden on both sides: every trace of the pipeline with
fetch as an internal rule is a trace of the ISA spec with fetch as an internal rule, started with
the same `pc`, registers and memories, no pending commit records, and halted iff the pipeline is. -/
theorem trace_inclusion (l : List (Event Method)) (i : WrappedModule.State) (h : ImplModule.init i) :
    imp_behaviour WrappedModule.getARule WrappedModule.getMethod l i →
    ∃ s', star_extend HiddenSpecModule.getARule HiddenSpecModule.getMethod
      (⟨i.pc, bool_to_bitvec1 i.hcf, i.rf, i.iMem.memory, i.dMem.memory, []⟩ : SpecModule.State) l s' := by
  rintro ⟨i', hi⟩
  obtain ⟨l', hi', rfl⟩ := unhide hi
  obtain ⟨s', hs'⟩ := M_mktop_pipelined.Refines.trace_inclusion l' i h ⟨i', hi'⟩
  exact ⟨s', hide_fetch hs'⟩

#print axioms hidden_refines_fetch
#print axioms trace_inclusion

end M_mktop_pipelined.HideFetch
