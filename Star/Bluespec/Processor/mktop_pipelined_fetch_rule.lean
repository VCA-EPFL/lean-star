import Star.Bluespec.Processor.mktop_pipelined_refines
open BluespecPrelude Params_types
open ReachingStar Bluespec

/-!
Fetch as an internal rule, with `getCommitInst` as the only method.

* `ImplF`: the pipeline's seven rules plus `RL_fetch` (the body of `doFetch`, without a stutter).
* `SpecF`: the ISA with no internal steps; `getCommitInst` executes one instruction and returns
  its commit record.

The two commutation obligations of `StructuredRefinementUpto` are proved here for `ImplF`
(`rules_commute_weakly`, `method_rule_commute`), all from the lemmas of
`mktop_pipelined_refines`: a fetch against another rule is the old `doFetch`/rule commutation
(`method_rule_commute_upto`) read with fetch as a rule.

`ImplF` is still not an instance of `StructuredRefinementUpto`, because its rules are not strongly
normalising (`not_strongly_normalising`): fetch is enabled whenever the processor has not halted.
-/

namespace M_mktop_pipelined.FetchRule

open M_mktop_pipelined

@[grind cases]
inductive Method : Type where
| getCommitInst

inductive Rule : Type where
| old (r : Refines.Rule)
| RL_fetch

def rule_RL_fetch (s : state) : t_bool × state := (meth_RDY_doFetch s, (meth_doFetch s).avAction_)

def ImplF : Bluespec.Module Rule Method where
  State := state
  methods
    | .getCommitInst => ofAVMethod0 meth_getCommitInst meth_RDY_getCommitInst
  rules
    | .old r => Refines.ImplModule.rules r
    | .RL_fetch => ofRule rule_RL_fetch

-- ─── Specification: `getCommitInst` executes one instruction ──────────

/-- Execute the next instruction and hand out its commit record. -/
def spec_getCommitInst (s : Spec.State) : t_actionvalue_ t_commitinst Spec.State :=
  let t := Spec.stepOne { s with output := [] }
  ⟨t.output.headD default, { t with output := [] }⟩

/-- Ready when the next instruction commits (not after a halt). -/
def spec_RDY_getCommitInst (s : Spec.State) : t_bool :=
  match (Spec.stepOne { s with output := [] }).output with
  | [] => BFalse Unit_
  | _ => BTrue Unit_

def SpecF : Bluespec.Module Empty Method where
  State := Spec.State
  methods
    | .getCommitInst => ofAVMethod0 spec_getCommitInst spec_RDY_getCommitInst
  rules := Empty.casesOn _

-- ─── Reachability ──────────────────────────────────────────────────────

def ImplF.atrans (s s' : state) : Prop := ImplF.getARule s s' ∨ ∃ e, ImplF.getMethod s e s'

def ImplF.reachable (s : state) : Prop :=
  ∃ s0, Refines.ImplModule.init s0 ∧ Relation.ReflTransGen ImplF.atrans s0 s

theorem ImplF.reachable_rule {a b : state} : ImplF.reachable a → ImplF.getARule a b → ImplF.reachable b :=
  fun ⟨s0, h0, hst⟩ hab => ⟨s0, h0, hst.tail (.inl hab)⟩

theorem ImplF.reachable_method {a b : state} {e : Event Method} :
    ImplF.reachable a → ImplF.getMethod a e b → ImplF.reachable b :=
  fun ⟨s0, h0, hst⟩ hab => ⟨s0, h0, hst.tail (.inr ⟨e, hab⟩)⟩

/-- A fetch is a real (non-stuttering) `doFetch` of the method-based pipeline. -/
theorem fetch_doFetch {a c : state} (h : ImplF.getRule .RL_fetch a c) :
    meth_RDY_doFetch a = BTrue Unit_ ∧ c = (meth_doFetch a).avAction_ ∧
    Refines.ImplModule.getMethod a ⟨.doFetch, Footprint.arg0 (meth_doFetch a).avValue_⟩ c := by
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp h
  exact ⟨hg, rfl, Or.inl ⟨_, rfl, rfl, hg⟩⟩

theorem atrans_old {s s' : state} (h : ImplF.atrans s s') : Refines.ImplModule.atrans s s' := by
  rcases h with ⟨r, hr⟩ | ⟨⟨⟨⟩, fp⟩, hm⟩
  · cases r with
    | old r => exact .inl ⟨r, hr⟩
    | RL_fetch => exact .inr ⟨_, (fetch_doFetch hr).2.2⟩
  · exact .inr ⟨⟨.getCommitInst, fp⟩, hm⟩

/-- Every state reachable with fetch as a rule is reachable in the method-based pipeline. -/
theorem reachable_old {s : state} (h : ImplF.reachable s) : Refines.ImplModule.reachable s :=
  let ⟨s0, h0, hst⟩ := h
  ⟨s0, h0, hst.mono fun _ _ => atrans_old⟩

theorem lift_old {a b : state} (h : Relation.ReflTransGen Refines.ImplModule.getARule a b) :
    Relation.ReflTransGen ImplF.getARule a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨r, hr⟩ := hs; exact ih.tail ⟨.old r, hr⟩

-- ─── Local confluence of the rules, fetch included ─────────────────────

/-- A fetch against an old rule: the old `doFetch`/rule commutation, with the (real or stuttering)
`doFetch` on the rule side read as a fetch or as no step. -/
theorem fetch_old_join {a b c : state} (hR : Refines.ImplModule.reachable a)
    (hr : Refines.ImplModule.getARule a b) (hf : ImplF.getRule .RL_fetch a c) :
    ∃ d, Relation.ReflTransGen ImplF.getARule c d ∧ Relation.ReflTransGen ImplF.getARule b d := by
  obtain ⟨-, -, hm⟩ := fetch_doFetch hf
  obtain ⟨b', d, j, hbb', hd, hcj, hdj⟩ := Refines.method_rule_commute_upto hR hr hm
  refine ⟨j, lift_old hcj, ?_⟩
  dsimp only [Refines.ImplModule, Module.getMethod, orStutter0, ofAVMethod0] at hd
  rcases hd with ⟨v, hv, -, hrdy⟩ | ⟨-, rfl⟩
  · have : d = (meth_doFetch b').avAction_ := by rw [hv]
    subst this
    exact (lift_old hbb').trans (.head ⟨.RL_fetch, Prod.ext hrdy rfl⟩ (lift_old hdj))
  · exact (lift_old hbb').trans (lift_old hdj)

theorem rules_commute_weakly {a b c : state} :
    ImplF.reachable a → ImplF.getARule a c → ImplF.getARule a b →
    ∃ d, Relation.ReflTransGen ImplF.getARule c d ∧ Relation.ReflTransGen ImplF.getARule b d := by
  rintro hR ⟨r1, h1⟩ ⟨r2, h2⟩
  have hR' := reachable_old hR
  cases r1 with
  | old r1 =>
    cases r2 with
    | old r2 =>
      obtain ⟨d, hc, hb⟩ := Refines.rules_commute_weakly_reachable hR' ⟨r1, h1⟩ ⟨r2, h2⟩
      exact ⟨d, lift_old hc, lift_old hb⟩
    | RL_fetch =>
      obtain ⟨d, hb, hc⟩ := fetch_old_join hR' ⟨r1, h1⟩ h2
      exact ⟨d, hc, hb⟩
  | RL_fetch =>
    cases r2 with
    | old r2 => exact fetch_old_join hR' ⟨r2, h2⟩ h1
    | RL_fetch =>
      -- fetch is deterministic
      obtain rfl := (fetch_doFetch h1).2.1
      obtain rfl := (fetch_doFetch h2).2.1
      exact ⟨_, .refl, .refl⟩

-- ─── Method/rule commutation ───────────────────────────────────────────

theorem method_rule_commute {a b c : state} {e : Event Method} :
    ImplF.reachable a → ImplF.getARule a b → ImplF.getMethod a e c →
    ∃ b' d j, Relation.ReflTransGen ImplF.getARule b b' ∧ ImplF.getMethod b' e d ∧
      Relation.ReflTransGen ImplF.getARule c j ∧ Relation.ReflTransGen ImplF.getARule d j := by
  rintro hR ⟨r, hr⟩ hm
  obtain ⟨⟨⟩, fp⟩ := e
  cases r with
  | old r =>
    obtain ⟨b', d, j, h1, h2, h3, h4⟩ :=
      Refines.method_rule_commute_upto (e := ⟨.getCommitInst, fp⟩) (reachable_old hR) ⟨r, hr⟩ hm
    exact ⟨b', d, j, lift_old h1, h2, lift_old h3, lift_old h4⟩
  | RL_fetch =>
    -- fetch and `getCommitInst` touch disjoint fields: they commute in one step
    obtain ⟨hg, rfl, -⟩ := fetch_doFetch hr
    obtain ⟨v, hv, hfp, hrdy⟩ := hm
    have hc : c = (meth_getCommitInst a).avAction_ := by rw [hv]
    have hvv : v = (meth_getCommitInst a).avValue_ := by rw [hv]
    subst hc hvv
    exact ⟨_, _, _, .refl, ⟨_, rfl, hfp, hrdy⟩, .single ⟨.RL_fetch, Prod.ext hg rfl⟩, .refl⟩

-- ─── Strong normalisation fails ────────────────────────────────────────

/-- Fetch can fire forever from any state that has not halted. -/
theorem not_strongly_normalising : ¬ strongly_normalising ImplF.getARule := by
  intro h
  have key : ∀ a, strongly_normalising' ImplF.getARule a → a.hcf = BFalse Unit_ → False := by
    intro a ha
    induction ha with
    | @step a _ ih =>
      intro hh
      have hg : meth_RDY_doFetch a = BTrue Unit_ := by
        simp [meth_RDY_doFetch, hh, M_mkFIFO.meth_RDY_enq, bool_to_bitvec1, bit_not, bitvec1_to_bool,
          bool_and]
      exact ih _ ⟨.RL_fetch, Prod.ext hg rfl⟩ hh
  let s : state := { (default : state) with hcf := BFalse Unit_ }
  exact key s (h s) rfl

#print axioms rules_commute_weakly
#print axioms method_rule_commute
#print axioms not_strongly_normalising

end M_mktop_pipelined.FetchRule
