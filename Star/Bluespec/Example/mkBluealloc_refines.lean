import Star.Bluespec.Example.mkBluealloc_spec
import Star.Bluespec.Basic
import Star.Tactic
import Mathlib.Logic.Relation

set_option autoImplicit false

open BluespecPrelude
open Bluealloc_types
open BluespecVerification
open ReachingStar Bluespec

namespace M_mkBluealloc.Modules

inductive Methods : Type where
| alloc
| free
| write_req
| read_req
| read_resp

def SpecModule : Bluespec.Module Empty Methods where
  A := Spec.State
  transitions e :=
    match e with
    | .rule s => Empty.casesOn _ s
    | .method e =>
      match e.name with
      | .alloc => ofAVMethod0 Spec.meth_alloc Spec.meth_RDY_alloc e
      | .free => ofAVMethod1 Spec.meth_free Spec.meth_RDY_free e
      | .write_req => ofAVMethod2 Spec.meth_write_req Spec.meth_RDY_write_req e
      | .read_req => ofAVMethod1 Spec.meth_read_req Spec.meth_RDY_read_req e
      | .read_resp => ofAVMethod0 Spec.meth_read_resp Spec.meth_RDY_read_resp e

def ImplModule : Bluespec.Module Verify.RuleTag Methods where
  A := state
  transitions e :=
    match e with
    | .rule s =>
      match s with
      | .RL_do_read_index => ofRule rule_RL_do_read_index
      | .RL_do_write_index => ofRule rule_RL_do_write_index
      | .RL_do_free_lookup => ofRule rule_RL_do_free_lookup
      | .RL_do_free_read => ofRule rule_RL_do_free_read
      | .RL_do_free_write => ofRule rule_RL_do_free_write
      | .RL_do_alloc_prefetch => ofRule rule_RL_do_alloc_prefetch
      | .RL_do_alloc_wait => ofRule rule_RL_do_alloc_wait
    | .method e =>
      match e.name with
      | .alloc => ofAVMethod0 meth_alloc meth_RDY_alloc e
      | .free => ofAVMethod1 meth_free meth_RDY_free e
      | .write_req => ofAVMethod2 meth_write_req meth_RDY_write_req e
      | .read_req => ofAVMethod1 meth_read_req meth_RDY_read_req e
      | .read_resp => ofAVMethod0 meth_read_resp meth_RDY_read_resp e

/- theorem applyRules_trans_refl {l s s'} :
 -   Verify.applyRules l s = s' → trans_refl ImplModule.getARule s s' := by -/

axiom trans_refl_trans {A r s s'' s'} : @trans_refl A r s s'' → trans_refl r s'' s' → trans_refl r s s'
axiom newmans_lemma :
  commutes_weakly ImplModule.getARule ImplModule.getARule →
  strongly_normalising ImplModule.getARule →
  has_diamond_property (trans_refl ImplModule.getARule)
axiom is_strongly_normalising : strongly_normalising ImplModule.getARule

theorem applyRule_rule {l s} :
  ImplModule.getARule s (Verify.applyRule l s) ∨ s = Verify.applyRule l s := by
  dsimp [Verify.applyRule]; cases l <;> dsimp at * <;> split <;> subst_vars <;> (try right; rfl) <;> left
  · exists .RL_do_read_index; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_write_index; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_free_lookup; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_free_read; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_free_write; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_alloc_prefetch; dsimp [ImplModule, Module.getRule, ofRule]; grind
  · exists .RL_do_alloc_wait; dsimp [ImplModule, Module.getRule, ofRule]; grind

/- theorem applyRule_rule_refl {l s} :
 -   Refl ImplModule.getARule s (Verify.applyRule l s) := by -/

theorem rule_applyRule {l s s'} :
  ImplModule.getRule l s s' → Verify.applyRule l s = s' := by
  intro hget
  dsimp [ImplModule, Module.getRule, Verify.applyRule] at *
  split <;> dsimp [ofRule] at * <;> grind

theorem arule_applyRule {s s'} :
  ImplModule.getARule s s' → ∃ l, Verify.applyRule l s = s' := by
  dsimp [Module.getARule]; intro h; cases h; constructor; apply rule_applyRule; assumption

theorem applyRules_trans_refl {l s s'} :
  Verify.applyRules l s = s' → trans_refl ImplModule.getARule s s' := by
  induction l generalizing s s' with
  | nil => dsimp [Verify.applyRules]; intros; subst_vars; apply trans_refl.refl
  | cons head tail ih =>
    dsimp [Verify.applyRules]
    intro ha; specialize ih ha
    apply trans_refl_trans <;> try assumption
    cases @applyRule_rule head s
    · apply trans_refl.step; assumption; apply trans_refl.refl
    · rename_i h'; rw [←h']; apply trans_refl.refl

theorem commutes_RL_do_read_index_RL_do_write_index {a b c : ImplModule.A} :
  ImplModule.getRule Verify.RuleTag.RL_do_read_index a c →
  ImplModule.getRule Verify.RuleTag.RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by sorry

theorem t_commutes_weakly : commutes_weakly ImplModule.getARule ImplModule.getARule := by
  dsimp [ReachingStar.commutes_weakly]
  intro a b c r1 r2
  dsimp [Module.getARule] at *
  obtain ⟨r1, hr1⟩ := r1
  obtain ⟨r2, hr2⟩ := r2
  cases r1 <;> cases r2
  · obtain hr1' := rule_applyRule hr1
    obtain hr2' := rule_applyRule hr2
    have : c = b := by grind
    exists c; and_intros
    · subst_vars; apply trans_refl.refl
    · subst_vars; apply trans_refl.refl
  · sorry
  all_goals sorry

theorem ofAVMethod0_correct {M State Value} {meth : State → t_actionvalue_ Value State} {meth_RDY : State → t_bool} {s s' : State} {name : M} {v} :
  ofAVMethod0 meth meth_RDY (Event.arg0 name v) s s' ↔ (meth s = ⟨v, s'⟩ ∧ isReady (meth_RDY s)) := by
  dsimp [ofAVMethod0] at *
  constructor
  · intro ⟨v', name', hmeth, harg, hrdy⟩
    cases harg; simp [*, isReady]
  · intro ⟨hl, hr⟩
    dsimp [isReady] at *; simp [*]
    grind

theorem ofAVMethod1_correct {M State A1 Value} {meth : State → A1 → t_actionvalue_ Value State} {meth_RDY : State → t_bool} {s s' : State} {name : M} {a1 v} :
  ofAVMethod1 meth meth_RDY (Event.arg1 name a1 v) s s' ↔ (meth s a1 = ⟨v, s'⟩ ∧ isReady (meth_RDY s)) := by
  dsimp [ofAVMethod1] at *; dsimp at a1
  constructor
  · intro ⟨a1', v', name', hmeth, harg, hrdy⟩
    cases harg; simp [*, isReady]
  · intro ⟨hl, hr⟩
    dsimp [isReady] at *; simp [*]
    grind

theorem ofAVMethod2_correct {M State A1 A2 Value} {meth : State → A1 → A2 → t_actionvalue_ Value State} {meth_RDY : State → t_bool} {s s' : State} {name : M} {a1 a2 v} :
  ofAVMethod2 meth meth_RDY (Event.arg2 name a1 a2 v) s s' ↔ (meth s a1 a2 = ⟨v, s'⟩ ∧ isReady (meth_RDY s)) := by
  dsimp [ofAVMethod2] at *; dsimp at a1; dsimp at a2
  constructor
  · intro ⟨a1', a2', v', name', hmeth, harg, hrdy⟩
    cases harg; simp [*, isReady]
  · intro ⟨hl, hr⟩
    dsimp [isReady] at *; simp [*]
    grind

theorem reconverge_RL_do_alloc_prefetch_write_req (s s' s'': state) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s (Event.arg2 .write_req write_req_addr write_req_data v) s'' →
  ∃ s''',
    ImplModule.getMethod s' (Event.arg2 .write_req write_req_addr write_req_data v) s'''
    ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by
  dsimp [ImplModule, Module.getRule, Module.getMethod, ofRule]
  intro hrule hmethod
  change ofAVMethod2 meth_write_req meth_RDY_write_req
    (Event.arg2 Methods.write_req write_req_addr write_req_data v) s s'' at hmethod
  change ∃ s''',
    ofAVMethod2 meth_write_req meth_RDY_write_req
      (Event.arg2 Methods.write_req write_req_addr write_req_data v) s' s'''
      ∧ rule_RL_do_alloc_prefetch s'' = (BTrue Unit_, s''')
  rw [ofAVMethod2_correct] at hmethod
  have hfull := Verify.reconverge_RL_do_alloc_prefetch_write_req_full s write_req_addr write_req_data (by grind) (by grind)
  have : (rule_RL_do_alloc_prefetch s).2 = s' := by grind
  have : (meth_write_req s write_req_addr write_req_data).avAction_ = s'' := by grind
  subst_vars
  exists (meth_write_req (rule_RL_do_alloc_prefetch s).snd write_req_addr write_req_data).avAction_
  grind [isReady, ofAVMethod2_correct]

theorem reconverge_RL_do_alloc_prefetch_write_req2 {S T F typs args ret a c b} :
  ImplModule.transitions
      (MethodOrRule.method { V := S, α := T, f := F, l := typs, name := Methods.write_req, args := args, ret := ret }) a c →
  ImplModule.transitions (MethodOrRule.rule Verify.RuleTag.RL_do_alloc_prefetch) a b →
  ∃ d,
      ImplModule.transitions
          (MethodOrRule.method { V := S, α := T, f := F, l := typs, name := Methods.write_req, args := args, ret := ret }) b
          d ∧
        ImplModule.transitions (MethodOrRule.rule Verify.RuleTag.RL_do_alloc_prefetch) c d := by
  /- dsimp [ImplModule, ofAVMethod2]
   - intro ha hb -/
 sorry

def flush : ImplModule.A → SpecModule.A → Prop := M_mkBluealloc.WeakSim.phi0

theorem flush_indistinguishable_write_req (i i' : ImplModule.A) (s : SpecModule.A) 
        (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) : 
  flush i s -> 
  ImplModule.getMethod i (Event.arg2 .write_req write_req_addr write_req_data v) i' -> 
  ∃ s', SpecModule.getMethod s (Event.arg2 .write_req write_req_addr write_req_data v) s' := by sorry

theorem reach_flush_again_write_req (i i' : ImplModule.A) (s s' : SpecModule.A) 
        (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  flush i s -> 
  ImplModule.getMethod i (Event.arg2 .write_req write_req_addr write_req_data v) i' -> 
  SpecModule.getMethod s (Event.arg2 .write_req write_req_addr write_req_data v) s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flush i'' s' := by sorry

theorem flush_reaches_flush_RL_do_read_index (i i' : ImplModule.A) (s : SpecModule.A) :
  flush i s -> ImplModule.getRule .RL_do_read_index i i' -> flush i' s := by sorry

/- theorem random :
 -   ofAVMethod2 a b -/

/- theorem t_commutes_strongly_method_rule : commutes_strongly_method_rule ImplModule.getMethod ImplModule.getARule := by
 -   unfold commutes_strongly_method_rule
 -   intro a b c e r1 m1
 -   dsimp [Module.getARule, Module.getMethod, Module.getRule] at *
 -   obtain ⟨r1, hr1⟩ := r1
 -   obtain ⟨S, T, F, typs, name, args, ret⟩ := e
 -   cases name <;> cases r1
 -   case write_req.RL_do_alloc_prefetch =>
 -     dsimp [ImplModule]
 -     skip -/

end M_mkBluealloc.Modules

namespace M_mkBluealloc.Refinement

end M_mkBluealloc.Refinement
