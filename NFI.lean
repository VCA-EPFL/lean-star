/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Star.Bluespec.Basic
import Star.Bluespec.Lib.BluespecPrelude
import Star.Bluespec.Lib.BluespecVerification
import SecurityPolicy

/-!
# Generic non-interference definitions

LTSs and their weak bisimilarity, the ORAAT semantics of a module, its projections `⟦M⟧^P` and
`⟦M⟧^{P_i}` by a policy, functional non-interference (Definition 3), and `NFI`, which overwrites
high inputs and is equivalent to it. The policies themselves are in `SecurityPolicy.lean`.
-/

open BluespecPrelude
open BluespecVerification

namespace ReachingStar.Security

open ReachingStar.Bluespec

/-! ## Labelled transition systems -/

/-- A labelled transition system `(S, L, T, I)`.

Arguments:
* `S`: the set of states.
* `L`: the set of labels, which may contain the silent label `τ` as `LTSLabel E` does. -/
structure LTS (S L : Type _) where
  /-- The transition relation, `T ⊆ S × L × S`. -/
  T : Set (S × L × S)
  /-- The initial state, `I ∈ S`. -/
  I : S

namespace LTS

variable {S Sa Sb L : Type _} {E E' : Type _}

/-- The paper's `s -l→ s'`: `(s, l, s') ∈ T`.

Arguments:
* `A`: the LTS.
* `s`, `s'`: the start and end states.
* `l`: the label. -/
abbrev Step (A : LTS S L) (s : S) (l : L) (s' : S) : Prop :=
  (s, l, s') ∈ A.T

/-- Notation for `s -l→ s'` in the LTS `A`.

Arguments:
* `s`, `s'`: the start and end states.
* `A`: the LTS.
* `l`: the label. -/
scoped notation:50 s " ⟶[" A ", " l "] " s' => LTS.Step A s l s'

/-- Definition 1: `R` is a bisimulation relation for `A` and `B`.

Arguments:
* `A`, `B`: the two LTSs, over the same labels.
* `R`: the candidate relation between states of `A` and states of `B`. -/
def IsBisimRel (A : LTS Sa L) (B : LTS Sb L) (R : Sa → Sb → Prop) : Prop :=
  ∀ a b, R a b → ∀ l : L,
    (∀ a', (a ⟶[A, l] a') → ∃ b', (b ⟶[B, l] b') ∧ R a' b') ∧
    (∀ b', (b ⟶[B, l] b') → ∃ a', (a ⟶[A, l] a') ∧ R a' b')

/-- `A ∼ B`: some bisimulation relation relates `I_A` and `I_B`.

Arguments:
* `A`, `B`: the two LTSs, compared from their initial states. -/
def StronglyBisimilar (A : LTS Sa L) (B : LTS Sb L) : Prop :=
  ∃ R : Sa → Sb → Prop, IsBisimRel A B R ∧ R A.I B.I

/-- Notation for strong bisimilarity. -/
scoped infix:50 " ∼ " => LTS.StronglyBisimilar

/-- Zero or more `τ` steps.

Arguments:
* `A`: the LTS.
* the arguments: the start and end states. -/
def TauStar (A : LTS S (LTSLabel E)) : S → S → Prop :=
  Relation.ReflTransGen (fun s s' => A.Step s .τ s')

/-- The paper's `a =l⇒ a'`: zero or more silent transitions `τ` before and after the `l`-transition.

Arguments:
* `A`: the LTS.
* `a`, `a'`: the start and end states.
* `l`: the label. -/
def WeakStep (A : LTS S (LTSLabel E)) (a : S) (l : LTSLabel E) (a' : S) : Prop :=
  ∃ a₁ a₂, A.TauStar a a₁ ∧ A.Step a₁ l a₂ ∧ A.TauStar a₂ a'

/-- Definition 2: `R` is a weak bisimulation relation for `A` and `B`.

Arguments:
* `A`, `B`: the two LTSs, over the same labels.
* `R`: the candidate relation between states of `A` and states of `B`. -/
def IsWeakBisimRel (A : LTS Sa (LTSLabel E)) (B : LTS Sb (LTSLabel E))
    (R : Sa → Sb → Prop) : Prop :=
  ∀ a b, R a b → ∀ l : LTSLabel E,
    (∀ a', A.Step a l a' → ∃ b', B.WeakStep b l b' ∧ R a' b') ∧
    (∀ b', B.Step b l b' → ∃ a', A.WeakStep a l a' ∧ R a' b')

/-- `A ≈ B`: some weak bisimulation relation relates `I_A` and `I_B`.

Arguments:
* `A`, `B`: the two LTSs, compared from their initial states. -/
def WeaklyBisimilar (A : LTS Sa (LTSLabel E)) (B : LTS Sb (LTSLabel E)) : Prop :=
  ∃ R : Sa → Sb → Prop, IsWeakBisimRel A B R ∧ R A.I B.I

/-- Notation for `s =l⇒ s'` in the LTS `A`.

Arguments:
* `s`, `s'`: the start and end states.
* `A`: the LTS.
* `l`: the label. -/
scoped notation:50 s " ⟹[" A ", " l "] " s' => LTS.WeakStep A s l s'

/-- Notation for weak bisimilarity. -/
scoped infix:50 " ≈ " => LTS.WeaklyBisimilar

/-- A step is a weak step.

Arguments:
* `h`: the step.

Proof: With no `τ` before or after. -/
theorem WeakStep.of_step {A : LTS S (LTSLabel E)} {s s' : S} {l : LTSLabel E}
    (h : s ⟶[A, l] s') : s ⟹[A, l] s' :=
  ⟨s, s', .refl, h, .refl⟩

/-- Relabelling: `(S, L, T, I) ↦ (S, f(L), {(s, f l, s') | (s, l, s') ∈ T}, I)`.

Arguments:
* `A`: the LTS to relabel.
* `f`: the function applied to every label, such as a projection `↓F_P`. -/
def map (A : LTS S (LTSLabel E)) (f : LTSLabel E → LTSLabel E') : LTS S (LTSLabel E') where
  T := {t | ∃ l, f l = t.2.1 ∧ A.Step t.1 l t.2.2}
  I := A.I

/-- Every step of `A` gives a step of `A.map f`, with label `f l`.

Arguments:
* `h`: the step of `A`.

Proof: By the definition of `map`. -/
theorem map_step {A : LTS S (LTSLabel E)} {f : LTSLabel E → LTSLabel E'} {s s' : S} {l : LTSLabel E}
    (h : A.Step s l s') : (A.map f).Step s (f l) s' :=
  ⟨l, rfl, h⟩

/-- A `τ*` path on the left of a weak bisimulation is matched by a `τ*` path on the right.

Arguments:
* `hR`: the weak bisimulation.
* `hab`: the start states are related.
* `h`: the path on the left.

Proof: By induction on the path, matching each `τ` step with a weak `τ` step. -/
theorem IsWeakBisimRel.tauStar_left {A : LTS Sa (LTSLabel E)} {B : LTS Sb (LTSLabel E)}
    {R : Sa → Sb → Prop}
    (hR : IsWeakBisimRel A B R) {a a' : Sa} {b : Sb}
    (hab : R a b) (h : A.TauStar a a') :
    ∃ b', B.TauStar b b' ∧ R a' b' := by
  induction h with
  | refl => exact ⟨b, .refl, hab⟩
  | tail _ hst ih =>
      obtain ⟨b₁, hb₁, hr₁⟩ := ih
      obtain ⟨b₂, ⟨u, v, hp, hm, hq⟩, hr₂⟩ := (hR _ _ hr₁ .τ).1 _ hst
      exact ⟨b₂, hb₁.trans (hp.trans (.head hm hq)), hr₂⟩

/-- An invariant preserved by every step holds along `τ*` paths.

Arguments:
* `Inv`: the invariant.
* `hInv`: every step preserves `Inv`.
* `h`: the path.
* `ha`: `Inv` holds at the start.

Proof: By induction on the path. -/
theorem TauStar.invariant {A : LTS S (LTSLabel E)} {Inv : S → Prop}
    (hInv : ∀ s l s', Inv s → A.Step s l s' → Inv s')
    {a a' : S} (h : A.TauStar a a') (ha : Inv a) : Inv a' := by
  induction h with
  | refl => exact ha
  | tail _ hst ih => exact hInv _ _ _ ih hst

/-- An invariant preserved by every step holds after a weak step.

Arguments:
* `Inv`: the invariant.
* `hInv`: every step preserves `Inv`.
* `h`: the weak step.
* `ha`: `Inv` holds at the start.

Proof: Apply `TauStar.invariant` before and after the `l`-transition. -/
theorem WeakStep.invariant {A : LTS S (LTSLabel E)} {Inv : S → Prop}
    (hInv : ∀ s l s', Inv s → A.Step s l s' → Inv s')
    {a a' : S} {l : LTSLabel E} (h : A.WeakStep a l a') (ha : Inv a) : Inv a' := by
  obtain ⟨a₁, a₂, h₁, h₂, h₃⟩ := h
  exact TauStar.invariant hInv h₃ (hInv _ _ _ (TauStar.invariant hInv h₁ ha) h₂)

/-- An invariant of `A` is an invariant of any relabelling of `A`.

Arguments:
* `Inv`: the invariant.
* `hInv`: every step of `A` preserves `Inv`.

Proof: A step of `A.map f` comes from a step of `A`. -/
theorem map_invariant {A : LTS S (LTSLabel E)} {f : LTSLabel E → LTSLabel E'} {Inv : S → Prop}
    (hInv : ∀ s l s', Inv s → A.Step s l s' → Inv s') :
    ∀ s l s', Inv s → (A.map f).Step s l s' → Inv s' :=
  fun _ _ _ hs ⟨_, _, h⟩ => hInv _ _ _ hs h

end LTS

/-! ## ORAAT semantics of a module

Helper functions to convert a module into an LTS. -/

/-- `T_M`: a method call `(id, σ)` of `m` is a visible transition.

Arguments:
* `R`, `M`: the rule names and method names of the module.
* `m`: the module. -/
def _root_.ReachingStar.Bluespec.Module.methodTransitions {R M : Type} (m : Module R M) :
    Set (m.State × LTSLabel (Label M) × m.State) :=
  {t | ∃ s e s', m.getMethod s e s' ∧ t = (s, .vis e, s')}

/-- `T_R`: firing a rule of `m` is a `τ` transition.

Arguments:
* `R`, `M`: the rule names and method names of the module.
* `m`: the module. -/
def _root_.ReachingStar.Bluespec.Module.ruleTransitions {R M : Type} (m : Module R M) :
    Set (m.State × LTSLabel (Label M) × m.State) :=
  {t | ∃ s s', m.getARule s s' ∧ t = (s, .τ, s')}

/-- The LTS of a module: `⟦M⟧_ORAAT ≜ (S, L, T, I)` with `T = T_M ∪ T_R`. A `Module` has no initial
state of its own, so `init` is an argument.

Arguments:
* `R`, `M`: the rule names and method names of the module.
* `m`: the module.
* `init`: the initial state `I`. -/
def _root_.ReachingStar.Bluespec.Module.oraat {R M : Type} (m : Module R M)
    (init : m.State) : LTS m.State (LTSLabel (Label M)) where
  T := m.methodTransitions ∪ m.ruleTransitions
  I := init

/-- A `τ` step of `⟦M⟧_ORAAT` is exactly the firing of a rule of `M`.

Arguments:
* `m`: the module.
* `init`: the initial state.
* `s`, `s'`: the start and end states.

Proof: A `τ` label can only come from `T_R`. -/
theorem _root_.ReachingStar.Bluespec.Module.oraat_tau_iff {R M : Type} {m : Module R M}
    {init s s' : m.State} :
    (m.oraat init).Step s .τ s' ↔ m.getARule s s' := by
  constructor
  · rintro (⟨_, _, _, -, h⟩ | ⟨_, _, hr, h⟩)
    · cases h
    · cases h
      exact hr
  · exact fun h => .inr ⟨s, s', h, rfl⟩

/-- A visible step of `⟦M⟧_ORAAT` is exactly a call of the method of `M` with that label.

Arguments:
* `m`: the module.
* `init`: the initial state.
* `s`, `s'`: the start and end states.
* `e`: the label.

Proof: A visible label can only come from `T_M`. -/
theorem _root_.ReachingStar.Bluespec.Module.oraat_vis_iff {R M : Type} {m : Module R M}
    {init s s' : m.State} {e : Label M} :
    (m.oraat init).Step s (.vis e) s' ↔ m.getMethod s e s' := by
  constructor
  · rintro (⟨_, _, _, hm, h⟩ | ⟨_, _, -, h⟩)
    · cases h
      exact hm
    · cases h
  · exact fun h => .inl ⟨s, e, s', h, rfl⟩

/-! ## Projected semantics -/

namespace TwoLevelPolicy

variable {M : Type}

/-- `⟦M⟧^P_ORAAT`: the ORAAT semantics of `m` with labels projected by `↓F_P`.

Arguments:
* `R`: the rule names of the module.
* `P`: the policy.
* `m`: the module.
* `init`: the initial state. -/
def semF {R : Type} (P : TwoLevelPolicy M) (m : Module R M) (init : m.State) :
    LTS m.State (LTSLabel (Label M)) :=
  (m.oraat init).map P.projectF

/-- The timing view of `⟦M⟧^P_ORAAT`, with labels projected by `↓T_P`.

Arguments:
* `R`: the rule names of the module.
* `P`: the policy.
* `m`: the module.
* `init`: the initial state. -/
def semT {R : Type} (P : TwoLevelPolicy M) (m : Module R M) (init : m.State) :
    LTS m.State (LTSLabel (Label M)) :=
  (m.oraat init).map P.projectT

/-- `⟦M⟧^{P_i}_ORAAT = (S, L^P, T^{P_i}, I)` with
`T^{P_i} = {(s, l ↓F_P, s') | (s, l, s') ∈ T, low_P(l) ∨ idx_P(l) = i}`.

Arguments:
* `R`: the rule names of the module.
* `I`: the type of indices.
* `P`: the policy.
* `g`: the encoding of high inputs used by `idx_P`.
* `i`: the index of the combination of high inputs to keep.
* `m`: the module.
* `init`: the initial state. -/
noncomputable def semFAt {R I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I) (i : I)
    (m : Module R M) (init : m.State) : LTS m.State (LTSLabel (Label M)) where
  T := {t | ∃ l, P.projectF l = t.2.1 ∧ (m.oraat init).Step t.1 l t.2.2 ∧
    (P.low l ∨ P.idxL g l = i)}
  I := init

/-- A transition of `⟦M⟧_ORAAT` passing the filter is a transition of `⟦M⟧^{P_i}`.

Arguments:
* `h`: the transition.
* `hk`: it passes the filter.

Proof: By the definition of `semFAt`. -/
theorem semFAt_step {R I : Type _} [Zero I] {P : TwoLevelPolicy M} {g : Label M → I} {i : I}
    {m : Module R M} {init s s' : m.State} {l : LTSLabel (Label M)}
    (h : (m.oraat init).Step s l s') (hk : P.low l ∨ P.idxL g l = i) :
    (P.semFAt g i m init).Step s (P.projectF l) s' :=
  ⟨l, rfl, h, hk⟩

/-- Every transition of `⟦M⟧^{P_i}` is a transition of `⟦M⟧^P`: `T^{P_i} ⊆ T^P`.

Arguments:
* `P`: the policy.
* `g`: the encoding of high inputs used by `idx_P`.
* `i`: the index.
* `h`: the transition.

Proof: Forget the filter. -/
theorem semFAt_sub {R I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I)
    (i : I) {m : Module R M} {init s s' : m.State} {l : LTSLabel (Label M)}
    (h : (P.semFAt g i m init).Step s l s') : (P.semF m init).Step s l s' :=
  let ⟨l₀, hl, h, _⟩ := h
  ⟨l₀, hl, h⟩

/-- The concretization `M_i`: a module whose methods are the transitions of `m` passing the filter
of `T^{P_i}`, with the same states and rules. It is a proof tool: FNI is defined on the LTS by
`semFAt`, and `semF_concretize` shows that the two agree.

Arguments:
* `R`: the rule names of the module.
* `I`: the type of indices.
* `P`: the policy.
* `g`: the encoding of high inputs used by `idx_P`.
* `i`: the index of the combination of high inputs to keep.
* `m`: the module to concretize. -/
noncomputable def concretize {R I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I)
    (i : I) (m : Module R M) : Module R M where
  State   := m.State
  rules   := m.rules
  methods := fun n fp s s' => m.methods n fp s s' ∧ (P.IsLow ⟨n, fp⟩ ∨ P.idx g ⟨n, fp⟩ = i)

/-- A transition of `⟦M_i⟧_ORAAT` is a transition of `⟦M⟧_ORAAT` passing the filter.

Arguments:
* `m`: the module.
* `init`: the initial state.
* `s`, `s'`: the start and end states.
* `l`: the label.

Proof: By cases on the label: rules are unchanged, and a method of `M_i` is a method of `m` with
the filter. -/
theorem concretize_step {R I : Type _} [Zero I] {P : TwoLevelPolicy M} {g : Label M → I} {i : I}
    {m : Module R M} {init s s' : m.State} {l : LTSLabel (Label M)} :
    ((P.concretize g i m).oraat init).Step s l s' ↔
      (m.oraat init).Step s l s' ∧ (P.low l ∨ P.idxL g l = i) := by
  cases l with
  | τ =>
      constructor
      · intro h
        exact ⟨Module.oraat_tau_iff.mpr ((Module.oraat_tau_iff (m := P.concretize g i m)).mp h),
          .inl trivial⟩
      · rintro ⟨h, -⟩
        exact (Module.oraat_tau_iff (m := P.concretize g i m)).mpr
          ((Module.oraat_tau_iff (m := m)).mp h)
  | vis e =>
      constructor
      · intro h
        obtain ⟨hm, hk⟩ := (Module.oraat_vis_iff (m := P.concretize g i m)).mp h
        exact ⟨Module.oraat_vis_iff.mpr hm, hk⟩
      · rintro ⟨h, hk⟩
        exact (Module.oraat_vis_iff (m := P.concretize g i m)).mpr
          ⟨(Module.oraat_vis_iff (m := m)).mp h, hk⟩

/-- The projection of the concretization is `⟦M⟧^{P_i}`: `⟦M_i⟧^P = ⟦M⟧^{P_i}`.

Arguments:
* `P`: the policy.
* `g`: the encoding of high inputs used by `idx_P`.
* `i`: the index.
* `m`: the module.
* `init`: the initial state.

Proof: The two sets of transitions are equal by `concretize_step`. -/
theorem semF_concretize {R I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I) (i : I)
    (m : Module R M) (init : m.State) :
    P.semF (P.concretize g i m) init = P.semFAt g i m init := by
  have hT : (P.semF (P.concretize g i m) init).T = (P.semFAt g i m init).T := by
    ext ⟨s, l, s'⟩
    constructor
    · rintro ⟨l₀, hl, h⟩
      obtain ⟨h₁, h₂⟩ := concretize_step.mp h
      exact ⟨l₀, hl, h₁, h₂⟩
    · rintro ⟨l₀, hl, h, hk⟩
      exact ⟨l₀, hl, concretize_step.mpr ⟨h, hk⟩⟩
  exact congrArg (fun T => LTS.mk T init) hT

end TwoLevelPolicy

section Observers
variable {L : Type} [Fintype L] [Preorder L] [DecidableLE L] {M : Type}

/-- `⟦M⟧^{P obs}_ORAAT`: the ORAAT semantics as seen by an observer.

Arguments:
* `R`: the rule names of the module.
* `P`: the multi-level policy.
* `obs`: the level of the observer.
* `m`: the module.
* `init`: the initial state. -/
def observe {R : Type} (P : SecurityPolicy L M) (obs : L) (m : Module R M)
    (init : m.State) : LTS m.State (LTSLabel (Label M)) :=
  (P obs).semF m init

end Observers

/-! ## Functional non-interference -/

/-- Definition 3, functional non-interference: `FNI_P(M) ≜ ∀ i, ⟦M⟧^P_ORAAT ≈ ⟦M⟧^{P_i}_ORAAT`.

Arguments:
* `R`, `M`: the rule names and method names of the module.
* `I`: the type of indices, with `0` as the default index.
* `P`: the policy, which carries the encoding of high inputs.
* `m`: the module.
* `init`: the initial state of both LTSs. -/
noncomputable def FNI {R I M : Type} [Zero I] (P : IndexedPolicy I M)
    (m : Module R M) (init : m.State) : Prop :=
  ∀ i : I, LTS.WeaklyBisimilar (P.semF m init) (P.semFAt P.g i m init)

/-- FNI through concretization: `FNI_P(M)` iff `M` is weakly bisimilar to each of its
concretizations `M_i`, all seen through the policy.

Arguments:
* `P`: the policy.
* `m`: the module.
* `init`: the initial state.

Proof: Rewrite with `semF_concretize` in both directions. -/
theorem FNI_iff_concretize {R I M : Type} [Zero I] (P : IndexedPolicy I M)
    (m : Module R M) (init : m.State) :
    FNI P m init ↔
      ∀ i : I, LTS.WeaklyBisimilar (P.semF m init) (P.semF (P.concretize P.g i m) init) := by
  constructor
  · intro h i
    rw [TwoLevelPolicy.semF_concretize]
    exact h i
  · intro h i
    rw [← TwoLevelPolicy.semF_concretize]
    exact h i

end ReachingStar.Security

namespace ReachingStar.Bluespec

/-! ## Realizable footprints -/

/-- `φ` is a realizable footprint of method `n` in `x`: some state pair fires it.

Arguments:
* `x`: the module.
* `n`: the method.
* `φ`: the footprint. -/
def Module.Real (x : Module R M) (n : M) (φ : Footprint) : Prop :=
  ∃ s s', x.methods n φ s s'

end ReachingStar.Bluespec

/-! ## Non-interference by overwriting high inputs -/

namespace ReachingStar.Security

open ReachingStar.Bluespec

/-- `r` overwrites the high inputs of a label to the values of index `i`, in a well-behaved way:
`r e e'` means that `e` runs as `e'`. The policy cannot see the overwriting, the label that runs
is one `T^{P_i}` keeps, and a real label that `T^{P_i}` keeps runs as itself.

Arguments:
* `P`: the policy.
* `i`: the index.
* `m`: the module.
* `r`: the overwriting, a relation between labels. -/
def Fixes {R I M : Type} [Zero I] (P : IndexedPolicy I M) (i : I)
    (m : Module R M) (r : Label M → Label M → Prop) : Prop :=
  (∀ e e', r e e' → P.projectF (.vis e') = P.projectF (.vis e)) ∧
  (∀ e e', r e e' → P.IsLow e' ∨ P.idx P.g e' = i) ∧
  (∀ e, m.Real e.name e.footprint → (P.IsLow e ∨ P.idx P.g e = i) → r e e)

/-- `m` where a call labelled `e` runs as any `e'` with `r e e'`. The event stays the caller's `e`.

Arguments:
* `r`: the overwriting.
* `m`: the module. -/
def overwrite {R M : Type} (r : Label M → Label M → Prop) (m : Module R M) : Module R M where
  State   := m.State
  rules   := m.rules
  methods := fun n fp s s' => ∃ e', r ⟨n, fp⟩ e' ∧ m.getMethod s e' s'

/-- `NFI_P(M)`: overwriting the high inputs of `M` to the values of any index cannot be told apart
from `M`, once labels are hidden by the policy.

Arguments:
* `P`: the policy.
* `m`: the module.
* `init`: the initial state. -/
def NFI {R I M : Type} [Zero I] (P : IndexedPolicy I M) (m : Module R M)
    (init : m.State) : Prop :=
  ∀ (i : I) (r : Label M → Label M → Prop), Fixes P i m r →
    LTS.WeaklyBisimilar (P.semF m init) (P.semF (overwrite r m) init)

/-- Overwriting the high inputs gives `⟦M⟧^{P_i}`.

Arguments:
* `h`: `r` is a well-behaved overwriting at index `i`.
* `init`: the initial state.

Proof: The two sets of transitions are equal. A call `e` running as `e'` has the label of `e'`
and passes the filter, and a kept label runs as itself. -/
theorem semF_overwrite {R I M : Type} [Zero I] {P : IndexedPolicy I M} {i : I}
    {m : Module R M} {r : Label M → Label M → Prop} (h : Fixes P i m r) (init : m.State) :
    P.semF (overwrite r m) init = P.semFAt P.g i m init := by
  have hT : (P.semF (overwrite r m) init).T = (P.semFAt P.g i m init).T := by
    ext ⟨s, l, s'⟩
    constructor
    · rintro ⟨l₀, hl, hs⟩
      cases l₀ with
      | τ =>
          exact ⟨.τ, hl, (Module.oraat_tau_iff (m := m)).mpr
            ((Module.oraat_tau_iff (m := overwrite r m)).mp hs), .inl trivial⟩
      | vis e =>
          obtain ⟨e', hr, hm⟩ := (Module.oraat_vis_iff (m := overwrite r m)).mp hs
          exact ⟨.vis e', (h.1 _ _ hr).trans hl, (Module.oraat_vis_iff (m := m)).mpr hm,
            h.2.1 _ _ hr⟩
    · rintro ⟨l₀, hl, hs, hk⟩
      cases l₀ with
      | τ =>
          exact ⟨.τ, hl, (Module.oraat_tau_iff (m := overwrite r m)).mpr
            ((Module.oraat_tau_iff (m := m)).mp hs)⟩
      | vis e =>
          have hm := (Module.oraat_vis_iff (m := m)).mp hs
          exact ⟨.vis e, hl, (Module.oraat_vis_iff (m := overwrite r m)).mpr
            ⟨e, h.2.2 e ⟨s, s', hm⟩ hk, hm⟩⟩
  exact congrArg (fun T => LTS.mk T init) hT

/-- FNI and NFI are equivalent when every index has a well-behaved overwriting.

Arguments:
* `P`: the policy.
* `m`: the module.
* `init`: the initial state.
* `hr`: every index `i` has an overwriting.

Proof: By `semF_overwrite`, the LTS of an overwriting at `i` is `⟦M⟧^{P_i}`. -/
theorem FNI_iff_NFI {R I M : Type} [Zero I] (P : IndexedPolicy I M)
    (m : Module R M) (init : m.State) (hr : ∀ i, ∃ r, Fixes P i m r) :
    FNI P m init ↔ NFI P m init := by
  constructor
  · intro h i r hf
    rw [semF_overwrite hf]
    exact h i
  · intro h i
    obtain ⟨r, hf⟩ := hr i
    rw [← semF_overwrite hf]
    exact h i r hf

end ReachingStar.Security
