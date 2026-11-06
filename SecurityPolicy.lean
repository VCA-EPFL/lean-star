import Star.Bluespec.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

namespace ReachingStar.Bluespec

/-! ## Labels -/

/-- A label `t = (id, σ) ∈ 𝓛 = 𝓘𝓓 × 𝓕`: an identifier and a footprint. It is Star's `Event`, with
`id = t.name` and `σ = t.footprint`. `τ` is not a label: the labels of an LTS are
`LTSLabel (Label ID)`.

Arguments:
* `ID`: the identifiers `𝓘𝓓`. -/
abbrev Label (ID : Type _) := Event ID

/-- The identity `𝓛 = 𝓘𝓓 × 𝓕`: a label is exactly a pair `(id, σ)`.

Arguments:
* `ID`: the identifiers `𝓘𝓓`.

Proof: Both round trips hold by definition. -/
def Label.equivProd (ID : Type _) : Label ID ≃ ID × Footprint where
  toFun t := (t.name, t.footprint)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ReachingStar.Bluespec

namespace ReachingStar.Security

open ReachingStar.Bluespec

/-! ## Levels of an event -/

/-- The levels of one event `(arg₁, …, argₙ, ret)`: a level per argument of the footprint, for any
arity, and a level for the return value.

Arguments:
* `L`: the type of security levels.
* `fp`: the footprint being classified. -/
structure EventLevels (L : Type) (fp : Footprint) where
  /-- The level of each argument, indexed by the argument positions `fp.α`. -/
  args : fp.α → L
  /-- The level of the return value. -/
  ret  : L

open Classical in
/-- The levels of a footprint, given by position in `fp.l`.

Arguments:
* `L`: the type of security levels.
* `fp`: the footprint whose arguments get levels.
* `levels`: the level of the `k`-th argument of `fp.l` is `levels[k]`.
* `dflt`: the level of an argument with no entry in `levels`.
* `ret`: the level of the return value. -/
noncomputable def EventLevels.ofList {L : Type} (fp : Footprint)
    (levels : List L) (dflt ret : L) : EventLevels L fp where
  args := fun a => levels.getD (fp.l.idxOf a) dflt
  ret  := ret

/-- The first element of a two-element list sits at position `0`.

Arguments:
* `a`, `b`: the elements of the list.

Proof: By the definition of `idxOf` on a cons. -/
private theorem idxOf_pair_fst {α : Type _} [DecidableEq α] (a b : α) : [a, b].idxOf a = 0 :=
  List.idxOf_cons_self

/-- The second element of a two-element list with distinct elements sits at position `1`.

Arguments:
* `a`, `b`: the elements of the list.
* `h`: the two elements differ.

Proof: The first comparison fails because `a ≠ b`, and the search then stops on `b`. -/
private theorem idxOf_pair_snd {α : Type _} [DecidableEq α] (a b : α) (h : a ≠ b) :
    [a, b].idxOf b = 1 := by
  rw [List.idxOf_cons]
  have hab : (a == b) = false := by simp [h]
  rw [hab]
  show List.idxOf b [b] + 1 = 1
  rw [List.idxOf_cons_self]

/-- `ofList` on a two-argument footprint gives the first argument the first level.

Arguments:
* `a1`, `a2`, `v`: the arguments and return value of the footprint.
* `x`, `y`: the levels of the two arguments.
* `d`, `r`: the default level and the return level.

Proof: The position of the first argument is `0` by `idxOf_pair_fst`. -/
theorem EventLevels.ofList_arg2_fst {L A1 A2 V : Type} (a1 : A1) (a2 : A2) (v : V)
    (x y d r : L) :
    (EventLevels.ofList (Footprint.arg2 a1 a2 v) [x, y] d r).args (0 : Fin 2) = x := by
  show [x, y].getD (@List.idxOf (Fin 2)
    (@instBEqOfDecidableEq _ fun a b => Classical.propDecidable (a = b)) 0 [0, 1]) d = x
  rw [@idxOf_pair_fst (Fin 2) (fun a b => Classical.propDecidable (a = b))]
  rfl

/-- `ofList` on a two-argument footprint gives the second argument the second level.

Arguments:
* `a1`, `a2`, `v`: the arguments and return value of the footprint.
* `x`, `y`: the levels of the two arguments.
* `d`, `r`: the default level and the return level.

Proof: The position of the second argument is `1` by `idxOf_pair_snd`. -/
theorem EventLevels.ofList_arg2_snd {L A1 A2 V : Type} (a1 : A1) (a2 : A2) (v : V)
    (x y d r : L) :
    (EventLevels.ofList (Footprint.arg2 a1 a2 v) [x, y] d r).args (1 : Fin 2) = y := by
  show [x, y].getD (@List.idxOf (Fin 2)
    (@instBEqOfDecidableEq _ fun a b => Classical.propDecidable (a = b)) 1 [0, 1]) d = y
  rw [@idxOf_pair_snd (Fin 2) (fun a b => Classical.propDecidable (a = b)) 0 1 (by decide)]
  rfl

/-- The two security levels `SL = {low, high}`. -/
inductive TwoLevel where
  /-- Public, observable. -/
  | low
  /-- Secret. -/
  | high
  deriving DecidableEq, Repr, Fintype

/-- The order on levels: `low ≤ high`.

Arguments:
* the two arguments: the levels being compared. -/
def TwoLevel.le : TwoLevel → TwoLevel → Prop
  | .low,  _     => True
  | .high, .high => True
  | .high, .low  => False

/-- `≤` on levels is `TwoLevel.le`. -/
instance : LE TwoLevel := ⟨TwoLevel.le⟩

/-- `a ≤ b` is decidable.

Arguments:
* the two arguments: the levels `a` and `b`.

Proof: By cases on the two levels. -/
instance : DecidableLE TwoLevel
  | .low,  _     => isTrue trivial
  | .high, .high => isTrue trivial
  | .high, .low  => isFalse id

/-- `low ≤ high` is a preorder.

Proof: By cases on the levels. -/
instance : Preorder TwoLevel where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le, TwoLevel.le]

/-- Swaps `low` and `high`.

Arguments:
* the argument: the level to swap. -/
def TwoLevel.flip : TwoLevel → TwoLevel
  | .low  => .high
  | .high => .low

/-- Masks a value: a `high` value becomes `none` (the paper's `()`), a `low` value `x` becomes
`some x`. The type does not depend on the level.

Arguments:
* `level`: the level of `x`.
* `α`: the type of `x`.
* `x`: the value to mask. -/
def maskOpt (level : TwoLevel) {α : Type} (x : α) : Option α :=
  if level = .low then some x else none

/-- Masking a `low` value keeps it.

Arguments:
* `x`: the value.

Proof: By definition. -/
@[simp] theorem maskOpt_low {α : Type} (x : α) : maskOpt .low x = some x := rfl

/-- Masking a `high` value hides it.

Arguments:
* `x`: the value.

Proof: By definition. -/
@[simp] theorem maskOpt_high {α : Type} (x : α) : maskOpt .high x = none := rfl

/-- Masks every `high` argument and a `high` return value of a footprint. Positions are preserved.

Arguments:
* `fp`: the footprint to mask.
* `args`: the level of each argument of `fp`.
* `ret`: the level of the return value of `fp`. -/
def maskFootprint (fp : Footprint) (args : fp.α → TwoLevel) (ret : TwoLevel) : Footprint where
  V    := Option fp.V
  α    := fp.α
  f    := fun i => Option (fp.f i)
  l    := fp.l
  args := fp.args.map (B := fun i => Option (fp.f i)) (fun i x => maskOpt (args i) x)
  ret  := maskOpt ret fp.ret

/-! ## LTS labels -/

/-- The labels of an LTS: a visible label `e` or the internal label `τ`.

Arguments:
* `E`: the type of visible labels. -/
inductive LTSLabel (E : Type _) where
  /-- A visible label.

  Arguments:
  * `e`: the label. -/
  | vis (e : E)
  /-- The internal label. -/
  | τ

/-! ## Two-level policies -/

/-- A two-level security policy `P`: a label is either `H`, a high transition, or `(arg_l, ret_l)`,
a low transition with a level per argument and a level for the return value.

Arguments:
* `M`: the method names. -/
structure TwoLevelPolicy (M : Type) where
  /-- The classification of a label: `none` for `H`, `some lv` for a low transition.

  Arguments:
  * `e`: the label. -/
  levels : (e : Label M) → Option (EventLevels TwoLevel e.footprint)

/-- `P e` stands for `P.levels e`.

Arguments:
* `M`: the method names. -/
instance {M : Type} :
    CoeFun (TwoLevelPolicy M)
      (fun _ => (e : Label M) → Option (EventLevels TwoLevel e.footprint)) :=
  ⟨TwoLevelPolicy.levels⟩

namespace TwoLevelPolicy

variable {M : Type}

/-- `↓F_P`: a high transition becomes `τ`, and a low transition has its high arguments and high
return value masked.

Arguments:
* `P`: the policy.
* the result: maps a label to its projection. -/
def projectF (P : TwoLevelPolicy M) : LTSLabel (Label M) → LTSLabel (Label M)
  | .τ     => .τ
  | .vis e =>
      match P e with
      | none    => .τ
      | some lv => .vis ⟨e.name, maskFootprint e.footprint lv.args lv.ret⟩

/-- `↓T_P`: as `↓F_P`, but the return value is removed from every label.

Arguments:
* `P`: the policy.
* the result: maps a label to its projection. -/
def projectT (P : TwoLevelPolicy M) : LTSLabel (Label M) → LTSLabel (Label M)
  | .τ     => .τ
  | .vis e =>
      match P e with
      | none    => .τ
      | some lv => .vis ⟨e.name, maskFootprint e.footprint lv.args .high⟩

/-- `↓F_P` keeps `τ` as `τ`.

Arguments:
* `P`: the policy.

Proof: By definition. -/
@[simp] theorem projectF_tau (P : TwoLevelPolicy M) : P.projectF .τ = .τ := rfl

/-- `↓T_P` keeps `τ` as `τ`.

Arguments:
* `P`: the policy.

Proof: By definition. -/
@[simp] theorem projectT_tau (P : TwoLevelPolicy M) : P.projectT .τ = .τ := rfl

/-- `low_P(l)`: `l` is a low transition whose arguments and return value are all `low`.

Arguments:
* `P`: the policy.
* `e`: the label `l`. -/
def IsLow (P : TwoLevelPolicy M) (e : Label M) : Prop :=
  ∃ lv, P e = some lv ∧ (∀ a, lv.args a = .low) ∧ lv.ret = .low

/-- The level of an argument of a label. Every argument of a high transition is `high`.

Arguments:
* `P`: the policy.
* `e`: the label.
* `a`: an argument position of `e`. -/
def argLevel (P : TwoLevelPolicy M) (e : Label M) (a : e.footprint.α) : TwoLevel :=
  match P e with
  | none    => .high
  | some lv => lv.args a

/-- `l` carries at least one high input.

Arguments:
* `P`: the policy.
* `e`: the label `l`. -/
def HasHighInput (P : TwoLevelPolicy M) (e : Label M) : Prop :=
  ∃ a, P.argLevel e a = .high

/-- The high inputs of a label: its low arguments and return value are replaced by `()`.

Arguments:
* `P`: the policy.
* `e`: the label. -/
def highInputs (P : TwoLevelPolicy M) (e : Label M) : Label M :=
  ⟨e.name, maskFootprint e.footprint (fun a => (P.argLevel e a).flip) .high⟩

open Classical in
/-- `idx_P`: the index of the combination of high inputs of `l`, or the default `0` when `l` has no
high input. It only depends on the high inputs of `l`.

Arguments:
* `I`: the type of indices, with `0` as the default index.
* `P`: the policy.
* `g`: the encoding of a combination of high inputs as an index.
* `e`: the label `l`. -/
noncomputable def idx {I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I)
    (e : Label M) : I :=
  if P.HasHighInput e then g (P.highInputs e) else 0

/-- A label without high input has index `0`.

Arguments:
* `P`: the policy.
* `g`: the encoding of high inputs.
* `h`: `e` has no high input.

Proof: By the definition of `idx`. -/
theorem idx_of_not_hasHighInput {I : Type _} [Zero I] (P : TwoLevelPolicy M)
    (g : Label M → I) {e : Label M} (h : ¬ P.HasHighInput e) : P.idx g e = 0 := by
  simp [idx, h]

/-- A label with a high input has index `g` of its high inputs.

Arguments:
* `P`: the policy.
* `g`: the encoding of high inputs.
* `h`: `e` has a high input.

Proof: By the definition of `idx`. -/
theorem idx_of_hasHighInput {I : Type _} [Zero I] (P : TwoLevelPolicy M)
    (g : Label M → I) {e : Label M} (h : P.HasHighInput e) :
    P.idx g e = g (P.highInputs e) := by
  simp [idx, h]

/-- `low_P` on the labels of an LTS: `IsLow` on a visible label, and always true on `τ`, which
carries no high data.

Arguments:
* `P`: the policy.
* the argument: the label. -/
def low (P : TwoLevelPolicy M) : LTSLabel (Label M) → Prop
  | .vis e => P.IsLow e
  | .τ     => True

/-- `idx_P` on the labels of an LTS: `τ` has no high input, so it has the default index `0`.

Arguments:
* `I`: the type of indices, with `0` as the default index.
* `P`: the policy.
* `g`: the encoding of high inputs.
* the argument: the label. -/
noncomputable def idxL {I : Type _} [Zero I] (P : TwoLevelPolicy M) (g : Label M → I) :
    LTSLabel (Label M) → I
  | .vis e => P.idx g e
  | .τ     => 0

end TwoLevelPolicy

/-- A two-level policy with its encoding of high inputs, so that `idx_P` is determined by `P`.

Arguments:
* `I`: the type of indices.
* `M`: the method names. -/
structure IndexedPolicy (I M : Type) extends TwoLevelPolicy M where
  /-- The encoding of a combination of high inputs (a `highInputs` label) as an index. -/
  g : Label M → I

/-! ## Multi-level policies and observers -/

/-- A security policy over any finite set of levels: `none` for a high transition, `some lv` for a
low one with a level per argument and for the return value.

Arguments:
* `L`: the security levels.
* `M`: the method names. -/
structure SecurityPolicy (L : Type) [Fintype L] (M : Type) where
  /-- The classification of a label: `none` for `H`, `some lv` for a low transition.

  Arguments:
  * `e`: the label. -/
  levels : (e : Label M) → Option (EventLevels L e.footprint)

section Observers
variable {L : Type} [Fintype L] [Preorder L] [DecidableLE L] {M : Type}

/-- What an observer sees of a value: it sees the value iff its level is `≤ obs`.

Arguments:
* `obs`: the level of the observer.
* `l`: the level of the value. -/
def lower (obs l : L) : TwoLevel := if l ≤ obs then .low else .high

/-- An observer at `obs` sees a value of level `l` iff `l ≤ obs`.

Arguments:
* `obs`: the level of the observer.
* `l`: the level of the value.

Proof: By cases on `l ≤ obs`. -/
theorem lower_eq_low {obs l : L} : lower obs l = .low ↔ l ≤ obs := by
  unfold lower; split_ifs with h <;> simp [h]

/-- A stronger observer sees at least as much.

Arguments:
* `obs`, `obs'`: the two observers.
* `l`: the level of the value.
* `h`: `obs ≤ obs'`.

Proof: By transitivity of `≤`. -/
theorem lower_mono {obs obs' l : L} (h : obs ≤ obs') :
    lower obs l = .low → lower obs' l = .low := by
  rw [lower_eq_low, lower_eq_low]; exact fun hl => le_trans hl h

/-- The two-level policy that `P` induces for an observer: levels `≤ obs` become `low`, all others
`high`, and high transitions stay high.

Arguments:
* `P`: the multi-level policy.
* `obs`: the level of the observer. -/
def SecurityPolicy.view (P : SecurityPolicy L M) (obs : L) : TwoLevelPolicy M :=
  ⟨fun e => (P.levels e).map fun lv =>
    { args := fun i => lower obs (lv.args i)
      ret  := lower obs lv.ret }⟩

/-- `P obs` is the two-level policy of the observer `obs`. -/
instance : CoeFun (SecurityPolicy L M) (fun _ => L → TwoLevelPolicy M) :=
  ⟨SecurityPolicy.view⟩

/-- For two levels, the `low` observer sees exactly the levels of the policy.

Arguments:
* `l`: the level.

Proof: By cases on `l`. -/
theorem lower_low (l : TwoLevel) : lower .low l = l := by
  cases l <;> rfl

/-- The `high` observer sees everything.

Arguments:
* `l`: the level.

Proof: By cases on `l`. -/
theorem lower_high (l : TwoLevel) : lower .high l = .low := by
  cases l <;> rfl

end Observers

end ReachingStar.Security
