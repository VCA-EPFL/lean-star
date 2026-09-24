import StarExperimental.MI

/-!
# Altre proprietà di `MI` dimostrate con `new_backward_tatic`

La tattica generica è in `BackwardGen.lean`; la sua istanza per `MI` (vista, invariante,
viste cattive, `badView_unreachable_from_default`) è in `MI.lean`, dove dimostra i lemmi
di commutazione. Qui, dalla stessa ricerca, seguono `twoCachesM_unreachable` (due cache
distinte in `M`) e `two_rsIμ_unreachable` (due `rsIμ` in volo su indici distinti).
-/

open THEORY
open Relation
open BackwardGen MIView

namespace MIDirect

/-! ### Due cache in `M` -/

/-- La stessa definizione che era in MI.lean: due cache distinte entrambe in `M`. -/
def twoCachesM {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ (s.caches i).state = Bstate.M ∧ (s.caches j).state = Bstate.M

theorem twoCachesM_unreachable {n} : ∀ s : MIState n, twoCachesM s → ¬ MI.reachable s := by
  intro s ⟨i, j, hij, hi, hj⟩
  exact badView_unreachable s ⟨i, j, Or.inl ⟨decide_eq_false hij, hi, hj⟩⟩

#print axioms twoCachesM_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

/-! ### Due `rsIμ` in volo -/

/-- Due indici distinti hanno entrambi un `rsIμ` in volo verso il parent. -/
def two_rsIμ' {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ (∃ (k : Nat) (v : Value), (s.parent.queue_cip i)[k]? = some (CPEvent.rsIμ v))
               ∧ (∃ (k : Nat) (v : Value), (s.parent.queue_cip j)[k]? = some (CPEvent.rsIμ v))

theorem two_rsIμ'_unreachable {n} : ∀ s : MIState n, two_rsIμ' s → ¬ MI.reachable s := by
  intro s ⟨i, j, hij, ⟨k, v, hk⟩, ⟨k', v', hk'⟩⟩
  refine badView_unreachable s ⟨i, j, Or.inr (Or.inl ⟨decide_eq_false hij, ?_, ?_⟩)⟩
  · show Cnt.ofCount (parentMsgs s.parent i) ≠ .zero
    rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hk
  · show Cnt.ofCount (parentMsgs s.parent j) ≠ .zero
    rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hk'

/-- La definizione com'è stata scritta (con `∀ k v`): è falsa su ogni stato, perché per
`k = length` la coda dà `none`; quindi il teorema segue da quello per `two_rsIμ'`
prendendo `k = 0`. -/
def two_rsIμ {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ (∀ (k : Nat) (v : Value), ((s.parent).queue_cip i)[k]? = some (CPEvent.rsIμ v))
               ∧ (∀ (k : Nat) (v : Value), ((s.parent).queue_cip j)[k]? = some (CPEvent.rsIμ v))

theorem two_rsIμ_unreachable {n} : ∀ s : MIState n, two_rsIμ s → ¬ MI.reachable s := by
  intro s ⟨i, j, hij, hi, hj⟩
  exact two_rsIμ'_unreachable s ⟨i, j, hij, ⟨0, 0, hi 0 0⟩, ⟨0, 0, hj 0 0⟩⟩

#print axioms two_rsIμ_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end MIDirect
