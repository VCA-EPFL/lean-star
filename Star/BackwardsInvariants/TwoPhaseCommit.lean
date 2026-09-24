import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation

namespace THEORY

structure LTS (T : Type) where
  S : Type
  transitions : T → S → S → Prop
  init : S → Prop
  flushed : S → Prop

def LTS.atrans {T} (l : LTS T) : l.S → l.S → Prop := fun s s' =>
  ∃ t, l.transitions t s s'

def LTS.reachable {T} (l : LTS T) : l.S → Prop := fun s =>
  ∀ s_init, l.init s_init → ReflTransGen l.atrans s_init s

def LTS.backwards_reachable_from {T} (l : LTS T) (s s' : l.S) :=
  ReflTransGen (Function.swap l.atrans) s s'

inductive LTS.φ {T} (l : LTS T) : l.S → Prop where
| flushed {s} : l.flushed s → l.φ s
| back_step {s s'} : l.atrans s s' → l.φ s' → l.φ s

def get {T} (l : LTS T) (s_init s) :=
  l.backwards_reachable_from s_init s
  ∨ (∃ (P : l.S → Prop), P s ∧ (∀ s', P s' → l.backwards_reachable_from s_init s'))

theorem backwards_reachable_not_init {T} {l : LTS T} {s} :
  (∀ s_init, l.init s_init → l.backwards_reachable_from s s_init) ↔ l.reachable s := by
  grind [LTS.reachable, LTS.backwards_reachable_from, Relation.reflTransGen_swap]

theorem backwards_reachable_φ {T} {l : LTS T} {s} :
  l.φ s → ∃ s_init, l.flushed s_init ∧ l.backwards_reachable_from s_init s := by
  intro h; induction h <;> grind [LTS.backwards_reachable_from]

theorem φ_backwards_reachable {T} {l : LTS T} {s} :
  ∀ s_init, l.flushed s_init → l.backwards_reachable_from s_init s → l.φ s := by
  dsimp [LTS.backwards_reachable_from]; intro s_init hinit htrans
  induction htrans
  · apply LTS.φ.flushed; assumption
  · apply LTS.φ.back_step; assumption; assumption

theorem φ_backwards_reachable_iff {T} {l : LTS T} {s} :
  l.φ s ↔ (∃ s_init, l.flushed s_init ∧ l.backwards_reachable_from s_init s) := by
  grind [backwards_reachable_φ, φ_backwards_reachable]



namespace TEST

def test : LTS (Fin 3) where
  S := Nat
  init s := s = 0
  flushed s := s = 0
  transitions := fun n =>
    match n with
    | 0 => fun s s' => s < 10 ∧ s' = 20
    | 1 => fun s s' => s >= 10 ∧ s' = s
    | 2 => fun s s' => s' = 0

theorem reachable : test.reachable (20:Nat) := by
  dsimp [test, LTS.reachable]
  intro s init; subst_vars
  trans
  · apply ReflTransGen.single; exists 0
  · apply ReflTransGen.single; exists 1

theorem back_reachable {x} : test.backwards_reachable_from (30:Nat) x → x = (30:Nat) := by
  dsimp [LTS.backwards_reachable_from]
  intro h
  generalize h30 : 30 = x30 at h
  induction h using ReflTransGen.head_induction_on with
  | refl => grind
  | @head a b h1 h2 h3 =>
    subst_vars
    dsimp [Function.swap, test, LTS.atrans] at h1
    obtain ⟨t, ht⟩ := h1
    fin_cases t <;> grind

theorem back_reachable4 : ¬ test.reachable (30:Nat) := by
  intro hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach (0:Nat) rfl
  rw [Relation.reflTransGen_swap] at hreach
  have h' := back_reachable hreach
  grind

theorem back_reachable2 : test.backwards_reachable_from (20:Nat) (5:Nat) := by
  dsimp [test, LTS.backwards_reachable_from]
  · apply ReflTransGen.single; exists 0

theorem back_reachable3 : test.backwards_reachable_from (20:Nat) (0:Nat) := by
  dsimp [test, LTS.backwards_reachable_from]
  · apply ReflTransGen.single; exists 0

end TEST


namespace TwoPhaseCommit

structure Coordinator where

inductive PState where
| empty
| tentative (b : Bool)
| committed (b : Bool)
| aborted

def PState.commit : PState → PState
| .tentative b => .committed b
| e => e

def PState.abort (_ : PState): PState := .aborted

def PState.consistentWith (b : Bool) : PState → Bool
| .empty => true
| .tentative b' => b == b'
| .committed b' => b == b'
| .aborted => true


structure State where
  p12c : Option Bool
  p22c : Option Bool
  p1 : PState
  p2 : PState

inductive Rule where
| pinit1
| pinit2
| part1
| part2
| commit
| abort

inductive Protocol : Rule → State → State → Prop where
| step_pinit1 {s : State} {b : Bool} : s.p12c.isNone → s.p1 = .empty → Protocol .pinit1 s {s with p1 := .tentative b}
| step_pinit2 {s : State} {b : Bool} : s.p22c.isNone → s.p2 = .empty → Protocol .pinit2 s {s with p2 := .tentative b}
| step_part1 {s : State} {b : Bool} : s.p1 = .tentative b → Protocol .part1 s {s with p12c := .some b}
| step_part2 {s : State} {b : Bool} : s.p2 = .tentative b → Protocol .part2 s {s with p22c := .some b}
| step_commit {s : State} : s.p12c.isSome → s.p12c = s.p22c → Protocol .commit s {p1 := s.p1.commit, p2 := s.p2.commit, p12c := .none, p22c := .none}
--| step_abort {s : State} : s.p12c.isSome → s.p12c.isSome → s.p12c ≠ s.p22c → Protocol .abort s {s with p1 := s.p1.abort, p2 := s.p2.abort, p12c := .none, p22c := .none}


inductive φ : State → Prop where
| base_commit {b : Bool}:
  φ {p1 := .committed b, p2 := .committed b, p12c := .none, p22c := .none}
| base_abort {b : Bool}:
  φ {p1 := .aborted, p2 := .aborted, p12c := .none, p22c := .none}
| step {s s' : State} {r : Rule}:
  φ s' → Protocol r s s' → φ s


def init : State → Prop :=
  fun s => s.p1 = .empty ∧ s.p2 = .empty ∧ s.p12c.isNone ∧ s.p22c.isNone



def init_state : State  := {
  p1 := .empty
  p2 := .empty
  p12c := none
  p22c := none
}



-- Define LTS for the two-phase commit protocol
def twoPC : LTS Rule where
  S := State
  transitions := Protocol
  init s := init s
  flushed s := φ s

def unreachable_set (s : State) : Prop :=
  ∃ b, (s.p1 = .tentative b ∧ s.p12c = some (!b)) ∨ (s.p2 = .tentative b ∧ s.p22c = some (!b))


theorem back_reachable_twoPC {x} : ∀ s, unreachable_set s -> twoPC.backwards_reachable_from s x → unreachable_set x := by
  dsimp [LTS.backwards_reachable_from]
  intro s hu h
  induction h using ReflTransGen.head_induction_on with
  | refl => grind
  | @head a c h1 h2 h3 =>
    clear h2
    dsimp [Function.swap, twoPC, LTS.atrans] at h1
    obtain ⟨t, ht⟩ := h1
    apply h3
    cases t
    . cases ht
      simp_all
      unfold unreachable_set at hu
      cases hu; rename_i H
      cases H
      . simp_all
      . unfold unreachable_set at *
        simp_all
    . cases ht
      simp_all
      unfold unreachable_set at hu
      cases hu; rename_i H
      cases H
      . unfold unreachable_set at *
        simp_all
      . simp_all
    . cases ht
      simp_all
      unfold unreachable_set at hu
      cases hu; rename_i H
      cases H
      . grind
      . --apply h3
        unfold unreachable_set at *
        simp_all
    . cases ht
      simp_all
      unfold unreachable_set at hu
      cases hu; rename_i H
      cases H
      . --apply h3
        unfold unreachable_set at *
        simp_all
      . grind
    . cases ht
      simp_all
      unfold unreachable_set at hu
      cases hu; rename_i H
      cases H
      . grind
      . --apply h3
        unfold unreachable_set at *
        simp_all
    . cases ht


theorem reachable_twoPC : ∀ s, unreachable_set s -> ¬ twoPC.reachable s := by
  intro s h hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach _
  . exact init_state
  . specialize hreach (by unfold init_state; constructor; simp_all; grind)
    rw [Relation.reflTransGen_swap] at hreach
    have h' := back_reachable_twoPC _ h hreach
    unfold unreachable_set at *
    unfold init_state at *
    simp_all

def test_state : State  := {
  p1 := .tentative true
  p2 := .empty
  p12c := false
  p22c := none
}

def test_state1 : State  := {
  p1 := .tentative false
  p2 := .empty
  p12c := true
  p22c := none
}

def test_state2 : State  := {
  p1 := .empty
  p2 := .tentative false
  p12c := none
  p22c := true
}

def test_state3 : State  := {
  p1 := .empty
  p2 := .tentative true
  p12c := none
  p22c := false
}

def test_state4 : State  := {
  p1 := .empty
  p2 := .tentative true
  p12c := none
  p22c := true
}



theorem reachable_twoPC_test : ¬ twoPC.reachable test_state := by
  intro hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach _
  . exact init_state
  . specialize hreach (by unfold init_state; constructor; simp_all; grind)
    rw [Relation.reflTransGen_swap] at hreach
    have h' := back_reachable_twoPC _ (by unfold unreachable_set; unfold test_state; simp_all) hreach
    unfold unreachable_set at *
    unfold init_state at *
    simp_all

theorem reachable_twoPC_test1 : ¬ twoPC.reachable test_state1 := by
  intro hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach _
  . exact init_state
  . specialize hreach (by unfold init_state; constructor; simp_all; grind)
    rw [Relation.reflTransGen_swap] at hreach
    have h' := back_reachable_twoPC _ (by unfold unreachable_set; unfold test_state1; simp_all) hreach
    unfold unreachable_set at *
    unfold init_state at *
    simp_all

theorem reachable_twoPC_test2 : ¬ twoPC.reachable test_state2 := by
  intro hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach _
  . exact init_state
  . specialize hreach (by unfold init_state; constructor; simp_all; grind)
    rw [Relation.reflTransGen_swap] at hreach
    have h' := back_reachable_twoPC _ (by unfold unreachable_set; unfold test_state2; simp_all) hreach
    unfold unreachable_set at *
    unfold init_state at *
    simp_all

theorem reachable_twoPC_test3 : ¬ twoPC.reachable test_state3 := by
  intro hreach
  dsimp [LTS.reachable] at hreach
  specialize hreach _
  . exact init_state
  . specialize hreach (by unfold init_state; constructor; simp_all; grind)
    rw [Relation.reflTransGen_swap] at hreach
    have h' := back_reachable_twoPC _ (by unfold unreachable_set; unfold test_state3; simp_all) hreach
    unfold unreachable_set at *
    unfold init_state at *
    simp_all


-- theorem reachable_twoPC_test4 : ¬ twoPC.reachable test_state4 := by
--   intro hreach
--   dsimp [LTS.reachable] at hreach
--   specialize hreach _
--   . exact init_state
--   . specialize hreach (by unfold init_state; constructor; simp_all; grind)
--     rw [Relation.reflTransGen_swap] at hreach
--     have h' := back_reachable_twoPC _ (by unfold unreachable_set; unfold test_state4; simp_all) hreach
--     unfold unreachable_set at *
--     unfold init_state at *
--     simp_all


theorem comm_pinit1_pinit2 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .pinit2 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .pinit2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hn₁ hp₁ =>
    cases h₂ with
    | step_pinit2 hn₂ hp₂ =>
      refine ⟨_, Protocol.step_pinit1 ?_ ?_, Protocol.step_pinit2 ?_ ?_⟩ <;> assumption

theorem comm_pinit1_part1 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hn hp =>
    cases h₂ with
    | step_part1 hp' => simp_all

theorem comm_pinit1_part2 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hn₁ hp₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_pinit1 ?_ ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_pinit2_part1 {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit2 hn₁ hp₁ =>
    cases h₂ with
    | step_part1 hs₂ =>
      refine ⟨_, Protocol.step_pinit2 ?_ ?_, Protocol.step_part1 ?_⟩ <;> assumption

theorem comm_pinit2_part2 {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit2 hn hp =>
    cases h₂ with
    | step_part2 hp' => simp_all

theorem comm_part1_part2 {s s' s''} :
  Protocol .part1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .part1 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_part1 hs₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_part1 ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_pinit1_commit {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .commit s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hn hp =>
    cases h₂ with
    | step_commit hs heq => simp_all

theorem comm_pinit2_commit {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .commit s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit2 hn hp =>
    cases h₂ with
    | step_commit hs heq => simp_all


theorem part1_det {s s' s''} :
  Protocol .part1 s s' →
  Protocol .part1 s s'' →
  s' = s'' := by
  intro h1 h2;
  cases h1 ; cases h2 ; grind


--back_reachable_twoPC {x} : ∀ s, unreachable_set s -> twoPC.backwards_reachable_from s x → unreachable_set x := by
theorem comm_part1_commit {s s' s''} (hphi : φ s) :
  ¬ unreachable_set s →
  twoPC.transitions .part1 s s' →
  twoPC.transitions .commit s s'' →
  twoPC.transitions .commit s' s'' := by
  intro h1 h2 h3
  cases h3; simp_all
  unfold unreachable_set at *
  by_cases s.p22c.isSome
  . by_cases s.p22c = true
    . simp_all
      cases h2
      constructor <;> simp_all
    . have h : s.p22c = false := by admit
      simp_all
      cases h2
      constructor <;> simp_all
  . grind





-- theorem part1_twice {s s'} :
--   Protocol .part1 s s' →
--   Protocol .part1 s' s' := by sorry

-- theorem comm_part1_commit' {s b} (hphi : φ s) :
--   s.p12c = .some b ∧ s.p1.consistentWith b := by
--   induction hphi generalizing b with
--   | base_commit => sorry
--   | base_abort => sorry
--   | @step s_p s'_p r hphi' hprot ih =>
--     cases r with
--     | pinit1 =>
--       cases hprot; grind
--     | pinit2 =>
--       cases hprot; grind
--     | part2 =>
--       cases hprot; grind
--     | part1 =>
--       cases hprot; specialize @ih b
--       dsimp [PState.consistentWith] at *
--       rename_i a
--       rw [a] at ih ⊢; dsimp at *

--     | commit =>
--       cases hprot; specialize @ih true; grind
--     | abort =>
--       cases hprot; specialize @ih true; grind

-- theorem comm_part1_commit {s s' s''} (hphi : φ s) :
--   Protocol .part1 s s' →
--   Protocol .commit s s'' →
--   Protocol .commit s' s'' := by
--   induction hphi generalizing s' s'' with
--   | base_commit => sorry
--   | base_abort => sorry
--   | @step s_p s'_p r hphi' hprot ih =>
--     intro htrans1 htrans2
--     cases r with
--     | pinit1 =>
--       obtain ⟨s_pinit_comm, h_pinit, h_comm⟩ := comm_pinit1_commit ‹_› ‹_›
--       obtain ⟨s_pinit_part1, h_pinit2, h_part1⟩ := comm_pinit1_part1 hprot ‹_›
--       have : Protocol Rule.commit s_pinit_part1 s_pinit_comm := by grind
--       sorry
--     | pinit2 =>
--       sorry
--     | part2 =>
--       sorry
--     | part1 =>
--       have : s'_p = s' := by grind [part1_det]
--       subst_vars
--       apply ih; grind [part1_twice]
--       skip
--     | commit => sorry
--     | abort => sorry

-- theorem comm_part2_commit {s s' s''} :
--   Protocol .part2 s s' →
--   Protocol .commit s s'' →
--   ∃ s''', Protocol .part2 s'' s''' ∧ Protocol .commit s' s''' := by
--   -- Commit makes p2 committed, disabling the part2 step on that branch.
--   sorry

-- --miss all the abort cases right?

end TwoPhaseCommit
end THEORY
