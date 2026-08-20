-- Scratch experiment: does `PipeInv` hold *backwards*, i.e.
-- `PipeInv i' → step i i' → PipeInv i`? (companion to
-- `scratch_sbinv_backward.lean`, which answered "yes" for `SbInv`.)
--
-- Answer: NO, not in general -- unlike `SbInv` (an affine, invertible
-- counting invariant), `PipeInv`'s two conjuncts are *conditional* on
-- `hasElement` flags that the rules themselves clear. Clearing a flag
-- destroys the ability to observe a violation, so a rule can turn an
-- invalid pre-state into a (vacuously) valid post-state:
--
-- * `rule_RL_fetch`: backward HOLDS. Its guard (`fifo_RDY_enq f2d_hasElement`)
--   forces `i.f2d_hasElement = false`, which makes the second conjunct (K)
--   vacuous in `i` regardless of `i'`; the first conjunct (J) only mentions
--   `d2e_hasElement`/`d2e_element`/`eEp`, none of which fetch touches, so
--   it's the literal same proposition in `i` and `i'`.
-- * `rule_RL_writeback`: backward HOLDS, trivially -- writeback touches
--   none of the four fields (`f2d_hasElement`, `f2d_element`,
--   `d2e_hasElement`, `d2e_element`, `eEp`) that `PipeInv` reads, so
--   `PipeInv i` and `PipeInv i'` are the identical proposition.
-- * `rule_RL_decode`: backward FAILS, specifically on the *squash* branch
--   (`epochMismatch = true` via an `idEp` mismatch alone, independent of
--   `ieEp`). Decode always drains `f2d` (`f2d_hasElement := false`) whether
--   it squashes or issues, and the squash branch passes `d2e` through
--   untouched. So a pre-state with `f2d_hasElement = d2e_hasElement = true`
--   but `f2d_element.ieEp ≠ d2e_element.ieEp` (violating K) can still fire
--   decode's squash branch (all it needs is `idEp` mismatch), producing a
--   post-state with `f2d_hasElement = false` -- vacuously satisfying K'
--   -- even though nothing about the actual epoch tags was reconciled.
--   See `counterI_decode`/`PipeInv_backward_rule_RL_decode_fails` below.
-- * `rule_RL_execute`: backward FAILS, and more dramatically: execute
--   *always* sets `d2e_hasElement := false` unconditionally (both branches),
--   so `PipeInv i'` is TRUE FOR FREE after any execute step, regardless of
--   `i` -- it carries zero information backward. Any pre-state `i` with
--   `d2e_hasElement = true` and a bad epoch tag (violating J or K) that
--   otherwise satisfies execute's fire guard is a counterexample.
--   See `counterI_execute`/`PipeInv_backward_rule_RL_execute_fails` below.
--
-- Not currently used by anything -- kept here purely as a validated
-- exploration, not landed into mktop_pipelined_spec.lean.
import Star.Bluespec.SimpleProcessor.mktop_pipelined_spec
open BluespecPrelude BluespecVerification ReachingStar Bluespec Params_types M_mktop_pipelined

set_option maxHeartbeats 4000000

inductive φ : ImplModule.State → SpecModule.State → Prop where
| flusehd : ∀ i s, phi0 i s → φ i s
| doFetch : ∀ i i' s, φ i' s → ImplModule.getRule .rule_RL_fetch i i' → φ i s
| doDecode : ∀ i i' s, φ i' s → ImplModule.getRule .rule_RL_decode i i' → φ i s
| doExecute : ∀ i i' s, φ i' s → ImplModule.getRule .rule_RL_execute i i' → φ i s
| doWriteback : ∀ i i' s, φ i' s → ImplModule.getRule .rule_RL_writeback i i' → φ i s

theorem PipeInv_backward_rule_RL_fetch {i i' : ImplModule.State} (hInv : PipeInv i')
    (hr : ImplModule.getRule .rule_RL_fetch i i') : PipeInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hJ', _⟩ := hInv
  have hf2d0 : i.f2d_hasElement = false := by
    dsimp only [fifo_RDY_enq] at hguard
    rcases h : i.f2d_hasElement with _ | _
    · rfl
    · exfalso; simp [h] at hguard
  refine ⟨hJ', ?_⟩
  rintro ⟨hf2d, _⟩
  rw [hf2d0] at hf2d
  exact absurd hf2d (by decide)

theorem PipeInv_backward_rule_RL_writeback {i i' : ImplModule.State} (hInv : PipeInv i')
    (hr : ImplModule.getRule .rule_RL_writeback i i') : PipeInv i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

-- Counterexample for decode: `idEp` mismatches `dEp` (forces squash
-- regardless of `ieEp`), while `f2d`'s `ieEp` (1) disagrees with `d2e`'s
-- `ieEp` (0, which *does* agree with `eEp`, so J already holds in `i`).
-- K fails in `i` (1 ≠ 0) but decode's squash branch fires anyway (only
-- drains `f2d`, passes `d2e` through), so K' is vacuous in `i'`.
def counterI_decode : ImplModule.State :=
  { f2d_hasElement := true
    f2d_element := { pc := 0, ppc := 4, idEp := 1, ieEp := 1 }
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 0, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv_backward_rule_RL_decode_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv i' → ImplModule.getRule .rule_RL_decode i i' → PipeInv i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_decode counterI_decode (rule_RL_decode counterI_decode).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_decode) (i' := (rule_RL_decode counterI_decode).2)
    (by unfold PipeInv; decide) hr
  exact absurd this (by unfold PipeInv; decide)

-- Counterexample for execute: `d2e`'s `ieEp` (1) disagrees with `eEp` (0),
-- violating J in `i` (`f2d_hasElement := false` here so K is moot). Execute
-- fires its squash branch (`ieEpMismatch = true`) fine -- it never checks
-- J/K -- and *always* clears `d2e_hasElement`, making `PipeInv i'` vacuously
-- true no matter what `i` looked like.
def counterI_execute : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := default
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv_backward_rule_RL_execute_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv i' → ImplModule.getRule .rule_RL_execute i i' → PipeInv i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_execute counterI_execute (rule_RL_execute counterI_execute).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_execute) (i' := (rule_RL_execute counterI_execute).2)
    (by unfold PipeInv; decide) hr
  exact absurd this (by unfold PipeInv; decide)

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #1: decode's failure above is entirely about K's
-- `f2d_hasElement ∧` conjunct (squashing needs only an `idEp` mismatch,
-- independent of `ieEp`, yet still drains `f2d`). Does DROPPING that
-- conjunct -- gating K on `d2e_hasElement` alone, i.e. the same flag J
-- already uses -- fix it?
--
-- Answer: it fixes decode (both branches, and writeback stays trivial),
-- but it just MOVES the problem to fetch instead of eliminating it. K2's
-- forward-preservation through decode's squash branch works because K2 is
-- now a literal identity across that branch (`f2d_element`/`d2e_hasElement`/
-- `d2e_element` are ALL unchanged by squash), and through decode's normal
-- branch it holds "for free" (`d2e_element.ieEp` is *copied* from
-- `f2d_element.ieEp` at the exact instant it's set, so K2 holds by
-- reflexivity, not by appeal to any previous invariant) -- both of which
-- make it trivially invertible too. But `fetch` previously got a free ride
-- on the OLD K precisely BECAUSE its guard forces `f2d_hasElement = false`,
-- making the old (both-flags-gated) K vacuous in `i` regardless of the
-- (unconstrained, stale) garbage sitting in `f2d_element`. K2 removes that
-- escape hatch: now that same garbage IS constrained (whenever
-- `d2e_hasElement`), so a pre-state can have `d2e_hasElement = true` with
-- stale, disagreeing garbage in the not-yet-overwritten `f2d_element` --
-- fetch overwrites it with a freshly-consistent tag either way, so K2'
-- comes out true regardless. See `counterI_fetch2` below.
--
-- Root cause, in short: this is genuinely a "stale FIFO payload" problem
-- (same species as the `rv1`/`rv2` issue fixed earlier in
-- `mktop_pipelined.lean`), not purely an artifact of which flag gates the
-- implication. The model never resets `f2d_element`/`d2e_element` on
-- drain, so *some* flag has to gate the K-style conjunct to avoid talking
-- about meaningless garbage -- and whichever flag you pick, the rule that
-- clears *that* flag without syncing the payload becomes the new failure.
def PipeInv2 (i : ImplModule.State) : Prop :=
  (i.d2e_hasElement → i.d2e_element.ieEp = i.eEp) ∧
  (i.d2e_hasElement → i.f2d_element.ieEp = i.d2e_element.ieEp)

theorem PipeInv2_preserved_rule_RL_fetch {i i' : ImplModule.State} (hInv : PipeInv2 i)
    (hr : ImplModule.getRule .rule_RL_fetch i i') : PipeInv2 i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hJ, _⟩ := hInv
  refine ⟨hJ, ?_⟩
  intro hd2e
  exact (hJ hd2e).symm

theorem PipeInv2_preserved_rule_RL_decode {i i' : ImplModule.State} (hInv : PipeInv2 i)
    (hr : ImplModule.getRule .rule_RL_decode i i') : PipeInv2 i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
    M_mktop_pipelined.rule_RL_decode_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hJ, hK⟩ := hInv
  generalize hsq :
    bool_or (bool_not (if (i.f2d_element.idEp == i.dEp) = true then BTrue Unit_ else BFalse Unit_))
      (bool_not (if (i.f2d_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_)) = sq at *
  cases sq
  case BTrue a =>
    cases a
    dsimp only at hJ hK ⊢
    exact ⟨hJ, hK⟩
  case BFalse a =>
    cases a
    dsimp only at hJ hK hguard ⊢
    refine ⟨?_, ?_⟩
    · intro _
      simp only [bool_or_eq_false_iff] at hsq
      obtain ⟨_, hB⟩ := hsq
      rw [bool_not_eq_false_iff] at hB
      split_ifs at hB
      rename_i heq
      exact (beq_iff_eq ..).mp heq
    · intro _
      rfl

theorem PipeInv2_preserved_rule_RL_execute {i i' : ImplModule.State} (hInv : PipeInv2 i)
    (hr : ImplModule.getRule .rule_RL_execute i i') : PipeInv2 i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute,
    M_mktop_pipelined.rule_RL_execute_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  refine ⟨?_, ?_⟩ <;> simp

theorem PipeInv2_preserved_rule_RL_writeback {i i' : ImplModule.State} (hInv : PipeInv2 i)
    (hr : ImplModule.getRule .rule_RL_writeback i i') : PipeInv2 i' := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

theorem PipeInv2_backward_rule_RL_decode {i i' : ImplModule.State} (hInv : PipeInv2 i')
    (hr : ImplModule.getRule .rule_RL_decode i i') : PipeInv2 i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_decode,
    M_mktop_pipelined.rule_RL_decode_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  obtain ⟨hJ', hK'⟩ := hInv
  generalize hsq :
    bool_or (bool_not (if (i.f2d_element.idEp == i.dEp) = true then BTrue Unit_ else BFalse Unit_))
      (bool_not (if (i.f2d_element.ieEp == i.eEp) = true then BTrue Unit_ else BFalse Unit_)) = sq at *
  cases sq
  case BTrue a =>
    cases a
    dsimp only at hJ' hK' ⊢
    exact ⟨hJ', hK'⟩
  case BFalse a =>
    cases a
    dsimp only at hguard ⊢
    have hd2e : i.d2e_hasElement = false := by
      dsimp only [fifo_RDY_enq] at hguard
      simp only [bool_and_true_iff] at hguard
      rcases h : i.d2e_hasElement with _ | _
      · rfl
      · exfalso; simp [h] at hguard
    refine ⟨?_, ?_⟩ <;> (rw [hd2e]; intro h; exact absurd h (by decide))

theorem PipeInv2_backward_rule_RL_writeback {i i' : ImplModule.State} (hInv : PipeInv2 i')
    (hr : ImplModule.getRule .rule_RL_writeback i i') : PipeInv2 i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

-- Counterexample: dropping the f2d_hasElement gate shifts the problem to
-- FETCH. Now `i`'s stale (unoccupied) f2d_element is unconstrained garbage,
-- and fetch's guard doesn't care what garbage was there -- it just
-- overwrites it with a freshly-consistent tag. So `PipeInv2 i` can be FALSE
-- (garbage ieEp disagrees with d2e) while `PipeInv2 i'` is forced TRUE.
def counterI_fetch2 : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := { pc := 0, ppc := 4, idEp := 0, ieEp := 1 }
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 0, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv2_backward_rule_RL_fetch_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv2 i' → ImplModule.getRule .rule_RL_fetch i i' → PipeInv2 i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_fetch counterI_fetch2 (rule_RL_fetch counterI_fetch2).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_fetch2) (i' := (rule_RL_fetch counterI_fetch2).2)
    (by unfold PipeInv2; decide) hr
  exact absurd this (by unfold PipeInv2; decide)

-- Execute is unaffected by this reformulation -- K was never the reason
-- execute broke backward, J was (untouched here), and execute always
-- clears d2e_hasElement unconditionally regardless of K's shape.
def counterI_execute2 : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := default
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv2_backward_rule_RL_execute_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv2 i' → ImplModule.getRule .rule_RL_execute i i' → PipeInv2 i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_execute counterI_execute2 (rule_RL_execute counterI_execute2).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_execute2) (i' := (rule_RL_execute counterI_execute2).2)
    (by unfold PipeInv2; decide) hr
  exact absurd this (by unfold PipeInv2; decide)

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #2: in the ACTUAL spec file, `PipeInv`'s first
-- conjunct J is destructured (`obtain ⟨hJ, hK⟩ := hInv`) at the one real
-- call site (`commutes_rule_RL_decode_rule_RL_execute`) but `hJ` is never
-- referenced again there -- only `hK`. Since the top-level consumer never
-- reads J, does dropping J from the invariant's definition entirely (i.e.
-- keeping ONLY the original, both-flags-gated K as a standalone invariant)
-- help?
--
-- Answer: no -- and it's worse than "no help", it breaks FORWARD
-- preservation outright. J is never read by the confluence proof, but it IS
-- read by K's OWN forward-preservation proof through `rule_RL_fetch`
-- (`exact (hJ hd2e).symm` at spec line ~470): fetch tags the freshly-filled
-- `f2d_element` with the CURRENT `eEp`, and the only way to know that
-- matches whatever's already sitting in `d2e_element.ieEp` is J itself.
-- Without it, nothing pins down `d2e_element.ieEp` at all, so `f2d`'s new
-- tag can simply disagree. This is the standard "auxiliary invariant"
-- pattern: J is scaffolding needed purely to keep K inductive across steps,
-- not because anything downstream ever consumes it directly -- removing an
-- unused conjunct from an invariant bundle is only safe if the invariant is
-- still self-sustaining without it, and here it isn't.
def PipeInv_Konly (i : ImplModule.State) : Prop :=
  i.f2d_hasElement ∧ i.d2e_hasElement → i.f2d_element.ieEp = i.d2e_element.ieEp

def counterI_fetch_noJ : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := default
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0  -- d2e_element.ieEp (1) ≠ eEp (0): the fact J would have given us
              -- is false here, and nothing else pins it down
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv_Konly_not_preserved_rule_RL_fetch :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv_Konly i →
        ImplModule.getRule .rule_RL_fetch i i' → PipeInv_Konly i') := by
  intro h
  have hr : ImplModule.getRule .rule_RL_fetch counterI_fetch_noJ (rule_RL_fetch counterI_fetch_noJ).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_fetch_noJ) (i' := (rule_RL_fetch counterI_fetch_noJ).2)
    (by unfold PipeInv_Konly; decide) hr
  exact absurd this (by unfold PipeInv_Konly; decide)

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #3: does resetting stale FIFO elements to a
-- canonical `default` on drain (rather than leaving real garbage) fix
-- fetch's PipeInv2 failure above? (Same species of change as the `rv1`/
-- `rv2` zeroing fix already landed in `mktop_pipelined.lean`, just applied
-- to whole elements instead of individual operands.)
--
-- Answer: no. K2 needs the (previously-drained, now-inert) `f2d_element`
-- to match `d2e_element.ieEp` -- a LIVE value set independently by whatever
-- decode last issued into `d2e`, unrelated to fetch/draining at all. A
-- FIXED default can only ever match one specific `ieEp` value; `d2e`'s
-- actual tag is a moving target it has no way to track. Below, `i` satisfies
-- BOTH the reset invariant (`f2d_element = default` given `¬f2d_hasElement`)
-- AND J (`d2e_element.ieEp = eEp`) -- i.e. even granting the model change
-- AND the one real half of the invariant -- and K2 still fails, because
-- `default.ieEp` (0, fixed) simply isn't `d2e_element.ieEp` (1, live) here.
-- "Reset to a canonical default" only ever helps when the invariant needs
-- the inert field to match ANOTHER FIXED thing; here it needs to match a
-- live, independently-varying field, which no static reset can do -- you'd
-- need to keep the field *dynamically* re-synced (turning `ieEp` from
-- stored data into a computed projection off `eEp`/`d2e_element`, not
-- reset it once and leave it), which is a much bigger structural change,
-- not "resetting to a default value".
def counterI_fetch_reset : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := default  -- the "reset" value; default.ieEp = 0
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 1  -- matches d2e_element.ieEp, so J holds in `i`
    commitQ_hasElement := false
    commitQ_element := default }

example : ¬ counterI_fetch_reset.f2d_hasElement → counterI_fetch_reset.f2d_element = default := by
  intro _; rfl

example : counterI_fetch_reset.d2e_hasElement →
    counterI_fetch_reset.d2e_element.ieEp = counterI_fetch_reset.eEp := by decide

theorem PipeInv2_backward_rule_RL_fetch_fails_even_with_reset :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv2 i' → ImplModule.getRule .rule_RL_fetch i i' → PipeInv2 i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_fetch counterI_fetch_reset (rule_RL_fetch counterI_fetch_reset).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_fetch_reset) (i' := (rule_RL_fetch counterI_fetch_reset).2)
    (by unfold PipeInv2; decide) hr
  exact absurd this (by unfold PipeInv2; decide)

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #4: completes the 2x2 "which flags gate K" matrix.
-- We've tried both-gated (original K: forward-sound, backward fails on
-- decode-squash + execute) and d2e-gated-only (K2: forward-sound, backward
-- fails on fetch + execute, i.e. `PipeInv2` above). The symmetric remaining
-- case: gate on f2d_hasElement ONLY (drop d2e_hasElement instead).
--
-- Answer: breaks forward preservation via fetch (so it isn't even a valid
-- invariant) -- symmetric to how dropping J broke `PipeInv_Konly`. Here the
-- unconstrained culprit is a stale `d2e_element` (garbage while
-- `d2e_hasElement = false`) that a freshly-fetched `f2d` tag has no reason
-- to match. Combined with the fully-ungated case (shown earlier, via the
-- `PipeInv2` header comment's `J''`/`K''` discussion, to *also* break
-- forward preservation the same way): of routing K through 4/4 possible
-- flag-gatings, exactly ONE (both-gated, i.e. the ORIGINAL `PipeInv`) is
-- even forward-sound, and it's exactly the one that fails backward.
def PipeInv3 (i : ImplModule.State) : Prop :=
  i.f2d_hasElement → i.f2d_element.ieEp = i.d2e_element.ieEp

def counterI_fetch_k3 : ImplModule.State :=
  { f2d_hasElement := false
    f2d_element := default
    d2e_hasElement := false
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv3_not_preserved_rule_RL_fetch :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv3 i →
        ImplModule.getRule .rule_RL_fetch i i' → PipeInv3 i') := by
  intro h
  have hr : ImplModule.getRule .rule_RL_fetch counterI_fetch_k3 (rule_RL_fetch counterI_fetch_k3).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_fetch_k3) (i' := (rule_RL_fetch counterI_fetch_k3).2)
    (by unfold PipeInv3; decide) hr
  exact absurd this (by unfold PipeInv3; decide)

-- ════════════════════════════════════════════════════════════════════
-- CONCLUSION (see chat for the full writeup): no single-state
-- reformulation of this invariant is simultaneously (a) forward-sound,
-- (b) strong enough for `commutes_rule_RL_decode_rule_RL_execute`, and
-- (c) backward-invariant through all four rules. Fetch's own soundness
-- FORCES the invariant to contain a `d2e_hasElement`-gated fact tying
-- `d2e_element.ieEp` to the live `eEp` (J, in some guise) -- and `execute`
-- is precisely the rule that unconditionally clears `d2e_hasElement` while
-- potentially also changing `eEp` in the same step, discarding exactly
-- that fact by design. This isn't a gating artifact (see the 4/4 matrix
-- above) -- it reflects that epoch resolution is genuinely, deliberately
-- lossy. None of this is needed by the actual proof, though: `PipeInv a`
-- at the confluence call site is established the ordinary way (forward
-- induction from the initial state via `PipeInv_preserved`), which never
-- required backward reasoning in the first place.

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #5: the above conclusion assumed the reformulation
-- ALSO had to be independently forward-sound. Dropping that requirement
-- entirely -- does it help?
--
-- Answer: YES, substantially -- this overturns the "execute is
-- information-theoretically hopeless" framing above. `PipeInv3` (`K3`
-- earlier, gated on `f2d_hasElement` ONLY -- the MIRROR of `PipeInv2`,
-- which gated on `d2e_hasElement` only) holds backward through fetch,
-- execute, AND writeback (all three PROVEN below, not just
-- counterexample-free). `execute`/`writeback` never touch
-- `f2d_hasElement`/`f2d_element`/`d2e_element` at all -- `K3 i` and `K3 i'`
-- are the identical proposition across both rules. `fetch`'s own guard
-- forces `f2d_hasElement = false` pre-fire, making `K3 i` vacuous there.
-- My earlier claim that execute's failure was a fundamental,
-- information-theoretic dead end (1-bit epoch, erasure) was only ever true
-- of invariants gated on `d2e_hasElement` (J, K2) -- the flag EXECUTE
-- itself clears. Gate on the OTHER flag and execute becomes a non-issue.
--
-- But `decode` is now the lone holdout, and UNIFORMLY so (both branches,
-- not just squash) -- decode ALWAYS clears `f2d_hasElement`, so `K3 i'` is
-- always vacuous immediately after, regardless of branch. This produces a
-- clean, symmetric picture: decode is to `f2d_hasElement` exactly what
-- execute is to `d2e_hasElement` -- the rule whose entire job is to
-- unconditionally consume that flag. Gating on a flag protects you from
-- every OTHER rule, but never from the one that retires it.
--
-- Does conjoining K2 ∧ K3 rescue both sides? No (checked, not included as
-- a formal theorem below since it's subsumed by the following argument):
-- K2's fetch failure is about stale garbage in `f2d_element` BEFORE fetch
-- overwrites it with a fresh, `eEp`-derived tag -- K3 says NOTHING about
-- that garbage (its antecedent, f2d_hasElement, is false exactly when the
-- garbage exists), so it can't patch K2's hole. "Gate on f2d_hasElement to
-- survive decode" and "don't, to survive fetch's garbage-overwrite" are
-- directly contradictory requirements for the same single comparison.
-- (`PipeInv3` itself is already defined above, in experiment #4.)

theorem PipeInv3_backward_rule_RL_fetch {i i' : ImplModule.State} (hInv : PipeInv3 i')
    (hr : ImplModule.getRule .rule_RL_fetch i i') : PipeInv3 i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  intro hf2d
  exfalso
  dsimp only [fifo_RDY_enq] at hguard
  rcases h : i.f2d_hasElement with _ | _
  · simp [h] at hf2d
  · simp [h] at hguard

theorem PipeInv3_backward_rule_RL_execute {i i' : ImplModule.State} (hInv : PipeInv3 i')
    (hr : ImplModule.getRule .rule_RL_execute i i') : PipeInv3 i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_execute,
    M_mktop_pipelined.rule_RL_execute_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

theorem PipeInv3_backward_rule_RL_writeback {i i' : ImplModule.State} (hInv : PipeInv3 i')
    (hr : ImplModule.getRule .rule_RL_writeback i i') : PipeInv3 i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

-- Decode, squash branch: f2d_hasElement always clears -> K3 i' always
-- vacuous, hiding whatever was true pre-squash (idEp mismatch alone
-- suffices, independent of ieEp -- same shape as the very first
-- `counterI_decode` example above).
def counterI_decode_squash_k3 : ImplModule.State :=
  { f2d_hasElement := true
    f2d_element := { pc := 0, ppc := 4, idEp := 1, ieEp := 1 }
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 0, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv3_backward_rule_RL_decode_squash_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv3 i' → ImplModule.getRule .rule_RL_decode i i' → PipeInv3 i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_decode counterI_decode_squash_k3
      (rule_RL_decode counterI_decode_squash_k3).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_decode_squash_k3) (i' := (rule_RL_decode counterI_decode_squash_k3).2)
    (by unfold PipeInv3; decide) hr
  exact absurd this (by unfold PipeInv3; decide)

-- Decode, normal branch: f2d_hasElement ALSO always clears here (decode
-- clears it unconditionally, regardless of branch), so the failure isn't
-- squash-specific -- it's uniform across all of decode. (imem/dmem set to
-- `#[]` here purely so kernel `rfl`/`decide` don't have to force-reduce the
-- 65536-entry `M_mkSimpleMem.defaultMem` that decode's normal branch -- but
-- not squash's -- actually reads through to compute `decodedInst`;
-- `Array.getD`'s out-of-bounds default gives the identical value either
-- way.)
def counterI_decode_normal_k3 : ImplModule.State :=
  { f2d_hasElement := true
    f2d_element := { pc := 0, ppc := 4, idEp := 0, ieEp := 0 }  -- idEp=dEp, ieEp=eEp: normal branch fires
    d2e_hasElement := false  -- required for normal branch's guard (enqueue-ready)
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 1, rv1 := 0, rv2 := 0 }  -- stale garbage, ieEp=1 ≠ f2d's ieEp=0
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    imem := #[]
    dmem := #[]
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv3_backward_rule_RL_decode_normal_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv3 i' → ImplModule.getRule .rule_RL_decode i i' → PipeInv3 i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_decode counterI_decode_normal_k3
      (rule_RL_decode counterI_decode_normal_k3).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_decode_normal_k3) (i' := (rule_RL_decode counterI_decode_normal_k3).2)
    (by unfold PipeInv3; decide) hr
  exact absurd this (by unfold PipeInv3; decide)

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #6: forget about forward preservation ENTIRELY --
-- does K alone (`PipeInv_Konly`, dropping J from the invariant's
-- definition, not just from its use -- already defined above in
-- experiment #2, where it was tested for FORWARD preservation) do any
-- BETTER backward than the full J ∧ K bundle did?
--
-- Answer: no change at all. K alone still fails at EXACTLY the same two
-- rules (decode-squash, execute) and holds at the same two (fetch,
-- writeback) as full `PipeInv` did. J and K are backward-INDEPENDENT:
-- each conjunct's backward fate is decided entirely by its own gating
-- flag and the rules that touch it, with zero cross-talk between them.
-- `counterI_decode` already demonstrates this -- J already holds in `i`
-- there (d2e's ieEp already agrees with eEp) and K alone is what breaks,
-- so it's a valid K-only counterexample as-is. `counterI_execute`,
-- however, had `f2d_hasElement := false`, making K moot and pinning that
-- disproof on J alone -- so a FRESH execute counterexample is needed
-- below to show K itself independently fails there too.
--
-- This is the mirror image of the forward story, where J was load-
-- bearing scaffolding *for* K (dropping it broke K's own forward step
-- through fetch). Backward, dropping J doesn't cost K anything, but it
-- also doesn't buy K anything -- the two conjuncts just never interacted
-- in the backward direction to begin with.

theorem PipeInv_Konly_backward_rule_RL_fetch {i i' : ImplModule.State}
    (hInv : PipeInv_Konly i') (hr : ImplModule.getRule .rule_RL_fetch i i') :
    PipeInv_Konly i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_fetch,
    M_mktop_pipelined.rule_RL_fetch_core] at hr
  obtain ⟨hguard, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  rintro ⟨hf2d, _⟩
  dsimp only [fifo_RDY_enq] at hguard
  rcases h : i.f2d_hasElement with _ | _
  · rw [h] at hf2d; exact absurd hf2d (by decide)
  · simp [h] at hguard

theorem PipeInv_Konly_backward_rule_RL_writeback {i i' : ImplModule.State}
    (hInv : PipeInv_Konly i') (hr : ImplModule.getRule .rule_RL_writeback i i') :
    PipeInv_Konly i := by
  dsimp [ImplModule, Module.getRule, ofRule, M_mktop_pipelined.rule_RL_writeback,
    M_mktop_pipelined.rule_RL_writeback_core] at hr
  obtain ⟨_, hi2⟩ := Prod.mk.injEq .. |>.mp hr
  subst hi2
  exact hInv

-- Same counterexample state as `counterI_decode` above -- K alone fails
-- backward at decode-squash for the identical reason (J's status there
-- is irrelevant either way, it already held in `i`).
theorem PipeInv_Konly_backward_rule_RL_decode_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv_Konly i' → ImplModule.getRule .rule_RL_decode i i' → PipeInv_Konly i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_decode counterI_decode (rule_RL_decode counterI_decode).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_decode) (i' := (rule_RL_decode counterI_decode).2)
    (by unfold PipeInv_Konly; decide) hr
  exact absurd this (by unfold PipeInv_Konly; decide)

-- NEW counterexample for execute: unlike `counterI_execute` above (which
-- had `f2d_hasElement := false`, making K moot there and pinning the
-- failure on J alone), this one sets BOTH flags true -- exactly what
-- execute's own guard requires of `d2e_hasElement`, plus an unrelated-but-
-- true `f2d_hasElement` (execute never reads `f2d` at all) -- with
-- mismatched f2d/d2e tags, so K itself (independent of J) is violated in
-- `i`, and execute's unconditional `d2e_hasElement := false` erases it.
def counterI_execute_konly : ImplModule.State :=
  { f2d_hasElement := true
    f2d_element := { pc := 0, ppc := 4, idEp := 0, ieEp := 1 }
    d2e_hasElement := true
    d2e_element := { dInst := default, pc := 0, ppc := 4, ieEp := 0, rv1 := 0, rv2 := 0 }
    e2w_hasElement := false
    e2w_element := default
    pc := 0
    dEp := 0
    eEp := 0
    commitQ_hasElement := false
    commitQ_element := default }

theorem PipeInv_Konly_backward_rule_RL_execute_fails :
    ¬ (∀ {i i' : ImplModule.State}, PipeInv_Konly i' → ImplModule.getRule .rule_RL_execute i i' → PipeInv_Konly i) := by
  intro h
  have hr : ImplModule.getRule .rule_RL_execute counterI_execute_konly (rule_RL_execute counterI_execute_konly).2 := by
    dsimp [ImplModule, Module.getRule, ofRule]
    rfl
  have := h (i := counterI_execute_konly) (i' := (rule_RL_execute counterI_execute_konly).2)
    (by unfold PipeInv_Konly; decide) hr
  exact absurd this (by unfold PipeInv_Konly; decide)

-- REVISED CONCLUSION: decode and execute play perfectly symmetric roles --
-- each is the sole "retiring" rule for one of the two flags this invariant
-- shape needs. Gating on either flag survives everything except the rule
-- that retires it, and no way of combining the two gated comparisons
-- patches both holes simultaneously (the counterexamples are genuinely
-- different mechanisms: stale-garbage-exposed-by-fetch vs.
-- flag-cleared-by-decode). Whether something OUTSIDE this "single direct
-- tag comparison" family could do better -- e.g. tracking additional
-- ghost/historical state -- is open; nothing tried here achieves all four.

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #7: `φ` (user-added above) is a hand-specialized
-- instance of the *actual* `φ_ind` machinery (`Star/Commute/ARS.lean`)
-- that the whole refinement proof runs on -- same `phi0` base relation,
-- same "walk backward one rule-step at a time from a flushed dead end"
-- shape. Question: does `φ i s → PipeInv i`?

-- Base case: `phi0 i s → PipeInv i` HOLDS, and for a clean structural
-- reason, not a coincidence. Both of `phi0`'s shapes tag `f2d_element` with
-- `ieEp := i.eEp` directly (literally in the `phi0` definition), and Shape
-- A's `d2e_element := decodeAt i.imem i.dEp i.eEp sb1 i.rf s2.pc` -- built
-- from the impl's own `rule_RL_decode_core` with `i.eEp` as the "current
-- epoch" argument -- has `.ieEp = i.eEp` too, by the already-proven
-- `decodeAt_ieEp` (using phi0's own `s2.pc`-legality conjunct as its
-- hypothesis). So in Shape A, both sides of J/K collapse to `i.eEp = i.eEp`
-- by construction; in Shape B, `d2e_hasElement = false` makes both
-- conjuncts vacuous. Either way, `phi0`'s rigid "every field pinned down by
-- explicit `Spec.stepOne`-lookaheads" shape leaves no room for the kind of
-- tag mismatch this whole file has been exploiting.
theorem phi0_implies_PipeInv {i : ImplModule.State} {s : SpecModule.State}
    (h : phi0 i s) : PipeInv i := by
  obtain ⟨_, hcq, hcqe, hrf, hA | hB⟩ := h
  · obtain ⟨_, _, _, hsb, hdmem, he2we, hd2ee, hf2de, hpc, hleg1, hleg2, hleg3⟩ := hA
    refine ⟨?_, ?_⟩
    · intro _
      rw [hd2ee]
      exact decodeAt_ieEp _ _ _ _ _ _ hleg2
    · intro _
      rw [hf2de, hd2ee, decodeAt_ieEp _ _ _ _ _ _ hleg2]
  · obtain ⟨_, hd2e, _, _⟩ := hB
    refine ⟨?_, ?_⟩
    · intro h; rw [hd2e] at h; exact absurd h (by decide)
    · rintro ⟨_, h⟩; rw [hd2e] at h; exact absurd h (by decide)

-- Inductive case: naive structural induction on `φ` reduces `doFetch`/
-- `doWriteback` to the already-proven backward lemmas directly, but
-- `doDecode`/`doExecute` need EXACTLY `PipeInv i' → step i i' → PipeInv i`
-- for the general (unrestricted) `i` -- the statement `PipeInv_backward_
-- rule_RL_decode_fails`/`_execute_fails` already PROVE is false. So this
-- specific proof strategy cannot close those two cases in general.
--
-- This alone doesn't settle `φ i s → PipeInv i` overall -- `phi0` requires
-- `f2d_hasElement = true` in BOTH shapes (fetch never blocks at a dead
-- end), while decode unconditionally clears `f2d_hasElement`. So decode's
-- post-squash state can never satisfy `phi0` directly; turning a decode
-- counterexample into a genuine disproof of the FULL claim needs carrying
-- its successor forward through more concrete steps until it satisfies
-- SOME `phi0 i'' s'`. Settled below by actually doing this.
theorem φ_implies_PipeInv_attempt {i : ImplModule.State} {s : SpecModule.State}
    (h : φ i s) : PipeInv i := by
  induction h with
  | flusehd i s h0 => exact phi0_implies_PipeInv h0
  | doFetch i i' s _ hr ih => exact PipeInv_backward_rule_RL_fetch ih hr
  | doDecode i i' s _ hr ih => sorry
  | doExecute i i' s _ hr ih => sorry
  | doWriteback i i' s _ hr ih => exact PipeInv_backward_rule_RL_writeback ih hr

-- ════════════════════════════════════════════════════════════════════
-- Follow-up experiment #8: settling `φ i s → PipeInv i` for real, by
-- mechanically constructing a full counterexample. Since `PipeInv` doesn't
-- mention `s`, and `∀ s (P s → Q) ↔ (∃ s, P s) → Q` when `Q` doesn't depend
-- on `s`, we just need ONE `s` -- solved for after the fact, not matched
-- against anything external.
--
-- Program: an all-NOP instruction stream (`ADDI x0, x0, 0` = `0x00000013`
-- -- legal, touches no register but x0, so no data hazard is ever
-- possible; decode can only ever be capacity-blocked, landing squarely in
-- `phi0`'s Shape A). Starting from `i_bad` (a `counterI_decode`-style K
-- violation: stale `f2d` tag disagrees with a REAL, `decodeAt`-derived
-- `d2e` entry), fire decode's squash branch, then just keep running the
-- machine forward (fetch/decode/execute/writeback, always picking
-- whichever rule is enabled) for 8 more steps. It lands EXACTLY in Shape A
-- (`f2d` = a freshly-fetched I3, `d2e` = I2, `e2w` = I1, `commitQ` = I0),
-- and the natural spec state `s_witness := {pc:=0, rf:=zeroRf, imem, dmem}`
-- (i.e. "everything before I0") makes every one of `phi0`'s equations true
-- by `rfl` -- the sequential spec, run on the same all-NOP program, retraces
-- the exact same pc/rf/dmem trajectory the impl took for real, since
-- nothing ever branches or touches a register besides x0.
--
-- Result: `φ i_bad s_witness` holds (9 constructor applications: 1 decode
-- + 8 more rule-steps down to the `phi0` dead end), while `PipeInv i_bad`
-- is false. `φ i s → PipeInv i` is FALSE, mechanically confirmed -- the
-- earlier `phi0_implies_PipeInv` base-case result was real, but `φ`'s
-- backward closure genuinely does reach past it into non-`PipeInv` territory.
def nopImem : Array (BitVec 32) := #[0x00000013, 0x00000013, 0x00000013, 0x00000013]
def zeroRfL : Array (BitVec 32) := .mk (List.replicate 32 0)
def zeroSbL : Array (BitVec 2) := .mk (List.replicate 32 0)
def smallDmemL : Array (BitVec 32) := #[0]

def i_bad : ImplModule.State :=
  { f2d_hasElement := true
    f2d_element := { pc := 4, ppc := 8, idEp := 1, ieEp := 1 }
    d2e_hasElement := true
    d2e_element := decodeAt nopImem 0 0 zeroSbL zeroRfL 0
    e2w_hasElement := false
    e2w_element := default
    pc := 4
    rf := zeroRfL
    sb := zeroSbL
    dEp := 0
    eEp := 0
    imem := nopImem
    dmem := smallDmemL
    commitQ_hasElement := false
    commitQ_element := default }

theorem i_bad_violates_PipeInv : ¬ PipeInv i_bad := by unfold PipeInv; decide

def i_1 := (rule_RL_decode i_bad).2
def i_2 := (rule_RL_fetch i_1).2
def i_3 := (rule_RL_execute i_2).2
def i_4 := (rule_RL_decode i_3).2
def i_5 := (rule_RL_fetch i_4).2
def i_6 := (rule_RL_writeback i_5).2
def i_7 := (rule_RL_execute i_6).2
def i_8 := (rule_RL_decode i_7).2
def i_9 := (rule_RL_fetch i_8).2

def s_witness : SpecModule.State := { pc := 0, rf := zeroRfL, imem := nopImem, dmem := smallDmemL }

-- i_9 lands exactly in phi0's Shape A for s_witness.
theorem phi0_i9 : phi0 i_9 s_witness := by
  unfold phi0
  exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem φ_i_bad : φ i_bad s_witness :=
  φ.doDecode i_bad i_1 s_witness
    (φ.doFetch i_1 i_2 s_witness
      (φ.doExecute i_2 i_3 s_witness
        (φ.doDecode i_3 i_4 s_witness
          (φ.doFetch i_4 i_5 s_witness
            (φ.doWriteback i_5 i_6 s_witness
              (φ.doExecute i_6 i_7 s_witness
                (φ.doDecode i_7 i_8 s_witness
                  (φ.doFetch i_8 i_9 s_witness (φ.flusehd i_9 s_witness phi0_i9)
                    (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
                  (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
                (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
              (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
            (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
          (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
        (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
      (by dsimp [ImplModule, Module.getRule, ofRule]; rfl))
    (by dsimp [ImplModule, Module.getRule, ofRule]; rfl)

theorem φ_does_not_imply_PipeInv :
    ¬ (∀ {i : ImplModule.State} {s : SpecModule.State}, φ i s → PipeInv i) := by
  intro h
  exact absurd (h φ_i_bad) i_bad_violates_PipeInv
