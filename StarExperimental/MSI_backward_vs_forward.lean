import StarExperimental.MSI_bag_def

/-! # `MSI_backward_vs_forward`: `badView` versus the forward invariant `ψ_msi`

`ψ_msi` is the hand-written invariant of the forward simulation of `FormalMSI`, translated to the
single-address model (no tag, no address; in the bag model "at most one message" is
`countP ≤ 1`). Here we prove that **`badView` implies it** (`ψ_of_noBad`): every clause of
`ψ_msi` is ruled out by patterns 1, 2, 4, 5, 6, 7 of `badView`, read on the view `(c, c)`.
The converse is false (`ψ_not_noBad`): `ψ_msi` quantifies over a single index and rules out
neither two `M` rows (pattern 8) nor an `M` row without a bearer (pattern 14). -/

open THEORY Relation BackwardGen

namespace MSIBag

variable {n : Nat}

/-- The forward invariant of `FormalMSI.SI`, at one address, on the bag model. -/
structure ψ_msi (i : MSIState n) : Prop where
  signal_state_rsS : ∀ c v, PCEvent.rsS v ∈ i.parent.queue_pci c →
    i.parent.shared_state c = Bstate.S ∧ (i.caches c).state = Bstate.I
  signal_state_rsM : ∀ c v, PCEvent.rsM v ∈ i.parent.queue_pci c →
    i.parent.shared_state c = Bstate.M ∧ (i.caches c).state = Bstate.I
  signal_state_rsIσ : ∀ c, CPEvent.rsIσ ∈ i.parent.queue_cip c →
    (i.caches c).state = Bstate.I ∧ i.parent.shared_state c = Bstate.S
  signal_state_rsIμ : ∀ c v, CPEvent.rsIμ v ∈ i.parent.queue_cip c →
    (i.caches c).state = Bstate.I ∧ i.parent.shared_state c = Bstate.M
  unique_rsS : ∀ c, (i.parent.queue_pci c).countP (fun e => isGrantS e = true) ≤ 1
  unique_rsM : ∀ c, (i.parent.queue_pci c).countP (fun e => isGrantM e = true) ≤ 1
  unique_rsIσ : ∀ c, (i.parent.queue_cip c).countP (fun e => isReleaseS e = true) ≤ 1
  unique_rsIμ : ∀ c, (i.parent.queue_cip c).countP (fun e => isReleaseM e = true) ≤ 1
  cache_belive_si : ∀ c, (i.caches c).state = Bstate.S → i.parent.shared_state c = Bstate.S
  cache_belive_mi : ∀ c, (i.caches c).state = Bstate.M → i.parent.shared_state c = Bstate.M
  parent_belive : ∀ c, i.parent.shared_state c = Bstate.I → (i.caches c).state = Bstate.I
  cross_signal_si : ∀ c v, CPEvent.rsIσ ∈ i.parent.queue_cip c → PCEvent.rsS v ∉ i.parent.queue_pci c
  cross_signal_mi : ∀ c v v', CPEvent.rsIμ v' ∈ i.parent.queue_cip c → PCEvent.rsM v ∉ i.parent.queue_pci c

/-! ## The definition of `badView`, written out

`badView` is imported from `MSI_bag_def` (`MSIBag.badView`); `badView_iff` below restates its
definition explicitly, one disjunct per line, and `Iff.rfl` checks that it is exactly the
imported one.

The view of the pair `(i, j)` (`msiView s i j`):
* `c0` = state of cache `i`;
* `d0` = parent row of `i`, `d1` = parent row of `j`;
* `m0` = `M` tokens in flight for `i` (`rsM` in `queue_pci i` + `rsIμ` in `queue_cip i`),
  saturated to `zero | one | many`;
* `s0` = `S` tokens in flight for `i` (`rsS` in `queue_pci i` + `rsIσ` in `queue_cip i`), saturated;
* `eq` = `decide (i = j)`: disjuncts without `eq` talk about a single index, those with
  `eq = false` about two distinct indices.

Next to each disjunct, after `⇒`: the fields of `ψ_msi` that `ψ_of_noBad` derives from that
pattern ("none" = `ψ_msi` does not rule the pattern out).

In short: patterns 1, 2, 4, 5, 6, 7 (single index) are enough to give all of `ψ_msi`; 3 follows
from `ψ_msi` but is not needed; 14 and 15 are single-index but `ψ_msi` does not rule them out
(`twoM` at the view `(0, 0)` is pattern 14); 8–13 (two indices) are out of reach of `ψ_msi`,
which quantifies over one index at a time (`twoM` at the view `(0, 1)` is pattern 8). -/

/-- **`badView`, explicitly** (the definition in `MSI_bag_def`, verbatim). -/
theorem badView_iff (v : MSIView.View) : badView v ↔
    -- ── single index: messages in flight ──────────────────────────────────────────────
    (v.m0 = .many                    -- 1.  two `M` tokens for `i` (two `rsM`, two `rsIμ`,
                                     --     or one `rsM` and one `rsIμ` together)
                                     --     ⇒ unique_rsM, unique_rsIμ, cross_signal_mi
    ∨ v.s0 = .many                   -- 2.  two `S` tokens for `i` (same with `rsS` / `rsIσ`)
                                     --     ⇒ unique_rsS, unique_rsIσ, cross_signal_si
    ∨ (v.m0 ≠ .zero ∧ v.s0 ≠ .zero)  -- 3.  an `M` token and an `S` token together for `i`
                                     --     ⇒ not used in ψ_of_noBad; ψ_msi rules it out
                                     --       anyway (signal_state_*: row `M` and row `S`)
    -- ── single index: a token in flight must be recorded by the row ───────────────────
    ∨ (v.m0 ≠ .zero ∧ v.d0 ≠ .M)     -- 4.  `M` token in flight for `i`, but the row of `i` is not `M`
                                     --     ⇒ signal_state_rsM / signal_state_rsIμ (row part)
    ∨ (v.s0 ≠ .zero ∧ v.d0 ≠ .S)     -- 5.  `S` token in flight for `i`, but the row of `i` is not `S`
                                     --     ⇒ signal_state_rsS / signal_state_rsIσ (row part)
    -- ── single index: a cache holding the token has nothing else in flight ────────────
    ∨ (v.c0 = .M ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .M))
                                     -- 6.  cache `i` in `M` with a token in flight for itself,
                                     --     or with the row of `i` different from `M`
                                     --     ⇒ cache_belive_mi, parent_belive,
                                     --       signal_state_* ("cache in I" part)
    ∨ (v.c0 = .S ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .S))
                                     -- 7.  cache `i` in `S` with a token in flight for itself,
                                     --     or with the row of `i` different from `S`
                                     --     ⇒ cache_belive_si, parent_belive,
                                     --       signal_state_* ("cache in I" part)
    -- ── two indices `i ≠ j`: parent rows ──────────────────────────────────────────────
    ∨ (v.eq = false ∧ v.d0 = .M ∧ v.d1 ≠ .I)   -- 8.  row `M` of `i` and row of `j` not `I`
                                               --     (`M` is exclusive)  ⇒ none (`twoM`)
    ∨ (v.eq = false ∧ v.d0 = .S ∧ v.d1 = .M)   -- 9.  row `S` of `i` and row `M` of `j`
                                               --     ⇒ none
    -- ── two indices `i ≠ j`: cache of `i` against row of `j` ──────────────────────────
    ∨ (v.eq = false ∧ v.c0 = .M ∧ v.d1 ≠ .I)   -- 10. cache `i` in `M` and row of `j` not `I`
                                               --     ⇒ none
    ∨ (v.eq = false ∧ v.c0 = .S ∧ v.d1 = .M)   -- 11. cache `i` in `S` and row `M` of `j`
                                               --     ⇒ none
    -- ── two indices `i ≠ j`: token in flight for `i` against row of `j` ───────────────
    ∨ (v.eq = false ∧ v.m0 ≠ .zero ∧ v.d1 ≠ .I) -- 12. `M` token in flight for `i` and row of `j` not `I`
                                               --     ⇒ none
    ∨ (v.eq = false ∧ v.s0 ≠ .zero ∧ v.d1 = .M) -- 13. `S` token in flight for `i` and row `M` of `j`
                                               --     ⇒ none
    -- ── single index: row recorded without a bearer (bag model only) ──────────────────
    ∨ (v.d0 = .M ∧ v.c0 ≠ .M ∧ v.m0 = .zero)   -- 14. row `M` of `i`, but neither cache `i` in `M`
                                               --     nor an `M` token in flight  ⇒ none
    ∨ (v.d0 = .S ∧ v.c0 ≠ .S ∧ v.s0 = .zero))  -- 15. row `S` of `i`, but neither cache `i` in `S`
                                               --     nor an `S` token in flight  ⇒ none
    := Iff.rfl

/-! ## The patterns of `badView` as injections into the disjunction -/

theorem bad1 {v : MSIView.View} (h : v.m0 = .many) : badView v := Or.inl h
theorem bad2 {v : MSIView.View} (h : v.s0 = .many) : badView v := Or.inr (Or.inl h)
theorem bad3 {v : MSIView.View} (h : v.m0 ≠ .zero ∧ v.s0 ≠ .zero) : badView v :=
  Or.inr (Or.inr (Or.inl h))
theorem bad4 {v : MSIView.View} (h : v.m0 ≠ .zero ∧ v.d0 ≠ .M) : badView v :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem bad5 {v : MSIView.View} (h : v.s0 ≠ .zero ∧ v.d0 ≠ .S) : badView v :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem bad6 {v : MSIView.View} (h : v.c0 = .M ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .M)) :
    badView v :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem bad7 {v : MSIView.View} (h : v.c0 = .S ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .S)) :
    badView v :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

/-! ## What the view `(c, c)` says when it has no bad pattern -/

/-- The single-index facts read from the view `(c, c)`. -/
structure KK (i : MSIState n) (c : Fin n) : Prop where
  mu_le : muMsgs i.parent c ≤ 1
  sig_le : sigMsgs i.parent c ≤ 1
  mu_sig : muMsgs i.parent c ≠ 0 → sigMsgs i.parent c = 0
  mu_row : muMsgs i.parent c ≠ 0 → i.parent.shared_state c = Bstate.M
  sig_row : sigMsgs i.parent c ≠ 0 → i.parent.shared_state c = Bstate.S
  cacheM : (i.caches c).state = Bstate.M →
    muMsgs i.parent c = 0 ∧ sigMsgs i.parent c = 0 ∧ i.parent.shared_state c = Bstate.M
  cacheS : (i.caches c).state = Bstate.S →
    muMsgs i.parent c = 0 ∧ sigMsgs i.parent c = 0 ∧ i.parent.shared_state c = Bstate.S

theorem kk_of_noBad {i : MSIState n} {c : Fin n} (h : ¬ badView (msiView i c c)) : KK i c := by
  have m0z : (msiView i c c).m0 ≠ .zero ↔ muMsgs i.parent c ≠ 0 := by
    show Cnt.ofCount (muMsgs i.parent c) ≠ .zero ↔ _
    rw [Ne, Cnt.ofCount_eq_zero]
  have s0z : (msiView i c c).s0 ≠ .zero ↔ sigMsgs i.parent c ≠ 0 := by
    show Cnt.ofCount (sigMsgs i.parent c) ≠ .zero ↔ _
    rw [Ne, Cnt.ofCount_eq_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hlt
    exact h (bad1 (show Cnt.ofCount (muMsgs i.parent c) = .many from
      (Cnt.ofCount_eq_many _).2 (by omega)))
  · by_contra hlt
    exact h (bad2 (show Cnt.ofCount (sigMsgs i.parent c) = .many from
      (Cnt.ofCount_eq_many _).2 (by omega)))
  · intro hmu
    by_contra hsig
    exact h (bad3 ⟨m0z.2 hmu, s0z.2 hsig⟩)
  · intro hmu
    by_contra hrow
    exact h (bad4 ⟨m0z.2 hmu, hrow⟩)
  · intro hsig
    by_contra hrow
    exact h (bad5 ⟨s0z.2 hsig, hrow⟩)
  · intro hM
    refine ⟨?_, ?_, ?_⟩
    · by_contra hmu; exact h (bad6 ⟨hM, Or.inl (m0z.2 hmu)⟩)
    · by_contra hsig; exact h (bad6 ⟨hM, Or.inr (Or.inl (s0z.2 hsig))⟩)
    · by_contra hrow; exact h (bad6 ⟨hM, Or.inr (Or.inr hrow)⟩)
  · intro hS
    refine ⟨?_, ?_, ?_⟩
    · by_contra hmu; exact h (bad7 ⟨hS, Or.inl (m0z.2 hmu)⟩)
    · by_contra hsig; exact h (bad7 ⟨hS, Or.inr (Or.inl (s0z.2 hsig))⟩)
    · by_contra hrow; exact h (bad7 ⟨hS, Or.inr (Or.inr hrow)⟩)

/-! ## Counters -/

theorem grantM_pos {q : Multiset PCEvent} {v : Value} (h : PCEvent.rsM v ∈ q) :
    0 < q.countP (fun e => isGrantM e = true) :=
  Multiset.countP_pos.2 ⟨_, h, rfl⟩
theorem grantS_pos {q : Multiset PCEvent} {v : Value} (h : PCEvent.rsS v ∈ q) :
    0 < q.countP (fun e => isGrantS e = true) :=
  Multiset.countP_pos.2 ⟨_, h, rfl⟩
theorem releaseM_pos {q : Multiset CPEvent} {v : Value} (h : CPEvent.rsIμ v ∈ q) :
    0 < q.countP (fun e => isReleaseM e = true) :=
  Multiset.countP_pos.2 ⟨_, h, rfl⟩
theorem releaseS_pos {q : Multiset CPEvent} (h : CPEvent.rsIσ ∈ q) :
    0 < q.countP (fun e => isReleaseS e = true) :=
  Multiset.countP_pos.2 ⟨_, h, rfl⟩

/-- A cache that is neither in `M` nor in `S` is in `I`. -/
theorem state_I_of_ne {b : Bstate} (hM : b ≠ Bstate.M) (hS : b ≠ Bstate.S) : b = Bstate.I := by
  cases b with
  | M => exact absurd rfl hM
  | S => exact absurd rfl hS
  | I => rfl

/-! ## The theorem -/

/-- **`badView` implies `ψ_msi`.** Only patterns 1, 2, 4, 5, 6, 7, on the view `(c, c)`. -/
theorem ψ_of_noBad {i : MSIState n} (hb : ∀ k k', ¬ badView (msiView i k k')) : ψ_msi i := by
  have kk : ∀ c, KK i c := fun c => kk_of_noBad (hb c c)
  -- a cache with an `M` token in flight is in `I`
  have cacheI_of_mu : ∀ c, muMsgs i.parent c ≠ 0 → (i.caches c).state = Bstate.I := by
    intro c hmu
    refine state_I_of_ne (fun hM => hmu ((kk c).cacheM hM).1) (fun hS => hmu ((kk c).cacheS hS).1)
  have cacheI_of_sig : ∀ c, sigMsgs i.parent c ≠ 0 → (i.caches c).state = Bstate.I := by
    intro c hsig
    refine state_I_of_ne (fun hM => hsig ((kk c).cacheM hM).2.1) (fun hS => hsig ((kk c).cacheS hS).2.1)
  have mu_of_grant : ∀ c v, PCEvent.rsM v ∈ i.parent.queue_pci c → muMsgs i.parent c ≠ 0 := by
    intro c v h; unfold muMsgs; have := grantM_pos h; omega
  have mu_of_release : ∀ c v, CPEvent.rsIμ v ∈ i.parent.queue_cip c → muMsgs i.parent c ≠ 0 := by
    intro c v h; unfold muMsgs; have := releaseM_pos h; omega
  have sig_of_grant : ∀ c v, PCEvent.rsS v ∈ i.parent.queue_pci c → sigMsgs i.parent c ≠ 0 := by
    intro c v h; unfold sigMsgs; have := grantS_pos h; omega
  have sig_of_release : ∀ c, CPEvent.rsIσ ∈ i.parent.queue_cip c → sigMsgs i.parent c ≠ 0 := by
    intro c h; unfold sigMsgs; have := releaseS_pos h; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c v h
    exact ⟨(kk c).sig_row (sig_of_grant c v h), cacheI_of_sig c (sig_of_grant c v h)⟩
  · intro c v h
    exact ⟨(kk c).mu_row (mu_of_grant c v h), cacheI_of_mu c (mu_of_grant c v h)⟩
  · intro c h
    exact ⟨cacheI_of_sig c (sig_of_release c h), (kk c).sig_row (sig_of_release c h)⟩
  · intro c v h
    exact ⟨cacheI_of_mu c (mu_of_release c v h), (kk c).mu_row (mu_of_release c v h)⟩
  · intro c; have := (kk c).sig_le; unfold sigMsgs at this; omega
  · intro c; have := (kk c).mu_le; unfold muMsgs at this; omega
  · intro c; have := (kk c).sig_le; unfold sigMsgs at this; omega
  · intro c; have := (kk c).mu_le; unfold muMsgs at this; omega
  · intro c hS; exact ((kk c).cacheS hS).2.2
  · intro c hM; exact ((kk c).cacheM hM).2.2
  · intro c hI
    refine state_I_of_ne (fun hM => ?_) (fun hS => ?_)
    · have := ((kk c).cacheM hM).2.2; rw [hI] at this; cases this
    · have := ((kk c).cacheS hS).2.2; rw [hI] at this; cases this
  · intro c v hrel hgr
    have h1 := releaseS_pos hrel
    have h2 := grantS_pos hgr
    have := (kk c).sig_le; unfold sigMsgs at this; omega
  · intro c v v' hrel hgr
    have h1 := releaseM_pos hrel
    have h2 := grantM_pos hgr
    have := (kk c).mu_le; unfold muMsgs at this; omega

/-! ## The converse is false -/

/-- Two `M` rows, caches in `I`, no messages: `ψ_msi` holds, the view `(0, 1)` is bad
(pattern 8). -/
def twoM : MSIState 2 :=
  ⟨fun _ => ⟨Bstate.I, 0, 0, 0, ⟨[], []⟩⟩,
   ⟨0, fun _ => Bstate.M, fun _ => 0, fun _ => 0⟩⟩

theorem ψ_twoM : ψ_msi twoM := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro c v h; simp [twoM] at h)
    | (intro c h; simp [twoM] at h)
    | (intro c; simp [twoM])

theorem twoM_bad : badView (msiView twoM 0 1) := by
  unfold badView msiView muMsgs sigMsgs
  decide

/-- **`ψ_msi` does not imply the absence of bad views.** -/
theorem ψ_not_noBad : ∃ s : MSIState 2, ψ_msi s ∧ ∃ i j, badView (msiView s i j) :=
  ⟨twoM, ψ_twoM, 0, 1, twoM_bad⟩

end MSIBag

#print axioms MSIBag.ψ_of_noBad
#print axioms MSIBag.ψ_not_noBad
