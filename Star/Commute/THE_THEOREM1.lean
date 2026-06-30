import Star.Commute.ARS

open ReachingStar
open ReachingStar

namespace the_theorem1

variable {A B E}

variable (flush :  A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)

--This is what we don't have to use if you prove the theorem without enought_star
def method_deterministic := ∀ s s' s'' e,  method_s s e s' ->  method_s s e s'' -> s' = s''

variable (φ : A -> B -> Prop)

def φ_flush : A → B → Prop := fun (i : A) (s : B) => φ i s ∧ (∀ (i' : A), ¬ rule i i')

def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'

theorem weakly_normalising_implication (i : A) : has_nf rule i -> ∃ i', trans_refl rule i i' ∧  (∀ (i'' : A), ¬rule i' i'') := by
        unfold has_nf at *
        intro hf
        unfold is_nf at *
        grind


theorem completeness:
  weakly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ_ind (φ_flush rule φ) rule) := by
    intro h1 h2 h3 h4
    unfold refinament at *
    intro i i' s l
    apply enough_star <;> try assumption
    . unfold relation_flush
      intro _ _ _ h5 h6
      unfold φ_flush at *
      cases h6
      . rename_i i1 _ _
        rcases h5 with ⟨ h5, h5'⟩; specialize h5' i1
        grind
      . assumption
    . unfold relation_flush_method
      intro ii ii' _ s' e h5 h6 h7
      unfold φ_flush at *
      rcases h5 with ⟨ h5, h5'⟩
      unfold weakly_normalising at *
      specialize h1 ii'
      have H := weakly_normalising_implication rule ii'
      specialize H h1
      rcases H with ⟨ i'', H⟩
      constructor; rotate_left
      . exact i''
      . constructor
        . grind
        . constructor
          . rcases H with ⟨ H, H'⟩
            specialize h4 _ i'' _ [e] h5
            have H : star_extend rule method_i ii [e] i'' := by
              apply star_extend.step_int; rotate_right 2
              . assumption
              . apply star_extend.step_ext; rotate_right 2
                . assumption
                . apply star_extend.refl
            specialize h4 H
            rcases h4 with ⟨ s'', h4, h4'⟩
            cases h4; rename_i s3 h4 h44
            cases h4
            admit
          . grind
    . unfold relation_method
      intro i1 i2 s1 e h5 h6
      unfold φ_flush at *
      rcases h5 with ⟨ h5, h5'⟩
      specialize h4 _ i2 _ [e] h5
      have H : star_extend rule method_i i1 [e] i2 := by
        apply star_extend.step_ext; rotate_right
        . exact i1
        . apply star_extend.refl
        . assumption
      specialize h4 H
      rcases h4 with ⟨ s'', h4, h4'⟩
      cases h4; rename_i H _; cases H
      grind

/-
We prove the completeness theorem for the refinement of abstract reduction systems.
The proof demonstrates that if a rule is weakly normalising, confluent (via the diamond
property), and commutes weakly with the implementation method, then the refinement
property lifts to the observational equivalence relation φ₀.
Note: The proof strategy using enough_star suggested in the prompt requires
relation_flush_method, which implies a form of determinism for method_s that is not
guaranteed by the premises. Therefore, we provided a direct proof using the confluence
and normalization properties to construct the required simulation.
-/
/-!
## A cleaner, more readable proof of completeness (`completeness1`)
The `admit` above shows that the `enough_star` route forces a determinism assumption on
`method_s` that the hypotheses do not provide.  Below we give a direct proof of the same
statement.  It uses only a handful of small, self-contained helper lemmas and reads as a
straight line of reasoning (see `completeness1`).
-/
/-- Transitivity of the reflexive–transitive closure `trans_refl`. -/
theorem trans_refl_trans {a b c : A} :
    trans_refl rule a b → trans_refl rule b c → trans_refl rule a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact trans_refl.step h (ih hbc)
/-- A pure rule path is an empty (label-free) extended run. -/
theorem trans_refl_implies_star_extend {i i' : A} :
    trans_refl rule i i' → star_extend rule method_i i [] i' :=
  fun h => star_extend.step_int _ _ _ _ (star_extend.refl i) h
/-- From `φ₀ (φ_flush rule φ)` we can read off a reachable normal form on which `φ` holds. -/
-- theorem phi0_implies_exists_base {i : A} {s : B} :
--     φ₀ (φ_flush rule φ) rule i s →
--     ∃ i_base, trans_refl rule i i_base ∧ is_nf rule i_base ∧ φ i_base s := by
--   intro h
--   induction h with
--   | base i s hbase =>
--       unfold φ_flush at *
--       exact ⟨i, trans_refl.refl, hbase.2, hbase.1⟩
--   | rule_step i i' s _ hstep ih =>
--       obtain ⟨i_base, h1, h2, h3⟩ := ih
--       exact ⟨i_base, trans_refl_trans rule hstep h1, h2, h3⟩

theorem phi0_implies_exists_base {i : A} {s : B} :
    φ₀ (φ_flush rule φ) rule i s →
    ∃ i_base, trans_refl rule i i_base ∧ φ i_base s := by
  intro h
  induction h with
  | base i s hbase =>
      unfold φ_flush at *
      exact ⟨i, trans_refl.refl,  hbase.1⟩
  | rule_step i i' s _ hstep ih =>
      obtain ⟨i_base, h1, h3⟩ := ih
      exact ⟨i_base, trans_refl_trans rule hstep h1, h3⟩
/-- Confluence for extended runs: a rule path out of the start can be pushed across a whole
run.  This is the diamond property for internal `rule` steps together with the weak
commutation of `method_i` with `rule`, lifted to `star_extend` by induction. -/

theorem star_extend_confluence
    (h_diamond : has_diamond_property (trans_refl rule))
    (h_comm : commutes_weakly_method_rule method_i rule) :
    ∀ {i l i'}, star_extend rule method_i i l i' → ∀ {i_nf}, trans_refl rule i i_nf →
    ∃ d, star_extend rule method_i i_nf l d ∧ trans_refl rule i' d := by
  intro i l i' h
  induction h with
  | refl => intro i_nf hnf; exact ⟨i_nf, star_extend.refl _, hnf⟩
  | step_int l s' s'' hstar hrule ih =>
      intro i_nf hnf
      obtain ⟨d, hd1, hd2⟩ := ih hnf
      obtain ⟨e, he1, he2⟩ := h_diamond hrule hd2
      exact ⟨e, star_extend.step_int _ _ _ _ hd1 he2, he1⟩
  | step_ext l s' s'' ev hstar hmeth ih =>
      intro i_nf hnf
      obtain ⟨d, hd1, hd2⟩ := ih hnf
      obtain ⟨d', hd3, hd4⟩ := h_comm hd2 hmeth
      exact ⟨d', star_extend.step_ext _ _ _ _ _ hd1 hd3, hd4⟩
/-- `φ` is preserved along pure rule paths (a label-free instance of refinement). -/
theorem φ_preserved_under_rule
    (h_refine : refinament rule method_i method_s φ) {i i' : A} {s : B} :
    φ i s → trans_refl rule i i' → φ i' s := by
  intro hphi htrans
  unfold refinament at *
  obtain ⟨s', hstar0, hphi'⟩ :=
    h_refine i i' s [] hphi (trans_refl_implies_star_extend rule method_i htrans)
  cases hstar0
  exact hphi'


-- theorem completeness1:
--   weakly_normalising rule ->
--   has_diamond_property (trans_refl rule) ->
--   commutes_weakly_method_rule method_i rule ->
--   refinament rule method_i method_s φ ->
--   refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
--   intro h_weak h_diamond h_comm h_refine
--   intro i i' s l hφ hstar
--   -- 1. extract a normal form `i_base` reachable from `i` with `φ i_base s`.
--   obtain ⟨i_base, hi_base, hiφ⟩ := phi0_implies_exists_base rule φ hφ
--   -- 2. push the run of `method_i` from `i` onto `i_base` (confluence + commutation).
--   have H := star_extend_confluence rule method_i h_diamond h_comm hstar hi_base
--   obtain ⟨d, hrun, hi'd⟩ := H
--   -- 3. simulate that run on the spec side, starting from `s`.
--   unfold refinament at *
--   obtain ⟨s', hspec, hφd⟩ := h_refine i_base d s l hiφ hrun
--   -- 4. normalise `d`, and transport `φ` along the resulting rule path.
--   unfold weakly_normalising at *; unfold has_nf at *
--   obtain ⟨d_nf, hd_nf, hd_nf_isnf⟩ := h_weak d
--   have hφnf : φ d_nf s' :=
--     φ_preserved_under_rule rule method_i method_s φ h_refine hφd hd_nf
--   -- 5. conclude: `s'` works, and `φ₀` holds at `i'` via the normal form `d_nf`.
--   refine ⟨s', hspec, ?_⟩
--   apply φ₀.rule_step _ d_nf
--   . apply φ₀.base
--     refine ⟨hφnf, hd_nf_isnf⟩
--   . exact trans_refl_trans rule hi'd hd_nf

theorem completeness1:
  weakly_normalising rule ->
  has_diamond_property (trans_refl rule) ->
  commutes_weakly_method_rule method_i rule ->
  refinament rule method_i method_s φ ->
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
  intro h_weak h_diamond h_comm h_refine
  unfold refinament at *
  intro i i' s l hφ hstar
  -- 1. extract a state `i_base` reachable from `i` with `φ i_base s`.
  obtain ⟨i_base, hi_base, hiφ⟩ := phi0_implies_exists_base rule φ hφ
  -- 2. push the run of `method_i` from `i` onto `i_base` (confluence + commutation).
  obtain ⟨d, hrun, hi'd⟩ :=
    star_extend_confluence rule method_i h_diamond h_comm hstar hi_base
  -- 3. FIRST use of refinement: simulate that run on the spec side, starting from `s`.
  obtain ⟨s', hspec, hφd⟩ := h_refine i_base d s l hiφ hrun
  -- 4. normalise `d`.
  obtain ⟨d_nf, hd_nf, hd_nf_isnf⟩ := h_weak d
  -- 5. SECOND use of refinement, on the empty-labelled rule path `d ⟶* d_nf`,
  --    transporting `φ` to the normal form `d_nf` (no `φ_preserved_under_rule`).
  obtain ⟨s'', hspec', hφnf⟩ :=
    h_refine d d_nf s' [] hφd (trans_refl_implies_star_extend rule method_i hd_nf)
  cases hspec'  -- `star method_s s' [] s''` forces `s'' = s'`
  -- 6. conclude: `s'` works, and `φ₀` holds at `i'` via the normal form `d_nf`.
  refine ⟨s', hspec, ?_⟩
  apply φ₀.rule_step _ d_nf
  · apply φ₀.base
    exact ⟨hφnf, hd_nf_isnf⟩
  · exact trans_refl_trans rule hi'd hd_nf


theorem φ_flus_smaller_φ : ∀ i s, φ_flush rule φ i s -> φ i s:= by
  intro i s h
  unfold φ_flush at *
  grind


#print axioms completeness1
end the_theorem1
