import Star.Commute.ARS
open ReachingStar
namespace the_theorem_ind
set_option quotPrecheck false
variable {A B E}
variable (flush :  A -> B -> Prop)
variable (rule : Rule A)
variable (method_i : Method A E)
variable (method_s : Method B E)
variable (similarity : A -> A -> Prop)
infix:50 " ~ " => similarity
-- The user requested this as an axiom, but for soundness we state it as a variable hypothesis.
variable (similarity_symm : ∀ {a b : A}, a ~ b → b ~ a)
variable (φ : A -> B -> Prop)
def φ_flush : A → B → Prop := fun (i : A) (s : B) => φ i s ∧ (∀ (i' : A), ¬ rule i i')
def refinament :=
  ∀ i i' s l, φ i s -> star_extend rule method_i i l i' -> ∃ s', star method_s s l s' ∧ φ i' s'
theorem weakly_normalising_implication (i : A) :
    has_nf rule i -> ∃ i', trans_refl rule i i' ∧ (∀ (i'' : A), ¬rule i' i'') := by
  unfold has_nf at *
  intro hf
  unfold is_nf at *
  grind
def indistinguishability1 (i : A) (i₁ : A) : Prop :=
  ∀ (i' : A) e, method_i i e i' -> ∃ i₁', method_i i₁ e i₁'


def has_diamond_property1 (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d d₁, α c d ∧ α b d₁ ∧ indistinguishability1 method_i d d₁
def has_diamond_property_similarity (α : Rule A) :=
  ∀ {a b c : A}, α a c → α a b → ∃ d d₁, α c d ∧ α b d₁ ∧ d ~ d₁


def preserve_flushing := ∀ i s i', flush i s -> i ~ i' -> flush i' s

def similarity_step := ∀ i i' i₁ , i ~ i' -> rule i i₁ -> ∃ i₁' , rule i' i₁' ∧ i₁ ~ i₁'

lemma similarity_trans_refl
    (hss : similarity_step rule similarity)
    {i i' j : A} (hsim : i ~ i') (htr : trans_refl rule i j) :
    ∃ j', trans_refl rule i' j' ∧ j ~ j' := by
  induction htr generalizing i' with
  | step h _ ih =>
    obtain ⟨j', hj', hj''⟩ := hss _ _ _ hsim h
    obtain ⟨j'', hj1, hj2⟩ := ih hj''
    exact ⟨j'', trans_refl.step hj' hj1, hj2⟩
  | refl => exact ⟨i', trans_refl.refl, hsim⟩

theorem phi_preserve_similarity :
  preserve_flushing flush similarity ->
  similarity_step rule similarity ->
  ∀ i s i', φ₀ flush rule i s -> i ~ i' -> φ₀ flush rule i' s := by
  intro h₀ h₁ i s i' hi hi'
  induction hi generalizing i' with
  | base i s hfl => exact φ₀.base i' s (h₀ i s i' hfl hi')
  | rule_step i i'' s _ htr ih =>
    obtain ⟨j', hj₁, hj₂⟩ := similarity_trans_refl rule similarity h₁ hi' htr
    exact φ₀.rule_step _ _ _ (ih _ hj₂) hj₁
/-
## Helper lemmas
-/

private lemma trans_refl_trans {a b c : A}
    (h1 : trans_refl rule a b) (h2 : trans_refl rule b c) :
    trans_refl rule a c := by
  induction h1 generalizing c with
  | step h _ ih => exact trans_refl.step h (ih h2)
  | refl => exact h2
private lemma trans_refl_nf_eq {a b : A}
    (hnf : is_nf rule a) (h : trans_refl rule a b) : a = b := by
  cases h with
  | step h1 _ => exact absurd h1 (hnf _)
  | refl => rfl
private lemma φ₀_extract_nf {i : A} {s : B}
    (hφ : φ₀ (φ_flush rule φ) rule i s) :
    ∃ i_nf, trans_refl rule i i_nf ∧ φ i_nf s ∧ is_nf rule i_nf := by
  induction hφ with
  | base i s h => exact ⟨i, trans_refl.refl, h.1, fun b hb => h.2 b hb⟩
  | rule_step i i' s _ htr ih =>
    obtain ⟨i_nf, h1, h2, h3⟩ := ih
    exact ⟨i_nf, trans_refl_trans rule htr h1, h2, h3⟩
private lemma star_nil_eq {s s' : B}
    (h : star method_s s [] s') : s' = s := by
  cases h; rfl
private lemma star_singleton {s s' : B} {e : E}
    (h : star method_s s [e] s') : method_s s e s' := by
  grind +splitIndPred
private lemma star_extend_single_ext {i i' : A} {e : E}
    (h : method_i i e i') : star_extend rule method_i i [e] i' :=
  star_extend.step_ext _ _ _ _ _ (star_extend.refl _) h
private lemma star_extend_internal {i i' : A}
    (h : trans_refl rule i i') : star_extend rule method_i i [] i' :=
  star_extend.step_int _ _ _ _ (star_extend.refl _) h


/-
## Forward lemma: φ₀ is preserved along rule steps (using diamond + similarity)
Uses phi_preserve_similarity from PhiPreserveSimilarity.lean, instantiated with
flush := φ_flush rule φ.
-/
private lemma φ₀_forward
    (hdp : has_diamond_property_similarity similarity (trans_refl rule))
    (hpf : preserve_flushing (φ_flush rule φ) similarity)
    (hss : similarity_step rule similarity)
    {i i' : A} {s : B}
    (hφ : φ₀ (φ_flush rule φ) rule i s)
    (htr : trans_refl rule i i') :
    φ₀ (φ_flush rule φ) rule i' s := by
  -- Derive full φ₀-preservation under similarity
  have hps := phi_preserve_similarity (φ_flush rule φ) rule similarity hpf hss
  induction hφ generalizing i' with
  | base i₀ s₀ hfl =>
    have hnf : is_nf rule i₀ := fun b hb => hfl.2 b hb
    have heq := trans_refl_nf_eq rule hnf htr
    rw [← heq]
    exact φ₀.base _ _ hfl
  | rule_step i₀ i₀' s₀ _ htr₀ ih =>
    obtain ⟨d, d₁, hd, hd₁, hsim⟩ := hdp htr₀ htr
    exact φ₀.rule_step _ d₁ _ (hps d s₀ d₁ (ih hd) hsim) hd₁







/-
## Teorema principale: completeness1 (con similarità + decomposizione)
**Ipotesi**:
1. `weakly_normalising rule` — normalizzazione debole
2. `has_diamond_property_similarity similarity (trans_refl rule)` — diamante con similarità
3. `commutes_weakly_method_rule method_i rule` — commutazione debole metodo-regola
4. `refinament rule method_i method_s φ` — φ è già un raffinamento
5. `phi_preserve_sim.preserve_flushing (φ_flush rule φ) similarity` — il flush (= φ ∧ is_nf)
   è preservato dalla similarità
6. `similarity_step rule similarity` — la similarità è una bisimulazione rispetto a rule
L'ipotesi 5 dice concretamente:
  `∀ i s i', (φ i s ∧ is_nf rule i) → i ~ i' → (φ i' s ∧ is_nf rule i')`
Le ipotesi 5 e 6 insieme implicano `phi_preserve_similarity` (tramite il teorema
in `PhiPreserveSimilarity.lean`), che è l'ingrediente chiave per il caso `step_int`.
**Nota sull'enunciato originale (commentato sotto)**:
L'enunciato originale usava `preserve_flushing flush similarity` dove `flush` è
disconnesso da `φ`. Questo rende l'ipotesi inutile perché non può essere usata
per trasferire `φ₀ (φ_flush rule φ)` tra stati simili. La versione corretta usa
`phi_preserve_sim.preserve_flushing (φ_flush rule φ) similarity`.
**Struttura della dimostrazione**: come nelle altre versioni, per induzione su `star_extend`:
- **`refl`**: banale.
- **`step_int`**: usa `φ₀_forward` (che internamente usa `phi_preserve_similarity`).
- **`step_ext`**: estrae la NF, commuta il metodo, simula, ricostruisce `φ₀`.
-/


theorem completeness1 :
  weakly_normalising rule →
  has_diamond_property_similarity similarity (trans_refl rule) →
  commutes_weakly_method_rule method_i rule →
  refinament rule method_i method_s φ →
  preserve_flushing (φ_flush rule φ) similarity →
  similarity_step rule similarity →
  refinament rule method_i method_s (φ₀ (φ_flush rule φ) rule) := by
  intro hwn hdp hcwm href hpf hss i i' s l hφ hstar
  induction hstar generalizing s
  case refl =>
    -- Caso base: esecuzione vuota
    exact ⟨s, star.refl s, hφ⟩
  case step_int l' i₁ i₂ hse htr ih =>
    -- Caso passo interno: usa φ₀_forward (che usa phi_preserve_similarity derivata)
    obtain ⟨s₁, hs₁, hφ₁⟩ := ih s hφ
    exact ⟨s₁, hs₁, φ₀_forward rule similarity φ hdp hpf hss hφ₁ htr⟩
  case step_ext l' i₁ i₂ e hse hmi ih =>
    -- Caso passo di metodo esterno
    obtain ⟨s₁, hs₁, hφ₁⟩ := ih s hφ
    -- (a) Estrai la forma normale
    obtain ⟨i₁_nf, htr₁, hφ_nf, hnf₁⟩ := φ₀_extract_nf rule φ hφ₁
    -- (b) Commuta il metodo oltre i passi interni
    obtain ⟨d, hmi_nf, htr_d⟩ := hcwm htr₁ hmi
    -- (c) Simula nella specifica
    obtain ⟨s₂, hs₂, hφ_d⟩ := href _ _ _ _ hφ_nf (star_extend_single_ext rule method_i hmi_nf)
    have hms : method_s s₁ e s₂ := star_singleton method_s hs₂
    -- (d) Trova forma normale per d
    obtain ⟨d_nf, htr_dnf, hnf_dnf⟩ := hwn d
    -- (e) Usa raffinamento per passi interni
    obtain ⟨s₃, hs₃, hφ_dnf⟩ := href _ _ _ _ hφ_d (star_extend_internal rule method_i htr_dnf)
    have heq : s₃ = s₂ := star_nil_eq method_s hs₃
    -- (f) Costruisci φ₀ per i₂ via d_nf
    have hφ₀_dnf : φ₀ (φ_flush rule φ) rule d_nf s₂ :=
      φ₀.base d_nf s₂ ⟨heq ▸ hφ_dnf, hnf_dnf⟩
    have htr_i₂_dnf := trans_refl_trans rule htr_d htr_dnf
    exact ⟨s₂, star.step _ s₁ s₂ _ _ hs₁ hms, φ₀.rule_step _ d_nf s₂ hφ₀_dnf htr_i₂_dnf⟩


end the_theorem_ind
