import StarExperimental.MSI_bag_flush_proof

/-! # `MSI_normale`: inclusione delle tracce nel modo classico (simulazione in avanti)

Modello bag (`MSI_bag_def.lean`). Una relazione `φ` tra stato dell'implementazione e stato dello
spec, conservata da ogni passo interno (spec fermo) e da ogni passo esterno (spec che fa lo stesso
evento), nello stile di `FormalMSI.SI`: `φ`, `φ_init`, `enough_internal`, `enough`, `enough_star`,
`trace_inclusion`.

`φ i s` è fatta di `badView`, `SVal`, `flush` e `synced`:
* `bad`: nessuna vista cattiva in `i` (i 15 pattern, il risultato della tattica);
* `sync`: `synced i` (l'`Inv` del setup della tattica);
* `sval`: l'invariante `SVal` (copie `S` e grant `rsS` valgono quanto il parent);
* `fl`: `flush` *ancorato in avanti*: da `i` si arriva con passi interni a uno stato flushed
  rispetto a `s`. È il legame con lo spec. L'ancora dietro ("si viene da uno stato flushed")
  è impossibile, si rompe alla store (`MSI_normale_flush.lean`); quella avanti si conserva grazie
  al drenaggio `reach_canon` di `MSI_bag_confluent.lean`;
* `good`: `Good i`, il trasporto di `bad` e `sync` lungo i passi. Serve perché la tattica non
  esporta la chiusura dei pattern: da `¬ badView i` e un passo `i → i'` non si ricava
  `¬ badView i'` se non passando per la forma raggiungibile (`shape`). `bad` e `sync` sono
  ricavabili da `good` (`noBad_of_good`, `synced_of_good`) e restano espliciti per leggibilità.

Nelle prove il valore logico `val` fa da tramite: `fl` equivale, su stati buoni, a
`val i = s.memory` più le `extqueue` uguali (`val_of_anchor`, `flush_canon`). -/

open THEORY Relation
open ReachingStar (trans_refl)

namespace MSIBag.Normale

variable {n : Nat}

/-- La relazione di simulazione: `badView` + `synced` + `SVal` + `flush` (ancorato in avanti). -/
structure φ (i : MSIState n) (s : SeqState n) : Prop where
  bad  : ∀ k k', ¬ badView (msiView i k k')
  sync : synced i
  sval : SVal i
  fl   : ∃ i₁, trans_refl (msi_rule n) i i₁ ∧ flush i₁ s
  good : Good i

/-! ## Il tramite: `val` -/

/-- Lo stato canonico di `x` è flushed rispetto a `s` se `val x` è la memoria di `s` e le
`extqueue` coincidono. -/
theorem flush_canon {x : MSIState n} {s : SeqState n} (hm : val x = s.memory)
    (hext : ∀ k, (x.caches k).extqueue = s.extqueue k) : flush (canon x (val x)) s :=
  ⟨⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, hm⟩, fun k => hext k⟩

/-- Dall'ancora: il valore logico di `i` è la memoria di `s`, e le `extqueue` coincidono. -/
theorem val_of_anchor {i : MSIState n} {s : SeqState n} (hg : Good i)
    (hfl : ∃ i₁, trans_refl (msi_rule n) i i₁ ∧ flush i₁ s) :
    val i = s.memory ∧ ∀ k, (i.caches k).extqueue = s.extqueue k := by
  obtain ⟨i₁, h, hf⟩ := hfl
  exact ⟨(val_trans hg h).symm.trans (val_of_flush0 hf.1),
         fun k => (ext_trans h k).symm.trans (hf.2 k)⟩

/-- L'ancora da `val`: lo stato canonico è raggiungibile ed è flushed. -/
theorem anchor_of_val {i : MSIState n} {s : SeqState n} (hg : Good i) (hm : val i = s.memory)
    (hext : ∀ k, (i.caches k).extqueue = s.extqueue k) :
    ∃ i₁, trans_refl (msi_rule n) i i₁ ∧ flush i₁ s :=
  ⟨canon i (val i), reach_canon hg, flush_canon hm hext⟩

/-! ## Le prove -/

/-- Lo stato iniziale è in relazione con `seq_init`: è flushed (`msi_relation_init`). -/
theorem φ_init : φ (default : MSIState n) (seq_init n) :=
  ⟨noBad_of_good good_default, synced_of_good good_default, sval_default,
   ⟨default, trans_refl.refl, msi_relation_init⟩, good_default⟩

/-- I passi interni conservano `φ` con lo spec fermo. -/
theorem enough_internal {i i' : MSIState n} {s : SeqState n} {e : MSIInternalEvent n}
    (hφ : φ i s) (h : msi_step_internal i e i') : φ i' s := by
  have hg' : Good i' := good_step hφ.good h
  obtain ⟨hm, hext⟩ := val_of_anchor hφ.good hφ.fl
  refine ⟨noBad_of_good hg', synced_of_good hg', sval_step (noBadFacts_of_good hφ.good) hφ.sval h,
          anchor_of_val hg' ?_ ?_, hg'⟩
  · rw [val_step hφ.good h, hm]
  · intro k; rw [ext_step h k, hext k]

/-- Ogni passo esterno dell'implementazione è riprodotto dallo spec, e `φ` si conserva. -/
theorem enough {i i' : MSIState n} {s : SeqState n} {e : MSIExternalEvent n}
    (hφ : φ i s) (h : msi_step_external i e i') : ∃ s', seq_step s e s' ∧ φ i' s' := by
  obtain ⟨_, _, hv, hfl, hg⟩ := hφ
  obtain ⟨hm, hext⟩ := val_of_anchor hg hfl
  have hg' : Good i' := good_step_ext hg h
  have hv' : SVal i' := sval_step_ext (noBadFacts_of_good hg) hv h
  -- lo spec fa lo stesso passo, e la memoria che ne risulta è `val i'`
  have key : ∃ s', seq_step s e s' ∧ val i' = s'.memory := by
    cases e with
    | cache ev k =>
      obtain ⟨hne, hst⟩ := val_ext hg h
      cases h with
      | cache _ c' _ hc' =>
        cases hc' with
        | ld_rq => exact ⟨_, seq_step.ld_rq s k, by rw [hne (by intro h; cases h), hm]⟩
        | st_rq v => exact ⟨_, seq_step.st_rq s v k, by rw [hne (by intro h; cases h), hm]⟩
        | ld_rq_data_available1 rst hrq hS =>
          have hval : (i.caches k).value = s.memory := (val_of_S hg hv hS).trans hm
          exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq) hval.symm,
                 by rw [hne (by intro h; cases h), hm]⟩
        | ld_rq_data_available rst hrq hM =>
          have hval : (i.caches k).value = s.memory := (val_of_M hg hM).trans hm
          exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq) hval.symm,
                 by rw [hne (by intro h; cases h), hm]⟩
        | st_rq_M_state v rst hrq hM =>
          refine ⟨_, seq_step.st_rs s v k rst (by rw [← hext k]; exact hrq), ?_⟩
          obtain ⟨v', rst', hrq', hval⟩ := hst rfl
          rw [hval]
          exact Event.st_rq.inj (List.cons.inj (hrq'.symm.trans hrq)).1
  obtain ⟨s', hs, hm'⟩ := key
  exact ⟨s', hs, noBad_of_good hg', synced_of_good hg', hv',
         anchor_of_val hg' hm' (ext_step_ext hext h hs), hg'⟩

/-- Lungo ogni esecuzione dell'implementazione lo spec segue con la stessa traccia. -/
theorem enough_star {i : MSIState n} {l : List (MSIExternalEvent n)}
    (h : star_extend msi_step_external msi_step_internal (default : MSIState n) l i) :
    ∃ s, star seq_step (seq_init n) l s ∧ φ i s := by
  induction h with
  | refl => exact ⟨seq_init n, star.refl _, φ_init⟩
  | step_int l s' s'' ie _ hstep ih =>
    obtain ⟨t, ht, hφ⟩ := ih
    exact ⟨t, ht, enough_internal hφ hstep⟩
  | step_ext l s' s'' e _ hstep ih =>
    obtain ⟨t, ht, hφ⟩ := ih
    obtain ⟨t', ht', hφ'⟩ := enough hφ hstep
    exact ⟨t', star.step _ _ _ _ _ ht ht', hφ'⟩

/-- **L'inclusione delle tracce, nel modo classico.** -/
theorem trace_inclusion (l : List (MSIExternalEvent n)) :
    imp_behaviour n l → spec_behaviour n l := by
  intro himp
  obtain ⟨i, hi⟩ := himp
  obtain ⟨s, hs, _⟩ := enough_star hi
  exact ⟨s, hs⟩

end MSIBag.Normale
