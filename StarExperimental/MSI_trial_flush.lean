import StarExperimental.MSI_trial_bridge
import StarExperimental.MSI_trial_spec

/-!
# `MSI_trial`: la relazione di flush e le quattro ipotesi di ARS che la riguardano

La stessa relazione di `MSI_final_flush.lean`: raggiungibilità, `extqueue` uguali, e **ogni copia viva
del valore è la memoria dello spec** (cache in `S`/`M`, grant `rsM`/`rsS` in volo, rilascio `rsIμ` in
volo, parent quando nessuna riga è `M`). Nessuna condizione di forma: la relazione è conservata da
ogni passo interno (`flush_step_int`), quindi `relation_flush`, `relation_method_int` e
`relation_flush_method_int` valgono con zero passi interni (`i'' := i'`).

Le code sono citate dal lato cache; il lato parent ne è la copia su ogni stato raggiungibile
(`synced_of_reach`). L'unico punto in cui servono le viste è `st_rq_M_state`: la memoria cambia, e
nessun'altra copia deve essere viva (sei fatti su `badView`, via i lemmi ponte).
-/

open THEORY Relation MSIView
open ReachingStar (Rule trans_refl relation_flush relation_flush_method_int relation_method_int
  relation_init)

namespace MSITrial

variable {n : Nat}

/-- La relazione di flush di `MSI_trial`. -/
def flush (i : MSIState n) (s : SeqState n) : Prop :=
  Reach i ∧
  (∀ k, (i.caches k).extqueue = s.extqueue k) ∧
  (∀ k, (i.caches k).state ≠ Bstate.I → (i.caches k).value = s.memory) ∧
  (∀ k v, PCEvent.rsM v ∈ (i.caches k).queue_pc → v = s.memory) ∧
  (∀ k v, PCEvent.rsS v ∈ (i.caches k).queue_pc → v = s.memory) ∧
  (∀ k v, CPEvent.rsIμ v ∈ (i.caches k).queue_cp → v = s.memory) ∧
  ((∀ k, i.parent.shared_state k ≠ Bstate.M) → i.parent.value = s.memory)

/-! ## Lemmi locali -/

/-- `Reach` è chiusa per un passo interno. -/
theorem reach_of_step_int {x y : MSIState n} {e : IEvent n} (hr : Reach x) (h : step_int x e y) :
    Reach y := by
  obtain ⟨l, hl⟩ := hr
  exact ⟨l, ReachingStar.star_extend.step_int _ _ _ _ hl
    (ReachingStar.trans_refl.step ⟨e, h⟩ ReachingStar.trans_refl.refl)⟩

/-- `Reach` è chiusa per un passo esterno. -/
theorem reach_of_step_ext {x y : MSIState n} {e : MSIExternalEvent n} (hr : Reach x)
    (h : msi_step_external x e y) : Reach y := by
  obtain ⟨l, hl⟩ := hr
  exact ⟨e :: l, ReachingStar.star_extend.step_ext _ _ _ _ _ hl h⟩

/-- Appartenenza a una famiglia di code aggiornata in `i` con un messaggio in più. -/
theorem mem_of_mem_update_append {α : Type} {i k : Fin n} {f : Fin n → List α} {a x : α}
    (h : a ∈ update_Fin i (f i ++ [x]) f k) : a ∈ f k ∨ a = x := by
  by_cases hk : i = k
  · subst hk
    rw [update_Fin_gss] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  · rw [update_Fin_gso _ _ _ _ hk] at h
    exact Or.inl h

/-- Appartenenza a una famiglia di code aggiornata in `i` con un messaggio in meno. -/
theorem mem_of_mem_update_eraseIdx {α : Type} {i k : Fin n} {f : Fin n → List α} {a : α} {j : Nat}
    (h : a ∈ update_Fin i ((f i).eraseIdx j) f k) : a ∈ f k := by
  by_cases hk : i = k
  · subst hk
    rw [update_Fin_gss] at h
    exact List.mem_of_mem_eraseIdx h
  · rw [update_Fin_gso _ _ _ _ hk] at h
    exact h

/-- Nessun grant `rsM` per `k` se non ci sono token `M` in volo per `k`. -/
theorem no_rsM_of_muMsgs_zero {p : ParentState n} {k : Fin n} (h : muMsgs p k = 0) {v : Value}
    (hv : PCEvent.rsM v ∈ p.queue_pci k) : False := by
  have : 0 < (p.queue_pci k).countP isGrantM := List.countP_pos_iff.mpr ⟨_, hv, rfl⟩
  unfold muMsgs at h; omega

/-- Nessun rilascio `rsIμ` di `k` se non ci sono token `M` in volo per `k`. -/
theorem no_rsIμ_of_muMsgs_zero {p : ParentState n} {k : Fin n} (h : muMsgs p k = 0) {v : Value}
    (hv : CPEvent.rsIμ v ∈ p.queue_cip k) : False := by
  have : 0 < (p.queue_cip k).countP isReleaseM := List.countP_pos_iff.mpr ⟨_, hv, rfl⟩
  unfold muMsgs at h; omega

/-- Nessun grant `rsS` per `k` se non ci sono token `S` in volo per `k`. -/
theorem no_rsS_of_sigMsgs_zero {p : ParentState n} {k : Fin n} (h : sigMsgs p k = 0) {v : Value}
    (hv : PCEvent.rsS v ∈ p.queue_pci k) : False := by
  have : 0 < (p.queue_pci k).countP isGrantS := List.countP_pos_iff.mpr ⟨_, hv, rfl⟩
  unfold sigMsgs at h; omega

/-- Le quattro clausole sui valori di una cache sono conservate da ogni regola di cache, e la
`extqueue` non cambia. -/
theorem cache_step_values {c c' : CacheState} {e : CEvent} {m : Value} (h : cache_step c e c')
    (h1 : c.state ≠ Bstate.I → c.value = m)
    (h2 : ∀ v, PCEvent.rsM v ∈ c.queue_pc → v = m)
    (h3 : ∀ v, PCEvent.rsS v ∈ c.queue_pc → v = m)
    (h4 : ∀ v, CPEvent.rsIμ v ∈ c.queue_cp → v = m) :
    (c'.state ≠ Bstate.I → c'.value = m) ∧
    (∀ v, PCEvent.rsM v ∈ c'.queue_pc → v = m) ∧
    (∀ v, PCEvent.rsS v ∈ c'.queue_pc → v = m) ∧
    (∀ v, CPEvent.rsIμ v ∈ c'.queue_cp → v = m) ∧ c'.extqueue = c.extqueue := by
  have hM : c.state = Bstate.M → c.value = m := fun hM => h1 (by rw [hM]; intro h; cases h)
  cases h with
  | rq_data_not_available hM' =>
    refine ⟨fun h => (h rfl).elim, h2, h3, fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases CPEvent.rsIμ.inj (List.mem_singleton.mp hv)
      exact hM hM'
  | rq_data_not_available1 _ =>
    refine ⟨fun h => (h rfl).elim, h2, h3, fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases List.mem_singleton.mp hv
  | upgrade_from_I_rq _ _ _ _ =>
    refine ⟨h1, h2, h3, fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases List.mem_singleton.mp hv
  | upgrade_from_I_rq1 _ _ _ _ =>
    refine ⟨h1, h2, h3, fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases List.mem_singleton.mp hv
  | upgrade_from_I_rs v j hj _ =>
    exact ⟨fun _ => h2 v (List.mem_of_getElem? hj),
      fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), h4, rfl⟩
  | upgrade_from_I_rsS v j hj _ =>
    exact ⟨fun _ => h3 v (List.mem_of_getElem? hj),
      fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), h4, rfl⟩
  | downgrade_from_M_rs j hj hM' =>
    refine ⟨fun h => (h rfl).elim, fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases CPEvent.rsIμ.inj (List.mem_singleton.mp hv)
      exact hM hM'
  | downgrade_from_M_rs1 j hj _ =>
    refine ⟨fun h => (h rfl).elim, fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), fun v hv => ?_, rfl⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h4 v hv
    · cases List.mem_singleton.mp hv
  | drop_rqIμ j hj _ =>
    exact ⟨h1, fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), h4, rfl⟩
  | drop_rqIσ j hj _ =>
    exact ⟨h1, fun w hw => h2 w (List.mem_of_mem_eraseIdx hw),
      fun w hw => h3 w (List.mem_of_mem_eraseIdx hw), h4, rfl⟩

/-- Le clausole sui valori lato parent sono conservate da ogni regola del parent. L'unico fatto
sulle viste: un `rsIσ` in volo per `k` ha la riga `k` a `S` (vista cattiva 2). -/
theorem parent_step_values {p p' : ParentState n} {ev : ParentInternalEvent n} {m : Value}
    (h : parent_msi_step p ev p')
    (h2 : ∀ k v, PCEvent.rsM v ∈ p.queue_pci k → v = m)
    (h3 : ∀ k v, PCEvent.rsS v ∈ p.queue_pci k → v = m)
    (h4 : ∀ k v, CPEvent.rsIμ v ∈ p.queue_cip k → v = m)
    (h7 : (∀ k, p.shared_state k ≠ Bstate.M) → p.value = m)
    (hbad : ∀ k, sigMsgs p k ≠ 0 → p.shared_state k = Bstate.S) :
    (∀ k v, PCEvent.rsM v ∈ p'.queue_pci k → v = m) ∧
    (∀ k v, PCEvent.rsS v ∈ p'.queue_pci k → v = m) ∧
    (∀ k v, CPEvent.rsIμ v ∈ p'.queue_cip k → v = m) ∧
    ((∀ k, p'.shared_state k ≠ Bstate.M) → p'.value = m) := by
  cases h with
  | downgrade_from_M_rq1 v i j hj =>
    exact ⟨h2, h3, fun k w hw => h4 k w (mem_of_mem_update_eraseIdx hw),
      fun _ => h4 i v (List.mem_of_getElem? hj)⟩
  | downgrade_from_M_rq2 i j hj =>
    refine ⟨h2, h3, fun k w hw => h4 k w (mem_of_mem_update_eraseIdx hw), fun hall => h7 fun k => ?_⟩
    by_cases hk : i = k
    · subst hk
      intro hM
      have := hbad i (sigMsgs_ne_zero_of_rsIσ hj)
      rw [hM] at this
      cases this
    · have := hall k
      simp only [update_Fin_gso _ _ _ _ hk] at this
      exact this
  | upgrade_to_M_data_avilable_rq1 i j hj hI =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, fun k w hw => h4 k w (mem_of_mem_update_eraseIdx hw),
      fun hall => absurd (update_Fin_gss i Bstate.M p.shared_state) (hall i)⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
        exact h7 fun k' => by rw [hI k']; intro h; cases h
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw
  | upgrade_to_M_data_avilable_rq2 i j hj _ hnoM =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, fun k w hw => h4 k w (mem_of_mem_update_eraseIdx hw),
      fun _ => h7 hnoM⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw
        exact h7 hnoM
  | upgrade_to_M_invalid_all i i' j hj _ =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, h4, h7⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw
  | upgrade_to_M_invalid_all1 i i' j hj _ =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, h4, h7⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw
  | upgrade_to_M_invalid_all2 i i' j hj _ _ =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, h4, h7⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw
  | upgrade_to_M_invalid_all3 i i' j hj _ =>
    refine ⟨fun k w hw => ?_, fun k w hw => ?_, h4, h7⟩
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h2 k w hw
      · cases hw
    · rcases mem_of_mem_update_append hw with hw | hw
      · exact h3 k w hw
      · cases hw

/-- Un passo esterno che non tocca valori né code interne e cambia la `extqueue` di `k` come lo spec
conserva `flush`. -/
theorem flush_ext_keep (k : Fin n) {i i' : MSIState n} {s s' : SeqState n}
    (hr' : Reach i') (hf : flush i s)
    (hmem : s'.memory = s.memory)
    (hq : (i'.caches k).extqueue = s'.extqueue k)
    (hcache : ∀ k', k ≠ k' → i'.caches k' = i.caches k')
    (hsq : ∀ k', k ≠ k' → s'.extqueue k' = s.extqueue k')
    (hst : (i'.caches k).state = (i.caches k).state)
    (hv : (i'.caches k).value = (i.caches k).value)
    (hpc : (i'.caches k).queue_pc = (i.caches k).queue_pc)
    (hcp : (i'.caches k).queue_cp = (i.caches k).queue_cp)
    (hrow : i'.parent.shared_state = i.parent.shared_state)
    (hpv : i'.parent.value = i.parent.value) : flush i' s' := by
  obtain ⟨_, hext, hval, hrsM, hrsS, hrsIμ, hpar⟩ := hf
  refine ⟨hr', fun k' => ?_, fun k' => ?_, fun k' v hv' => ?_, fun k' v hv' => ?_,
    fun k' v hv' => ?_, fun hall => ?_⟩
  · by_cases hk : k = k'
    · subst hk; exact hq
    · rw [hcache k' hk, hsq k' hk]; exact hext k'
  · by_cases hk : k = k'
    · subst hk; rw [hst, hv, hmem]; exact hval k
    · rw [hcache k' hk, hmem]; exact hval k'
  · by_cases hk : k = k'
    · subst hk; rw [hpc] at hv'; rw [hmem]; exact hrsM k v hv'
    · rw [hcache k' hk] at hv'; rw [hmem]; exact hrsM k' v hv'
  · by_cases hk : k = k'
    · subst hk; rw [hpc] at hv'; rw [hmem]; exact hrsS k v hv'
    · rw [hcache k' hk] at hv'; rw [hmem]; exact hrsS k' v hv'
  · by_cases hk : k = k'
    · subst hk; rw [hcp] at hv'; rw [hmem]; exact hrsIμ k v hv'
    · rw [hcache k' hk] at hv'; rw [hmem]; exact hrsIμ k' v hv'
  · rw [hpv, hmem]
    exact hpar fun k' => by have := hall k'; rwa [hrow] at this

/-! ## Conservazione -/

/-- Ogni passo interno conserva `flush` (stesso `s`): ogni regola copia una copia viva del valore in
un altro posto, o non tocca valori. Nessun fatto sulle viste. -/
theorem flush_step_int {i i' : MSIState n} {s : SeqState n} {e : IEvent n}
    (hf : flush i s) (h : step_int i e i') : flush i' s := by
  obtain ⟨hr, hext, hval, hrsM, hrsS, hrsIμ, hpar⟩ := hf
  have hsync := synced_of_reach hr
  refine ⟨reach_of_step_int hr h, ?_⟩
  cases h with
  | cache cache' k e hc =>
    obtain ⟨c1, c2, c3, c4, c5⟩ := cache_step_values hc (hval k) (hrsM k) (hrsS k) (hrsIμ k)
    refine ⟨fun k' => ?_, fun k' => ?_, fun k' v hv => ?_, fun k' v hv => ?_, fun k' v hv => ?_, hpar⟩
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss]; rw [c5]; exact hext k
      · simp only [update_Fin_gso _ _ _ _ hk]; exact hext k'
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss]; exact c1
      · simp only [update_Fin_gso _ _ _ _ hk]; exact hval k'
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact c2 v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsM k' v hv
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact c3 v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsS k' v hv
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact c4 v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsIμ k' v hv
  | parent_upd_queue parent' e k hp =>
    have hs2 : ∀ k v, PCEvent.rsM v ∈ i.parent.queue_pci k → v = s.memory :=
      fun k v hv => hrsM k v (by rw [← (hsync k).2]; exact hv)
    have hs3 : ∀ k v, PCEvent.rsS v ∈ i.parent.queue_pci k → v = s.memory :=
      fun k v hv => hrsS k v (by rw [← (hsync k).2]; exact hv)
    have hs4 : ∀ k v, CPEvent.rsIμ v ∈ i.parent.queue_cip k → v = s.memory :=
      fun k v hv => hrsIμ k v (by rw [← (hsync k).1]; exact hv)
    have hbad : ∀ k, sigMsgs i.parent k ≠ 0 → i.parent.shared_state k = Bstate.S :=
      fun k hk => Classical.byContradiction fun hne => not_reach_of_sig_row hk hne hr
    obtain ⟨p2, p3, p4, p7⟩ := parent_step_values hp hs2 hs3 hs4 hpar hbad
    refine ⟨fun k' => ?_, fun k' => ?_, fun k' v hv => ?_, fun k' v hv => ?_, fun k' v hv => ?_, p7⟩
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss]; exact hext k
      · simp only [update_Fin_gso _ _ _ _ hk]; exact hext k'
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss]; exact hval k
      · simp only [update_Fin_gso _ _ _ _ hk]; exact hval k'
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact p2 k v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsM k' v hv
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact p3 k v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsS k' v hv
    · by_cases hk : k = k'
      · subst hk; simp only [update_Fin_gss] at hv; exact p4 k v hv
      · simp only [update_Fin_gso _ _ _ _ hk] at hv; exact hrsIμ k' v hv

/-- Un metodo abilitato nell'implementazione è abilitato nello spec: le `extqueue` coincidono, e per
le load il valore della cache (in `S`/`M`) è la memoria. -/
theorem flush_method {i i' : MSIState n} {s : SeqState n} {e : MSIExternalEvent n}
    (hf : flush i s) (h : msi_step_external i e i') : ∃ s', seq_step s e s' := by
  obtain ⟨_, hext, hval, _, _, _, _⟩ := hf
  cases h with
  | cache ev cache' k hc =>
    cases hc with
    | ld_rq => exact ⟨_, seq_step.ld_rq s k⟩
    | st_rq v => exact ⟨_, seq_step.st_rq s v k⟩
    | ld_rq_data_available1 rst hrq hS =>
      exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq)
        (hval k (by rw [hS]; intro h; cases h)).symm⟩
    | ld_rq_data_available rst hrq hM =>
      exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq)
        (hval k (by rw [hM]; intro h; cases h)).symm⟩
    | st_rq_M_state v rst hrq hM =>
      exact ⟨_, seq_step.st_rs s v k rst (by rw [← hext k]; exact hrq)⟩

/-- Dopo lo stesso metodo nell'implementazione e nello spec la relazione vale di nuovo. Per
`st_rq_M_state` servono le viste: la cache che scrive è l'unico portatore. -/
theorem flush_step_ext {i i' : MSIState n} {s s' : SeqState n} {e : MSIExternalEvent n}
    (hf : flush i s) (h : msi_step_external i e i') (hs : seq_step s e s') : flush i' s' := by
  have hr := hf.1
  have hext := hf.2.1
  have hsync := synced_of_reach hr
  have hr' : Reach i' := reach_of_step_ext hr h
  cases h with
  | cache ev cache' k hc =>
    cases hc with
    | ld_rq =>
      cases hs
      exact flush_ext_keep k hr' hf rfl (by simp only [update_Fin_gss]; rw [hext k])
        (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
        (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
        (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss])
        (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss]) rfl rfl
    | st_rq v =>
      cases hs
      exact flush_ext_keep k hr' hf rfl (by simp only [update_Fin_gss]; rw [hext k])
        (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
        (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
        (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss])
        (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss]) rfl rfl
    | ld_rq_data_available1 rst hrq _ =>
      cases hs with
      | ld_rs _ _ rsts hrqs _ =>
        have hrq' : (s.extqueue k).rq = Event.ld_rq :: rst := by rw [← hext k]; exact hrq
        rw [hrq'] at hrqs
        cases hrqs
        exact flush_ext_keep k hr' hf rfl (by simp only [update_Fin_gss]; rw [hext k])
          (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
          (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
          (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss])
          (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss]) rfl rfl
    | ld_rq_data_available rst hrq _ =>
      cases hs with
      | ld_rs _ _ rsts hrqs _ =>
        have hrq' : (s.extqueue k).rq = Event.ld_rq :: rst := by rw [← hext k]; exact hrq
        rw [hrq'] at hrqs
        cases hrqs
        exact flush_ext_keep k hr' hf rfl (by simp only [update_Fin_gss]; rw [hext k])
          (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
          (fun k' hk => by simp only [update_Fin_gso _ _ _ _ hk])
          (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss])
          (by simp only [update_Fin_gss]) (by simp only [update_Fin_gss]) rfl rfl
    | st_rq_M_state v rst hrq hM =>
      cases hs with
      | st_rs vs _ rsts hrqs =>
        have hrq' : (s.extqueue k).rq = Event.st_rq v :: rst := by rw [← hext k]; exact hrq
        rw [hrq'] at hrqs
        cases hrqs
        -- la cache `k` in `M` è l'unico portatore (sei fatti sulle viste)
        have hrowk : i.parent.shared_state k = Bstate.M :=
          Classical.byContradiction fun hne => not_reach_of_M hM (Or.inr (Or.inr hne)) hr
        have hmuk : muMsgs i.parent k = 0 :=
          Classical.byContradiction fun hne => not_reach_of_M hM (Or.inl hne) hr
        have hsigk : sigMsgs i.parent k = 0 :=
          Classical.byContradiction fun hne => not_reach_of_M hM (Or.inr (Or.inl hne)) hr
        have hrow' : ∀ k', k ≠ k' → i.parent.shared_state k' = Bstate.I :=
          fun k' hk => Classical.byContradiction fun hne => not_reach_of_M_rowJ hk hM hne hr
        have hmu' : ∀ k', k ≠ k' → muMsgs i.parent k' = 0 :=
          fun k' hk => Classical.byContradiction fun hne =>
            not_reach_of_mu_row hne (by rw [hrow' k' hk]; intro h; cases h) hr
        have hsig' : ∀ k', k ≠ k' → sigMsgs i.parent k' = 0 :=
          fun k' hk => Classical.byContradiction fun hne =>
            not_reach_of_sig_row hne (by rw [hrow' k' hk]; intro h; cases h) hr
        have hstate' : ∀ k', k ≠ k' → (i.caches k').state = Bstate.I := by
          intro k' hk
          cases hst : (i.caches k').state with
          | M => exact absurd hr (not_reach_of_M hst
                   (Or.inr (Or.inr (by rw [hrow' k' hk]; intro h; cases h))))
          | I => rfl
          | S => exact absurd hr (not_reach_of_S hst
                   (Or.inr (Or.inr (by rw [hrow' k' hk]; intro h; cases h))))
        refine ⟨hr', fun k' => ?_, fun k' => ?_, fun k' w hw => ?_, fun k' w hw => ?_,
          fun k' w hw => ?_, fun hall => ?_⟩
        · by_cases hk : k = k'
          · subst hk; simp only [update_Fin_gss]; rw [hext k]
          · simp only [update_Fin_gso _ _ _ _ hk]; exact hext k'
        · by_cases hk : k = k'
          · subst hk; intro _; simp only [update_Fin_gss]
          · simp only [update_Fin_gso _ _ _ _ hk]; intro hne; exact absurd (hstate' k' hk) hne
        · exfalso
          by_cases hk : k = k'
          · subst hk; simp only [update_Fin_gss] at hw
            exact no_rsM_of_muMsgs_zero hmuk (by rw [(hsync k).2]; exact hw)
          · simp only [update_Fin_gso _ _ _ _ hk] at hw
            exact no_rsM_of_muMsgs_zero (hmu' k' hk) (by rw [(hsync k').2]; exact hw)
        · exfalso
          by_cases hk : k = k'
          · subst hk; simp only [update_Fin_gss] at hw
            exact no_rsS_of_sigMsgs_zero hsigk (by rw [(hsync k).2]; exact hw)
          · simp only [update_Fin_gso _ _ _ _ hk] at hw
            exact no_rsS_of_sigMsgs_zero (hsig' k' hk) (by rw [(hsync k').2]; exact hw)
        · exfalso
          by_cases hk : k = k'
          · subst hk; simp only [update_Fin_gss] at hw
            exact no_rsIμ_of_muMsgs_zero hmuk (by rw [(hsync k).1]; exact hw)
          · simp only [update_Fin_gso _ _ _ _ hk] at hw
            exact no_rsIμ_of_muMsgs_zero (hmu' k' hk) (by rw [(hsync k').1]; exact hw)
        · exact absurd hrowk (hall k)

/-! ## Le quattro ipotesi di ARS -/

theorem flush_trans {i i' : MSIState n} {s : SeqState n} (hf : flush i s)
    (h : trans_refl (rule n) i i') : flush i' s := by
  induction h with
  | refl => exact hf
  | step hab _ ih =>
      obtain ⟨e, he⟩ := hab
      exact ih (flush_step_int hf he)

theorem trial_relation_init : relation_init (flush (n := n)) (default : MSIState n) (seq_init n) := by
  unfold relation_init flush
  exact ⟨⟨[], ReachingStar.star_extend.refl _⟩, fun _ => rfl, fun _ h => (h rfl).elim,
    fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ h => (List.not_mem_nil h).elim, fun _ => rfl⟩

theorem trial_relation_flush (i i' : MSIState n) (s : SeqState n) :
    relation_flush flush i i' s (rule n) :=
  fun hf htr => ⟨i', trans_refl.refl, flush_trans hf htr⟩

theorem trial_relation_method_int (i i' i'' : MSIState n) (s : SeqState n) (e : MSIExternalEvent n) :
    relation_method_int flush (rule n) msi_step_external seq_step i i' i'' s e :=
  fun hf htr hm => flush_method (flush_trans hf htr) hm

theorem trial_relation_flush_method_int (i i' i'' : MSIState n) (s s' : SeqState n)
    (e : MSIExternalEvent n) :
    relation_flush_method_int flush (rule n) msi_step_external seq_step i i' i'' s s' e :=
  fun hf htr hm hs => ⟨i'', trans_refl.refl, flush_step_ext (flush_trans hf htr) hm hs⟩

end MSITrial
