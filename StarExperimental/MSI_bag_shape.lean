import StarExperimental.MSI_bag_def

/-! # `MSI_bag_shape`: la forma di uno stato e gli stati "buoni"

Le viste non guardano né i valori né le `extqueue`. `shape s` azzera i valori (nelle cache, nel
parent, dentro i messaggi) e svuota le `extqueue`: uno stato *flushed* ha `shape = default`, e i
passi interni commutano con `shape` a meno dei valori nelle etichette. Così il risultato della
tattica (nessuna vista cattiva sui cammini interni ed esterni da `default`) si trasporta a ogni
cammino interno che parte da uno stato con forma raggiungibile: è `Good`.

`Good x` non è un invariante dimostrato a mano: è "la forma di `x` è raggiungibile da `default`",
chiusa per passi interni (`good_step`) ed esterni (`good_step_ext`), implicata da `Reach`
(`good_of_reach`) e da flush (`shape` di uno stato flushed è `default`). Da `Good x` si leggono
`synced x` e `¬ badView` (`noBad_of_good`). -/

open THEORY Relation
open ReachingStar (trans_refl)

namespace MSIBag

variable {n : Nat}

/-- Azzera il dato di un rilascio. -/
def stripCP : CPEvent → CPEvent
  | .rsIμ _ => .rsIμ 0
  | .rsIσ => .rsIσ
  | .rqS => .rqS
  | .rqM => .rqM

/-- Azzera il dato di un grant. -/
def stripPC : PCEvent → PCEvent
  | .rsM _ => .rsM 0
  | .rsS _ => .rsS 0
  | .rqIμ => .rqIμ
  | .rqIσ => .rqIσ

def shapeCache (c : CacheState) : CacheState :=
  { state := c.state, value := 0, queue_cp := c.queue_cp.map stripCP,
    queue_pc := c.queue_pc.map stripPC, extqueue := ⟨[], []⟩ }

def shapeParent (p : ParentState n) : ParentState n :=
  { value := 0, shared_state := p.shared_state,
    queue_cip := fun k => (p.queue_cip k).map stripCP,
    queue_pci := fun k => (p.queue_pci k).map stripPC }

/-- Lo stato senza valori e senza code esterne. -/
def shape (s : MSIState n) : MSIState n :=
  ⟨fun k => shapeCache (s.caches k), shapeParent s.parent⟩

@[simp] theorem isGrantM_stripPC (e : PCEvent) : isGrantM (stripPC e) = isGrantM e := by
  cases e <;> rfl
@[simp] theorem isGrantS_stripPC (e : PCEvent) : isGrantS (stripPC e) = isGrantS e := by
  cases e <;> rfl
@[simp] theorem isReleaseM_stripCP (e : CPEvent) : isReleaseM (stripCP e) = isReleaseM e := by
  cases e <;> rfl
@[simp] theorem isReleaseS_stripCP (e : CPEvent) : isReleaseS (stripCP e) = isReleaseS e := by
  cases e <;> rfl

theorem countP_grantM_strip (q : Multiset PCEvent) :
    (q.map stripPC).countP (fun e => isGrantM e = true) = q.countP (fun e => isGrantM e = true) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.countP_cons, ih]
theorem countP_grantS_strip (q : Multiset PCEvent) :
    (q.map stripPC).countP (fun e => isGrantS e = true) = q.countP (fun e => isGrantS e = true) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.countP_cons, ih]
theorem countP_releaseM_strip (q : Multiset CPEvent) :
    (q.map stripCP).countP (fun e => isReleaseM e = true) = q.countP (fun e => isReleaseM e = true) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.countP_cons, ih]
theorem countP_releaseS_strip (q : Multiset CPEvent) :
    (q.map stripCP).countP (fun e => isReleaseS e = true) = q.countP (fun e => isReleaseS e = true) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.countP_cons, ih]

theorem muMsgs_shape (s : MSIState n) (k : Fin n) : muMsgs (shape s).parent k = muMsgs s.parent k := by
  simp only [muMsgs, shape, shapeParent, countP_grantM_strip, countP_releaseM_strip]

theorem sigMsgs_shape (s : MSIState n) (k : Fin n) : sigMsgs (shape s).parent k = sigMsgs s.parent k := by
  simp only [sigMsgs, shape, shapeParent, countP_grantS_strip, countP_releaseS_strip]

/-- Le viste non guardano né i valori né le `extqueue`. -/
theorem msiView_shape (s : MSIState n) (i j : Fin n) : msiView (shape s) i j = msiView s i j := by
  unfold msiView
  rw [muMsgs_shape, sigMsgs_shape]
  rfl

theorem synced_shape {s : MSIState n} (hs : synced s) : synced (shape s) := by
  intro k
  obtain ⟨h1, h2⟩ := hs k
  exact ⟨by simp only [shape, shapeParent, shapeCache, h1],
         by simp only [shape, shapeParent, shapeCache, h2]⟩

/-- Estensionalità di `MSIState`: cache puntuali e parent. -/
theorem shape_default_aux1 {a b : MSIState n} (hc : ∀ k, a.caches k = b.caches k)
    (hp : a.parent = b.parent) : a = b := by
  obtain ⟨ca, pa⟩ := a
  obtain ⟨cb, pb⟩ := b
  have e1 : ca = cb := funext hc
  have e2 : pa = pb := hp
  subst e1 e2
  rfl

/-- Estensionalità campo per campo di `ParentState` (puntuale sulle code). -/
theorem shape_default_aux2 {a b : ParentState n} (hv : a.value = b.value)
    (hs : a.shared_state = b.shared_state) (h1 : ∀ k, a.queue_cip k = b.queue_cip k)
    (h2 : ∀ k, a.queue_pci k = b.queue_pci k) : a = b := by
  obtain ⟨va, sa, ca, da⟩ := a
  obtain ⟨vb, sb, cb, db⟩ := b
  have e1 : va = vb := hv
  have e2 : sa = sb := hs
  have e3 : ca = cb := funext h1
  have e4 : da = db := funext h2
  subst e1 e2 e3 e4
  rfl

theorem shape_default : shape (default : MSIState n) = default :=
  shape_default_aux1 (fun _ => rfl) rfl

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem shape_cache_internal_aux1 {c c' c'' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c') (heq : c' = c'') : cache_msi_step_internal c e c'' :=
  heq ▸ h

/-- Un passo interno di cache commuta con `shape`, a meno del valore nell'etichetta. -/
theorem shape_cache_internal {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c') :
    ∃ e', cache_msi_step_internal (shapeCache c) e' (shapeCache c') := by
  cases h with
  | rq_data_not_available hM =>
    exact ⟨_, shape_cache_internal_aux1 (.rq_data_not_available _ hM)
      (by simp [shapeCache, stripCP])⟩
  | rq_data_not_available1 hS =>
    exact ⟨_, shape_cache_internal_aux1 (.rq_data_not_available1 _ hS)
      (by simp [shapeCache, stripCP])⟩
  | upgrade_from_I_rq hI =>
    exact ⟨_, shape_cache_internal_aux1 (.upgrade_from_I_rq _ hI)
      (by simp [shapeCache, stripCP])⟩
  | upgrade_from_I_rq1 hI =>
    exact ⟨_, shape_cache_internal_aux1 (.upgrade_from_I_rq1 _ hI)
      (by simp [shapeCache, stripCP])⟩
  | upgrade_from_I_rs v hv hI =>
    exact ⟨_, shape_cache_internal_aux1
      (.upgrade_from_I_rs _ 0 (Multiset.mem_map_of_mem stripPC hv) hI)
      (by simp [shapeCache, Multiset.map_erase_of_mem stripPC _ hv, stripPC.eq_1])⟩
  | upgrade_from_I_rsS v hv hI =>
    exact ⟨_, shape_cache_internal_aux1
      (.upgrade_from_I_rsS _ 0 (Multiset.mem_map_of_mem stripPC hv) hI)
      (by simp [shapeCache, Multiset.map_erase_of_mem stripPC _ hv, stripPC.eq_2])⟩
  | downgrade_from_M_rs hv hM =>
    exact ⟨_, shape_cache_internal_aux1
      (.downgrade_from_M_rs _ (Multiset.mem_map_of_mem stripPC hv) hM)
      (by simp [shapeCache, Multiset.map_erase_of_mem stripPC _ hv, stripPC.eq_3, stripCP.eq_1])⟩
  | downgrade_from_M_rs1 hv hS =>
    exact ⟨_, shape_cache_internal_aux1
      (.downgrade_from_M_rs1 _ (Multiset.mem_map_of_mem stripPC hv) hS)
      (by simp [shapeCache, Multiset.map_erase_of_mem stripPC _ hv, stripPC.eq_4, stripCP.eq_2])⟩

theorem shape_parent_internal_aux1 {p p' p'' : ParentState n} {e : ParentInternalEvent n}
    (h : parent_msi_step p e p') (heq : p' = p'') : parent_msi_step p e p'' := heq ▸ h

/-- Un passo del parent commuta con `shape`, a meno del valore nell'etichetta. -/
theorem shape_parent_internal {p p' : ParentState n} {e : ParentUpdQueueInternalEvent n} {i : Fin n}
    (h : parent_msi_step p (.upd_queue e i) p') :
    ∃ e', parent_msi_step (shapeParent p) (.upd_queue e' i) (shapeParent p') := by
  cases h with
  | downgrade_from_M_rq1 v i hv =>
    refine ⟨.downgrade_from_M_rq1 0, shape_parent_internal_aux1
      (.downgrade_from_M_rq1 (shapeParent p) 0 i (Multiset.mem_map_of_mem stripCP hv)) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => ?_) (fun k => rfl)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, Multiset.map_erase_of_mem stripCP _ hv, stripCP.eq_1]
    · simp [update_Fin_gso2 _ _ _ _ hk]
  | downgrade_from_M_rq2 i hv =>
    refine ⟨.downgrade_from_S_rq1S, shape_parent_internal_aux1
      (.downgrade_from_M_rq2 (shapeParent p) i (Multiset.mem_map_of_mem stripCP hv)) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => ?_) (fun k => rfl)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, Multiset.map_erase_of_mem stripCP _ hv, stripCP.eq_2]
    · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_data_avilable_rq1 i hv hall =>
    refine ⟨.upgrade_to_M_data_avilable_rq1, shape_parent_internal_aux1
      (.upgrade_to_M_data_avilable_rq1 (shapeParent p) i (Multiset.mem_map_of_mem stripCP hv) hall) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => ?_) (fun k => ?_)
    · simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, Multiset.map_erase_of_mem stripCP _ hv, stripCP.eq_4]
      · simp [update_Fin_gso2 _ _ _ _ hk]
    · simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_data_avilable_rq2 i hv hi hall =>
    refine ⟨.upgrade_to_S_data_avilable_rq1S, shape_parent_internal_aux1
      (.upgrade_to_M_data_avilable_rq2 (shapeParent p) i (Multiset.mem_map_of_mem stripCP hv) hi hall) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => ?_) (fun k => ?_)
    · simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, Multiset.map_erase_of_mem stripCP _ hv, stripCP.eq_3]
      · simp [update_Fin_gso2 _ _ _ _ hk]
    · simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all i0 i hv hrow =>
    refine ⟨.upgrade_to_M_invalid_all i0, shape_parent_internal_aux1
      (.upgrade_to_M_invalid_all (shapeParent p) i0 i (Multiset.mem_map_of_mem stripCP hv) hrow) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => rfl) (fun k => ?_)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, stripPC]
    · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all1 i0 i hv hrow =>
    refine ⟨.invalid_allS, shape_parent_internal_aux1
      (.upgrade_to_M_invalid_all1 (shapeParent p) i0 i (Multiset.mem_map_of_mem stripCP hv) hrow) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => rfl) (fun k => ?_)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, stripPC]
    · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all2 i0 i hv hne hrow =>
    refine ⟨.upgrade_to_S_invalid_2_rq1S i0, shape_parent_internal_aux1
      (.upgrade_to_M_invalid_all2 (shapeParent p) i0 i (Multiset.mem_map_of_mem stripCP hv) hne hrow) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => rfl) (fun k => ?_)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, stripPC]
    · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all3 i0 i hv hrow =>
    refine ⟨.upgrade_to_M_invalid_all i0, shape_parent_internal_aux1
      (.upgrade_to_M_invalid_all3 (shapeParent p) i0 i (Multiset.mem_map_of_mem stripCP hv) hrow) ?_⟩
    refine shape_default_aux2 rfl rfl (fun k => rfl) (fun k => ?_)
    simp only [shapeParent]
    by_cases hk : k = i
    · subst hk; simp [update_Fin_gss, stripPC]
    · simp [update_Fin_gso2 _ _ _ _ hk]

theorem shape_internal_aux1 {s s' s'' : MSIState n} {t : MSIInternalEvent n}
    (h : msi_step_internal s t s') (heq : s' = s'') : msi_step_internal s t s'' := heq ▸ h

/-- Un passo interno di sistema commuta con `shape`. -/
theorem shape_internal {s s' : MSIState n} {t : MSIInternalEvent n} (h : msi_step_internal s t s') :
    ∃ t', msi_step_internal (shape s) t' (shape s') := by
  cases h with
  | cache c' i e hc =>
    obtain ⟨e', hc'⟩ := shape_cache_internal hc
    refine ⟨.cache e' i,
      shape_internal_aux1 (msi_step_internal.cache (shape s) (shapeCache c') i e' hc') ?_⟩
    refine shape_default_aux1 ?_ (shape_default_aux2 rfl rfl ?_ ?_)
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeCache, update_Fin_gss]
      · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeParent, shapeCache, update_Fin_gss]
      · simp [shape, shapeParent, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeParent, shapeCache, update_Fin_gss]
      · simp [shape, shapeParent, shapeCache, update_Fin_gso2 _ _ _ _ hk]
  | parent_upd_queue p' e i hp =>
    obtain ⟨e', hp'⟩ := shape_parent_internal hp
    refine ⟨.parent (.upd_queue e' i),
      shape_internal_aux1 (msi_step_internal.parent_upd_queue (shape s) (shapeParent p') e' i hp') ?_⟩
    refine shape_default_aux1 ?_ rfl
    intro k
    by_cases hk : k = i
    · subst hk; simp [shape, shapeCache, shapeParent, update_Fin_gss]
    · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]

/-- Un passo esterno di cache non tocca stato e code interne. -/
theorem shape_external_aux1 {c c' : CacheState} {e : Event} (h : cache_msi_step c e c') :
    c'.state = c.state ∧ c'.queue_cp = c.queue_cp ∧ c'.queue_pc = c.queue_pc := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- Un passo esterno non cambia la forma (su stati `synced`: il riallineamento delle copie
delle code nel parent è l'identità). NOTE: the skeleton's statement WITHOUT `(hs : synced s)` is
false (see notes / `shape_external_verbatim_false`); this is the provable version, and
`good_step_ext` must call it as `shape_external hx.1 hs`. -/
theorem shape_external {s s' : MSIState n} {e : MSIExternalEvent n} (hs : synced s)
    (h : msi_step_external s e s') : shape s' = shape s := by
  cases h with
  | cache e c' i hc =>
    obtain ⟨hst, hcp, hpc⟩ := shape_external_aux1 hc
    refine shape_default_aux1 ?_ (shape_default_aux2 rfl rfl ?_ ?_)
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeCache, update_Fin_gss, hst, hcp, hpc]
      · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeParent, update_Fin_gss, hcp, (hs k).1]
      · simp [shape, shapeParent, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeParent, update_Fin_gss, hpc, (hs k).2]
      · simp [shape, shapeParent, update_Fin_gso2 _ _ _ _ hk]

/-! ## Gli stati buoni -/

/-- La forma di `x` è raggiungibile da `default` (con i passi della tattica) e `x` è sincronizzato. -/
def Good (x : MSIState n) : Prop :=
  synced x ∧ ReflTransGen (msiSetup n).atrans (default : MSIState n) (shape x)

theorem good_default : Good (default : MSIState n) :=
  ⟨fun _ => ⟨rfl, rfl⟩, by rw [shape_default]⟩

theorem synced_of_good {x : MSIState n} (hx : Good x) : synced x := hx.1

/-- **Il ponte**: uno stato buono non ha viste cattive. Solo il risultato della tattica. -/
theorem noBad_of_good {x : MSIState n} (hx : Good x) : ∀ i j, ¬ badView (msiView x i j) := by
  intro i j hb
  refine badView_unreachable_from_default (shape x) ⟨i, j, ?_⟩ hx.2
  show badView (msiView (shape x) i j)
  rw [msiView_shape]; exact hb

theorem good_step {x y : MSIState n} (hx : Good x) {e} (hs : msi_step_internal x e y) : Good y := by
  obtain ⟨t', ht'⟩ := shape_internal hs
  exact ⟨synced_step hx.1 hs, hx.2.tail ⟨.inl t', msi_step_any.int _ _ _ ht'⟩⟩

theorem good_trans {x y : MSIState n} (hx : Good x) (hs : trans_refl (msi_rule n) x y) : Good y := by
  induction hs with
  | refl => exact hx
  | step hr _ ih => obtain ⟨e, he⟩ := hr; exact ih (good_step hx he)

theorem good_step_ext {x y : MSIState n} (hx : Good x) {e} (hs : msi_step_external x e y) : Good y :=
  ⟨synced_step_ext hx.1 hs, by rw [shape_external hx.1 hs]; exact hx.2⟩

theorem good_of_reach {x : MSIState n} (h : Reach x) : Good x := by
  unfold Reach ReachingStar.reachable at h
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact good_default
  | step_int l s' s'' _ hstep ih => exact good_trans ih hstep
  | step_ext l s' s'' e _ hstep ih => exact good_step_ext ih hstep

end MSIBag
