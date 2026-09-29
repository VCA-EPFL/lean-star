import StarExperimental.MSI

open THEORY
open Relation
open MSIView


/-! # `MSI_normale`: inclusione delle tracce alla vecchia maniera

Simulazione in avanti tra l'implementazione `MSI` e lo spec sequenziale (`SeqState`, `seq_step`,
`spec_behaviour`: copia letterale di `MSI_flush_proof.lean`, che non si può importare insieme a
`MSI.lean` perché entrambi definiscono `isRequest`), **senza** il framework ARS: niente `relation_*`,
niente diamante, niente riconvergenze. L'inclusione `imp_behaviour n l → spec_behaviour n l` è
un'induzione sulla traccia (`star_extend`): un passo interno conserva la relazione di simulazione
con lo stesso stato dello spec (stutter), un passo esterno è simulato da un passo di `seq_step`.

L'invariante φ dell'implementazione è **`badView`** (`MSI_def.lean`), cioè "nessuna coppia di
indici ha una vista cattiva", più `synced`. Non ne ridimostriamo l'induttività: il risultato della
tattica, `badView_unreachable_from_default`, dice che nessuna vista cattiva è raggiungibile da
`default` con passi *interni*. Per usarlo lungo una traccia con passi esterni si proietta lo stato su
`shape`, che azzera `value` (nelle cache, nel parent e dentro i messaggi) e le `extqueue`: le viste
non guardano nessuna di queste cose (`msiView_shape`), i passi interni commutano con `shape`
(`shape_internal`) e i passi esterni non la cambiano (`shape_external`). Quindi `shape s` è
internamente raggiungibile per ogni `s` sulla traccia, e `s` non ha viste cattive.

La sezione 4 ha la struttura del file `FormalMSI.SI` (`φ`, `enough`, `enough_internal`,
`enough_star`, `φ_init`, `trace_inclusion`), con `badView` al posto della `ψ` scritta a mano.

`badView` da solo non basta per la simulazione: parla della struttura (un proprietario di `M`,
token registrati), non dei valori, e lo spec risponde `ld_rs v` solo se `memory = v`. La relazione
di simulazione `sim` aggiunge quindi `memVal`: la memoria dello spec è "il valore della linea", cioè
il valore di chi la tiene in `M`, di ogni copia in `S`, di ogni token in volo (`rsIμ`, `rsM`, `rsS`)
e, se nessuno tiene `M` e nessun rilascio è in volo, del parent. È `badView` a rendere `memVal`
conservato: l'esclusività fa sì che ci sia un solo "detentore" alla volta. -/

namespace Normale

/-! ## 0. Lo spec sequenziale (copia di `MSI_flush_proof.lean`) -/

structure SeqState (n : Nat) where
  memory : Value
  extqueue : Fin n -> RsRqEvent

instance : Inhabited (SeqState n) where
  default := SeqState.mk default (fun _ => default)

/-- Una memoria e, per ogni cache, la coda esterna; gli eventi portano l'indice della cache come
`msi_step_external`. Richieste servite in ordine FIFO; `ld_rs v` richiede `v` uguale alla memoria,
`st_rs` scrive il valore in testa. -/
inductive seq_step : SeqState n -> MSIExternalEvent n -> SeqState n -> Prop where
  | ld_rq : ∀ (s1 : SeqState n) i,
      seq_step s1 (.cache Event.ld_rq i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.ld_rq] } s1.extqueue }
  | st_rq : ∀ (s1 : SeqState n) v i,
      seq_step s1 (.cache (Event.st_rq v) i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.st_rq v] } s1.extqueue }
  | ld_rs : ∀ (s1 : SeqState n) v i rst,
      (s1.extqueue i).rq = Event.ld_rq :: rst →
      s1.memory = v ->
      seq_step s1 (.cache (Event.ld_rs v) i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rs := (s1.extqueue i).rs ++ [Event.ld_rs v], rq := rst } s1.extqueue }
  | st_rs : ∀ (s1 : SeqState n) v i rst,
      (s1.extqueue i).rq = Event.st_rq v :: rst →
      seq_step s1 (.cache Event.st_rs i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rs := (s1.extqueue i).rs ++ [Event.st_rs],rq := rst } s1.extqueue, memory := v }

@[simp]
def seq_init (n : Nat) : SeqState n := Inhabited.default

def spec_behaviour (n : Nat) :=
  behaviour (seq_init n : SeqState n) seq_step

/-! ## 1. La proiezione `shape`: quello che le viste guardano -/

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
    queue_pc := c.queue_pc.map stripPC, extqueue := default }

def shapeParent {n} (p : ParentState n) : ParentState n :=
  { value := 0, shared_state := p.shared_state,
    queue_cip := fun k => (p.queue_cip k).map stripCP,
    queue_pci := fun k => (p.queue_pci k).map stripPC }

/-- Lo stato senza valori e senza code esterne. -/
def shape {n} (s : MSIState n) : MSIState n :=
  ⟨fun k => shapeCache (s.caches k), shapeParent s.parent⟩

@[simp] theorem isGrantM_stripPC (e : PCEvent) : isGrantM (stripPC e) = isGrantM e := by
  cases e <;> rfl
@[simp] theorem isGrantS_stripPC (e : PCEvent) : isGrantS (stripPC e) = isGrantS e := by
  cases e <;> rfl
@[simp] theorem isReleaseM_stripCP (e : CPEvent) : isReleaseM (stripCP e) = isReleaseM e := by
  cases e <;> rfl
@[simp] theorem isReleaseS_stripCP (e : CPEvent) : isReleaseS (stripCP e) = isReleaseS e := by
  cases e <;> rfl

theorem countP_grantM_strip (l : List PCEvent) :
    (l.map stripPC).countP isGrantM = l.countP isGrantM := by
  rw [List.countP_map]; congr 1; funext e; exact isGrantM_stripPC e
theorem countP_grantS_strip (l : List PCEvent) :
    (l.map stripPC).countP isGrantS = l.countP isGrantS := by
  rw [List.countP_map]; congr 1; funext e; exact isGrantS_stripPC e
theorem countP_releaseM_strip (l : List CPEvent) :
    (l.map stripCP).countP isReleaseM = l.countP isReleaseM := by
  rw [List.countP_map]; congr 1; funext e; exact isReleaseM_stripCP e
theorem countP_releaseS_strip (l : List CPEvent) :
    (l.map stripCP).countP isReleaseS = l.countP isReleaseS := by
  rw [List.countP_map]; congr 1; funext e; exact isReleaseS_stripCP e

theorem muMsgs_shape {n} (s : MSIState n) (k : Fin n) :
    muMsgs (shape s).parent k = muMsgs s.parent k := by
  simp only [muMsgs, shape, shapeParent, countP_grantM_strip, countP_releaseM_strip]

theorem sigMsgs_shape {n} (s : MSIState n) (k : Fin n) :
    sigMsgs (shape s).parent k = sigMsgs s.parent k := by
  simp only [sigMsgs, shape, shapeParent, countP_grantS_strip, countP_releaseS_strip]

/-- Le viste non guardano né i valori né le `extqueue`. -/
theorem msiView_shape {n} (s : MSIState n) (i j : Fin n) :
    msiView (shape s) i j = msiView s i j := by
  unfold msiView
  rw [muMsgs_shape, sigMsgs_shape]
  rfl

theorem synced_shape {n} {s : MSIState n} (hs : synced s) : synced (shape s) := by
  intro k
  obtain ⟨h1, h2⟩ := hs k
  exact ⟨by simp only [shape, shapeParent, shapeCache, h1],
         by simp only [shape, shapeParent, shapeCache, h2]⟩

theorem shape_default {n} : shape (default : MSIState n) = default :=
  MSIState.ext_all (fun _ => rfl) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem cache_internal_congr {c c' c'' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c') (heq : c' = c'') : cache_msi_step_internal c e c'' :=
  heq ▸ h

theorem parent_congr {n} {p p' p'' : ParentState n} {e : ParentInternalEvent n}
    (h : parent_msi_step p e p') (heq : p' = p'') : parent_msi_step p e p'' := heq ▸ h

/-- Un passo interno di cache commuta con `shape`, a meno del valore nell'etichetta: le regole non
leggono i valori se non per copiarli nei messaggi, e le `extqueue` non le toccano. -/
theorem shape_cache_internal {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c') :
    ∃ e', cache_msi_step_internal (shapeCache c) e' (shapeCache c') := by
  cases h with
  | rq_data_not_available hM =>
    exact ⟨_, cache_internal_congr (.rq_data_not_available _ hM)
      (by simp [shapeCache, stripCP, List.map_append])⟩
  | rq_data_not_available1 hS =>
    exact ⟨_, cache_internal_congr (.rq_data_not_available1 _ hS)
      (by simp [shapeCache, stripCP, List.map_append])⟩
  | upgrade_from_I_rq hI =>
    exact ⟨_, cache_internal_congr (.upgrade_from_I_rq _ hI)
      (by simp [shapeCache, stripCP, List.map_append])⟩
  | upgrade_from_I_rq1 hI =>
    exact ⟨_, cache_internal_congr (.upgrade_from_I_rq1 _ hI)
      (by simp [shapeCache, stripCP, List.map_append])⟩
  | upgrade_from_I_rs v j hj hI =>
    exact ⟨_, cache_internal_congr
      (.upgrade_from_I_rs _ 0 j (by simp [shapeCache, List.getElem?_map, hj, stripPC]) hI)
      (by simp [shapeCache, List.eraseIdx_map])⟩
  | upgrade_from_I_rsS v j hj hI =>
    exact ⟨_, cache_internal_congr
      (.upgrade_from_I_rsS _ 0 j (by simp [shapeCache, List.getElem?_map, hj, stripPC]) hI)
      (by simp [shapeCache, List.eraseIdx_map])⟩
  | downgrade_from_M_rs j hj hM =>
    exact ⟨_, cache_internal_congr
      (.downgrade_from_M_rs _ j (by simp [shapeCache, List.getElem?_map, hj, stripPC]) hM)
      (by simp [shapeCache, stripCP, List.map_append, List.eraseIdx_map])⟩
  | downgrade_from_M_rs1 j hj hS =>
    exact ⟨_, cache_internal_congr
      (.downgrade_from_M_rs1 _ j (by simp [shapeCache, List.getElem?_map, hj, stripPC]) hS)
      (by simp [shapeCache, stripCP, List.map_append, List.eraseIdx_map])⟩

/-- Estensionalità campo per campo di `ParentState` (puntuale sulle code). -/
theorem shape_parent_internal_ext {n} {a b : ParentState n} (hv : a.value = b.value)
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

/-- Un passo del parent commuta con `shape`, a meno del valore nell'etichetta. -/
theorem shape_parent_internal {n} {p p' : ParentState n} {e : ParentUpdQueueInternalEvent n}
    {i : Fin n} (h : parent_msi_step p (.upd_queue e i) p') :
    ∃ e', parent_msi_step (shapeParent p) (.upd_queue e' i) (shapeParent p') := by
  cases h with
  | downgrade_from_M_rq1 v i j hj =>
    refine ⟨.downgrade_from_M_rq1 0, parent_congr (.downgrade_from_M_rq1 (shapeParent p) 0 i j ?_) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => ?_) (fun k => rfl)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.eraseIdx_map]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | downgrade_from_M_rq2 i j hj =>
    refine ⟨.downgrade_from_S_rq1S, parent_congr (.downgrade_from_M_rq2 (shapeParent p) i j ?_) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => ?_) (fun k => rfl)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.eraseIdx_map]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_data_avilable_rq1 i j hj hall =>
    refine ⟨.upgrade_to_M_data_avilable_rq1,
      parent_congr (.upgrade_to_M_data_avilable_rq1 (shapeParent p) i j ?_ hall) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => ?_) (fun k => ?_)
      · simp only [shapeParent]
        by_cases hk : k = i
        · subst hk; simp [update_Fin_gss, List.eraseIdx_map]
        · simp [update_Fin_gso2 _ _ _ _ hk]
      · simp only [shapeParent]
        by_cases hk : k = i
        · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
        · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_data_avilable_rq2 i j hj hi hall =>
    refine ⟨.upgrade_to_S_data_avilable_rq1S,
      parent_congr (.upgrade_to_M_data_avilable_rq2 (shapeParent p) i j ?_ hi hall) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => ?_) (fun k => ?_)
      · simp only [shapeParent]
        by_cases hk : k = i
        · subst hk; simp [update_Fin_gss, List.eraseIdx_map]
        · simp [update_Fin_gso2 _ _ _ _ hk]
      · simp only [shapeParent]
        by_cases hk : k = i
        · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
        · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all i0 i j hj hrow =>
    refine ⟨.upgrade_to_M_invalid_all i0,
      parent_congr (.upgrade_to_M_invalid_all (shapeParent p) i0 i j ?_ hrow) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => rfl) (fun k => ?_)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all1 i0 i j hj hrow =>
    refine ⟨.invalid_allS,
      parent_congr (.upgrade_to_M_invalid_all1 (shapeParent p) i0 i j ?_ hrow) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => rfl) (fun k => ?_)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all2 i0 i j hj hne hrow =>
    refine ⟨.upgrade_to_S_invalid_2_rq1S i0,
      parent_congr (.upgrade_to_M_invalid_all2 (shapeParent p) i0 i j ?_ hne hrow) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => rfl) (fun k => ?_)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]
  | upgrade_to_M_invalid_all3 i0 i j hj hrow =>
    refine ⟨.upgrade_to_M_invalid_all i0,
      parent_congr (.upgrade_to_M_invalid_all3 (shapeParent p) i0 i j ?_ hrow) ?_⟩
    · simp only [shapeParent]; rw [List.getElem?_map, hj]; rfl
    · refine shape_parent_internal_ext rfl rfl (fun k => rfl) (fun k => ?_)
      simp only [shapeParent]
      by_cases hk : k = i
      · subst hk; simp [update_Fin_gss, List.map_append, stripPC]
      · simp [update_Fin_gso2 _ _ _ _ hk]

/-- Un passo interno di sistema commuta con `shape` (a meno dell'etichetta). -/
theorem shape_internal {n} {s s' : MSIState n} {t : MSIInternalEvent n}
    (h : msi_step_internal s t s') :
    ∃ t', msi_step_internal (shape s) t' (shape s') := by
  cases h with
  | cache c' i e hc =>
    obtain ⟨e', hc'⟩ := shape_cache_internal hc
    refine ⟨.cache e' i,
      msi_step_congr (msi_step_internal.cache (shape s) (shapeCache c') i e' hc') ?_⟩
    refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeCache, update_Fin_gss]
      · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · rfl
    · intro k; rfl
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
      msi_step_congr (msi_step_internal.parent_upd_queue (shape s) (shapeParent p') e' i hp') ?_⟩
    refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
    · intro k
      by_cases hk : k = i
      · subst hk; simp [shape, shapeCache, shapeParent, update_Fin_gss]
      · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · rfl
    · intro k; rfl
    · intro k; rfl
    · intro k; rfl
  | parent_no_queue _ _ _ hp => cases hp

/-- Un passo esterno non cambia `shape` (su stati `synced` il riallineamento delle copie delle code
è l'identità). -/
theorem shape_external {n} {s s' : MSIState n} {e : MSIExternalEvent n} (hs : synced s)
    (h : msi_step_external s e s') : shape s' = shape s := by
  cases h with
  | cache e c' i hc =>
    obtain ⟨hst, hcp, hpc⟩ := cache_msi_step_frame hc
    refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
    · intro k
      by_cases hk : k = i
      · subst hk
        simp [shape, shapeCache, update_Fin_gss, hst, hcp, hpc]
      · simp [shape, shapeCache, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk
        simp [shape, shapeParent, update_Fin_gss, hcp, (hs k).1]
      · simp [shape, shapeParent, update_Fin_gso2 _ _ _ _ hk]
    · intro k
      by_cases hk : k = i
      · subst hk
        simp [shape, shapeParent, update_Fin_gss, hpc, (hs k).2]
      · simp [shape, shapeParent, update_Fin_gso2 _ _ _ _ hk]

/-- Un passo esterno conserva `synced`. -/
theorem synced_ext {n} {s s' : MSIState n} {e : MSIExternalEvent n} (hs : synced s)
    (h : msi_step_external s e s') : synced s' := by
  cases h with
  | cache e c' i hc =>
    intro k
    by_cases hk : k = i
    · subst hk
      simp [update_Fin_gss]
    · simp only [update_Fin_gso2 _ _ _ _ hk]
      exact hs k

/-- Lungo una traccia (passi esterni e interni) da uno stato `synced`, `shape` resta internamente
raggiungibile da `shape` dello stato di partenza. -/
theorem shape_reach {n} {a s : MSIState n} {l : List (MSIExternalEvent n)}
    (h : star_extend msi_step_external msi_step_internal a l s) (ha : synced a) :
    synced s ∧ ReflTransGen MSI.atrans (shape a) (shape s) := by
  induction h with
  | refl => exact ⟨ha, ReflTransGen.refl⟩
  | step_int l s' s'' ie _ hstep ih =>
    obtain ⟨t', ht'⟩ := shape_internal hstep
    exact ⟨synced_step ih.1 hstep, ReflTransGen.tail ih.2 (Exists.intro t' ht')⟩
  | step_ext l s' s'' e _ hstep ih =>
    refine ⟨synced_ext ih.1 hstep, ?_⟩
    rw [shape_external ih.1 hstep]
    exact ih.2

/-- **φ lungo le tracce**: nessuno stato di una traccia da `default` ha una vista cattiva. È qui
che entra il risultato della tattica, senza ridimostrare nulla. -/
theorem noBad_of_trace {n} {s : MSIState n} {l : List (MSIExternalEvent n)}
    (h : star_extend msi_step_external msi_step_internal (default : MSIState n) l s) :
    ∀ i j, ¬ badView (msiView s i j) := by
  intro i j hb
  have hr := (shape_reach h (fun _ => ⟨rfl, rfl⟩)).2
  rw [shape_default] at hr
  exact badView_unreachable_from_default (shape s)
    ⟨i, j, by show badView (msiView (shape s) i j); rw [msiView_shape]; exact hb⟩ hr

theorem synced_of_trace {n} {s : MSIState n} {l : List (MSIExternalEvent n)}
    (h : star_extend msi_step_external msi_step_internal (default : MSIState n) l s) :
    synced s :=
  (shape_reach h (fun _ => ⟨rfl, rfl⟩)).1


/-! ## 2. Le esclusioni: cosa `badView` dice di uno stato -/

/-- "Nessuna vista cattiva" per lo stato `s`. -/
abbrev NoBad {n} (s : MSIState n) : Prop := ∀ i j, ¬ badView (msiView s i j)

theorem muMsgs_ne_zero_of_release {n} {s : MSIState n} {k : Fin n} {v : Value}
    (h : CPEvent.rsIμ v ∈ s.parent.queue_cip k) : muMsgs s.parent k ≠ 0 := by
  unfold muMsgs
  have : 0 < (s.parent.queue_cip k).countP isReleaseM :=
    List.countP_pos_iff.mpr ⟨_, h, rfl⟩
  omega

theorem muMsgs_ne_zero_of_grant {n} {s : MSIState n} {k : Fin n} {v : Value}
    (h : PCEvent.rsM v ∈ s.parent.queue_pci k) : muMsgs s.parent k ≠ 0 := by
  unfold muMsgs
  have : 0 < (s.parent.queue_pci k).countP isGrantM :=
    List.countP_pos_iff.mpr ⟨_, h, rfl⟩
  omega

theorem sigMsgs_ne_zero_of_grant {n} {s : MSIState n} {k : Fin n} {v : Value}
    (h : PCEvent.rsS v ∈ s.parent.queue_pci k) : sigMsgs s.parent k ≠ 0 := by
  unfold sigMsgs
  have : 0 < (s.parent.queue_pci k).countP isGrantS :=
    List.countP_pos_iff.mpr ⟨_, h, rfl⟩
  omega

/-- Pattern 6: la cache in `M` è registrata dal parent. -/
theorem rowM_of_M {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (hM : (s.caches k).state = Bstate.M) : s.parent.shared_state k = Bstate.M := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, Or.inr (Or.inr hne)⟩))))))

/-- Pattern 7: la cache in `S` è registrata dal parent. -/
theorem rowS_of_S {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (hS : (s.caches k).state = Bstate.S) : s.parent.shared_state k = Bstate.S := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, Or.inr (Or.inr hne)⟩)))))))

/-- Pattern 6: la cache in `M` non ha token in volo per sé. -/
theorem no_mu_of_M {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (hM : (s.caches k).state = Bstate.M) : muMsgs s.parent k = 0 := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, Or.inl (cnt_ne_zero hne)⟩))))))

theorem no_sig_of_M {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (hM : (s.caches k).state = Bstate.M) : sigMsgs s.parent k = 0 := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM, Or.inr (Or.inl (cnt_ne_zero hne))⟩))))))

/-- Pattern 4: un token `M` in volo per `k` è registrato dal parent. -/
theorem rowM_of_mu {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (h : muMsgs s.parent k ≠ 0) : s.parent.shared_state k = Bstate.M := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hne⟩))))

/-- Pattern 5: un token `S` in volo per `k` è registrato dal parent. -/
theorem rowS_of_sig {n} {s : MSIState n} (hnb : NoBad s) {k : Fin n}
    (h : sigMsgs s.parent k ≠ 0) : s.parent.shared_state k = Bstate.S := by
  by_contra hne
  exact hnb k k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt_ne_zero h, hne⟩)))))

/-- Pattern 8: la riga `M` di `i` esclude ogni altra riga. -/
theorem rowI_of_rowM {n} {s : MSIState n} (hnb : NoBad s) {i j : Fin n} (hij : i ≠ j)
    (hM : s.parent.shared_state i = Bstate.M) : s.parent.shared_state j = Bstate.I := by
  by_contra hne
  exact hnb i j (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨decide_eq_false hij, hM, hne⟩))))))))

/-- Pattern 9: la riga `S` di `i` esclude una riga `M`. -/
theorem not_rowM_of_rowS {n} {s : MSIState n} (hnb : NoBad s) {i j : Fin n} (hij : i ≠ j)
    (hS : s.parent.shared_state i = Bstate.S) : s.parent.shared_state j ≠ Bstate.M := by
  intro hM
  exact hnb i j (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨decide_eq_false hij, hS, hM⟩)))))))))


/-! ## 3. Il valore della linea e la relazione di simulazione -/

/-- `m` è il valore della linea in `s`: ogni detentore (cache in `M` o in `S`, token in volo) porta
`m`, e il parent porta `m` se nessuno tiene `M` e nessun rilascio è in volo. -/
structure memVal {n} (s : MSIState n) (m : Value) : Prop where
  cacheM : ∀ k, (s.caches k).state = Bstate.M → (s.caches k).value = m
  cacheS : ∀ k, (s.caches k).state = Bstate.S → (s.caches k).value = m
  release : ∀ k v, CPEvent.rsIμ v ∈ s.parent.queue_cip k → v = m
  grantM : ∀ k v, PCEvent.rsM v ∈ s.parent.queue_pci k → v = m
  grantS : ∀ k v, PCEvent.rsS v ∈ s.parent.queue_pci k → v = m
  parent : (∀ k, (s.caches k).state ≠ Bstate.M) →
    (∀ k v, CPEvent.rsIμ v ∉ s.parent.queue_cip k) → s.parent.value = m

/-- La relazione di simulazione: stesse code esterne, memoria dello spec = valore della linea. -/
def sim {n} (i : MSIState n) (s : SeqState n) : Prop :=
  (∀ k, s.extqueue k = (i.caches k).extqueue) ∧ memVal i s.memory

theorem memVal_default {n} : memVal (default : MSIState n) 0 where
  cacheM := fun _ _ => rfl
  cacheS := fun _ h => by cases h
  release := fun _ _ h => by cases h
  grantM := fun _ _ h => by cases h
  grantS := fun _ _ h => by cases h
  parent := fun _ _ => rfl

theorem sim_default {n} : sim (default : MSIState n) (seq_init n) :=
  ⟨fun _ => rfl, memVal_default⟩

/-- Passo di cache: `memVal` per lo stato di arrivo, dato che la nuova cache `c'` porta `m` e che,
se non tiene `M` e non ha rilasci in coda, nemmeno la vecchia li aveva. -/
theorem memVal_internal_cache {n} {s : MSIState n} {i : Fin n} {c' : CacheState} {m : Value}
    (hm : memVal s m)
    (hM : c'.state = Bstate.M → c'.value = m)
    (hS : c'.state = Bstate.S → c'.value = m)
    (hrel : ∀ v, CPEvent.rsIμ v ∈ c'.queue_cp → v = m)
    (hgM : ∀ v, PCEvent.rsM v ∈ c'.queue_pc → v = m)
    (hgS : ∀ v, PCEvent.rsS v ∈ c'.queue_pc → v = m)
    (hpar : c'.state ≠ Bstate.M → (∀ v, CPEvent.rsIμ v ∉ c'.queue_cp) →
      (s.caches i).state ≠ Bstate.M ∧ ∀ v, CPEvent.rsIμ v ∉ s.parent.queue_cip i) :
    memVal { s with caches := update_Fin i c' s.caches,
                    parent.queue_cip := update_Fin i c'.queue_cp s.parent.queue_cip,
                    parent.queue_pci := update_Fin i c'.queue_pc s.parent.queue_pci } m where
  cacheM k hk := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hk ⊢; exact hM hk
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢; exact hm.cacheM k hk
  cacheS k hk := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hk ⊢; exact hS hk
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢; exact hm.cacheS k hk
  release k v hv := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hv; exact hrel v hv
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hv; exact hm.release k v hv
  grantM k v hv := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hv; exact hgM v hv
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hv; exact hm.grantM k v hv
  grantS k v hv := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hv; exact hgS v hv
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hv; exact hm.grantS k v hv
  parent hM' hrel' := by
    have hMi := hM' i
    have hreli := fun v => hrel' i v
    simp only [update_Fin_gss] at hMi hreli
    obtain ⟨h1, h2⟩ := hpar hMi hreli
    refine hm.parent (fun k => ?_) (fun k v => ?_)
    · by_cases hki : k = i
      · subst hki; exact h1
      · have := hM' k; simp only [update_Fin_gso2 _ _ _ _ hki] at this; exact this
    · by_cases hki : k = i
      · subst hki; exact h2 v
      · have := hrel' k v; simp only [update_Fin_gso2 _ _ _ _ hki] at this; exact this

/-- Passo del parent: `memVal` per lo stato di arrivo, dato il nuovo parent `p'` (le cache non
cambiano stato né valore, cambia solo la copia delle code all'indice `i`). -/
theorem memVal_internal_parent {n} {s : MSIState n} {i : Fin n} {p' : ParentState n} {m : Value}
    (hm : memVal s m)
    (hrel : ∀ k v, CPEvent.rsIμ v ∈ p'.queue_cip k → v = m)
    (hgM : ∀ k v, PCEvent.rsM v ∈ p'.queue_pci k → v = m)
    (hgS : ∀ k v, PCEvent.rsS v ∈ p'.queue_pci k → v = m)
    (hpar : (∀ k, (s.caches k).state ≠ Bstate.M) → (∀ k v, CPEvent.rsIμ v ∉ p'.queue_cip k) →
      p'.value = m) :
    memVal { s with
      caches := update_Fin i { s.caches i with queue_cp := p'.queue_cip i, queue_pc := p'.queue_pci i } s.caches,
      parent := p' } m where
  cacheM k hk := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hk ⊢; exact hm.cacheM _ hk
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢; exact hm.cacheM k hk
  cacheS k hk := by
    by_cases hki : k = i
    · subst hki; simp only [update_Fin_gss] at hk ⊢; exact hm.cacheS _ hk
    · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢; exact hm.cacheS k hk
  release := hrel
  grantM := hgM
  grantS := hgS
  parent hM' hrel' := hpar (fun k => by
      have := hM' k
      by_cases hki : k = i
      · subst hki; simp only [update_Fin_gss] at this; exact this
      · simp only [update_Fin_gso2 _ _ _ _ hki] at this; exact this) hrel'

/-- **Stutter**: un passo interno conserva il valore della linea. Servono `synced` (le regole di
cache leggono la loro copia della coda) e le esclusioni di `badView` (per i grant: il parent porta
`m` perché nessuno tiene `M` e nessun rilascio è in volo). -/
theorem memVal_internal {n} {s s' : MSIState n} {t : MSIInternalEvent n} {m : Value}
    (hs : synced s) (hnb : NoBad s) (hm : memVal s m) (h : msi_step_internal s t s') :
    memVal s' m := by
  cases h with
  | cache c' i e hc =>
    have hcp : s.parent.queue_cip i = (s.caches i).queue_cp := (hs i).1
    have hpc : s.parent.queue_pci i = (s.caches i).queue_pc := (hs i).2
    have hrelI : ∀ v, CPEvent.rsIμ v ∈ (s.caches i).queue_cp → v = m :=
      fun v hv => hm.release i v (by rw [hcp]; exact hv)
    have hgMI : ∀ v, PCEvent.rsM v ∈ (s.caches i).queue_pc → v = m :=
      fun v hv => hm.grantM i v (by rw [hpc]; exact hv)
    have hgSI : ∀ v, PCEvent.rsS v ∈ (s.caches i).queue_pc → v = m :=
      fun v hv => hm.grantS i v (by rw [hpc]; exact hv)
    -- un rilascio nella copia lato parent sta nella copia lato cache
    have hcpI : ∀ v, CPEvent.rsIμ v ∈ s.parent.queue_cip i → CPEvent.rsIμ v ∈ (s.caches i).queue_cp :=
      fun v hv => by rw [← hcp]; exact hv
    cases hc with
    | rq_data_not_available hM =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · nofun
      · nofun
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, CPEvent.rsIμ.injEq] at hv
        rcases hv with hv | hv
        · exact hrelI v hv
        · rw [hv]; exact hm.cacheM i hM
      · exact hgMI
      · exact hgSI
      · intro _ hno; exact (hno (s.caches i).value (by simp)).elim
    | rq_data_not_available1 hS =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · nofun
      · nofun
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
        exact hrelI v hv
      · exact hgMI
      · exact hgSI
      · intro _ hno
        exact ⟨by simp [hS], fun v hv => hno v (List.mem_append_left _ (hcpI v hv))⟩
    | upgrade_from_I_rq hI =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · intro h; simp [hI] at h
      · intro h; simp [hI] at h
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
        exact hrelI v hv
      · exact hgMI
      · exact hgSI
      · intro _ hno
        exact ⟨by simp [hI], fun v hv => hno v (List.mem_append_left _ (hcpI v hv))⟩
    | upgrade_from_I_rq1 hI =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · intro h; simp [hI] at h
      · intro h; simp [hI] at h
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
        exact hrelI v hv
      · exact hgMI
      · exact hgSI
      · intro _ hno
        exact ⟨by simp [hI], fun v hv => hno v (List.mem_append_left _ (hcpI v hv))⟩
    | upgrade_from_I_rs v j hj hI =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · intro _; exact hgMI v (List.mem_of_getElem? hj)
      · nofun
      · exact hrelI
      · exact fun v' hv => hgMI v' (List.mem_of_mem_eraseIdx hv)
      · exact fun v' hv => hgSI v' (List.mem_of_mem_eraseIdx hv)
      · intro h _; exact absurd rfl h
    | upgrade_from_I_rsS v j hj hI =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · nofun
      · intro _; exact hgSI v (List.mem_of_getElem? hj)
      · exact hrelI
      · exact fun v' hv => hgMI v' (List.mem_of_mem_eraseIdx hv)
      · exact fun v' hv => hgSI v' (List.mem_of_mem_eraseIdx hv)
      · intro _ hno
        exact ⟨by simp [hI], fun v hv => hno v (hcpI v hv)⟩
    | downgrade_from_M_rs j hj hM =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · nofun
      · nofun
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, CPEvent.rsIμ.injEq] at hv
        rcases hv with hv | hv
        · exact hrelI v hv
        · rw [hv]; exact hm.cacheM i hM
      · exact fun v' hv => hgMI v' (List.mem_of_mem_eraseIdx hv)
      · exact fun v' hv => hgSI v' (List.mem_of_mem_eraseIdx hv)
      · intro _ hno; exact (hno (s.caches i).value (by simp)).elim
    | downgrade_from_M_rs1 j hj hS =>
      refine memVal_internal_cache hm ?_ ?_ ?_ ?_ ?_ ?_
      · nofun
      · nofun
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
        exact hrelI v hv
      · exact fun v' hv => hgMI v' (List.mem_of_mem_eraseIdx hv)
      · exact fun v' hv => hgSI v' (List.mem_of_mem_eraseIdx hv)
      · intro _ hno
        exact ⟨by simp [hS], fun v hv => hno v (List.mem_append_left _ (hcpI v hv))⟩
  | parent_upd_queue p' e i hp =>
    -- se nessuna riga è `M`, il parent porta `m`: nessuna cache tiene `M` (pattern 6) e nessun
    -- rilascio è in volo (pattern 4)
    have hpv : (∀ k, ¬ s.parent.shared_state k = Bstate.M) → s.parent.value = m := fun hI =>
      hm.parent (fun k hk => hI k (rowM_of_M hnb hk))
        (fun k v hv => hI k (rowM_of_mu hnb (muMsgs_ne_zero_of_release hv)))
    cases hp with
    | downgrade_from_M_rq1 v i j hj =>
      refine memVal_internal_parent hm ?_ ?_ ?_ ?_
      · intro k v' hv
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hv
          exact hm.release _ v' (List.mem_of_mem_eraseIdx hv)
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.release k v' hv
      · exact hm.grantM
      · exact hm.grantS
      · intro _ _; exact hm.release i v (List.mem_of_getElem? hj)
    | downgrade_from_M_rq2 i j hj =>
      refine memVal_internal_parent hm ?_ ?_ ?_ ?_
      · intro k v' hv
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hv
          exact hm.release _ v' (List.mem_of_mem_eraseIdx hv)
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.release k v' hv
      · exact hm.grantM
      · exact hm.grantS
      · intro hM' hno
        refine hm.parent hM' (fun k v hv => hno k v ?_)
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss]
          obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hv
          exact List.mem_eraseIdx_iff_getElem?.mpr ⟨j', fun hjj => by subst hjj; simp [hj] at hj', hj'⟩
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hv
    | upgrade_to_M_data_avilable_rq1 i j hj hall =>
      have hv0 : s.parent.value = m := hpv (fun k hk => Bstate.noConfusion ((hall k).symm.trans hk))
      refine memVal_internal_parent hm ?_ ?_ ?_ ?_
      · intro k v' hv
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hv
          exact hm.release _ v' (List.mem_of_mem_eraseIdx hv)
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.release k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, PCEvent.rsM.injEq] at hv
          rcases hv with hv | hv
          · exact hm.grantM _ v' hv
          · rw [hv]; exact hv0
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantS _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
      · intro _ _; exact hv0
    | upgrade_to_M_data_avilable_rq2 i j hj hIi hnoM =>
      have hv0 : s.parent.value = m := hpv hnoM
      refine memVal_internal_parent hm ?_ ?_ ?_ ?_
      · intro k v' hv
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hv
          exact hm.release _ v' (List.mem_of_mem_eraseIdx hv)
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.release k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantM _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, PCEvent.rsS.injEq] at hv
          rcases hv with hv | hv
          · exact hm.grantS _ v' hv
          · rw [hv]; exact hv0
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
      · intro _ _; exact hv0
    | upgrade_to_M_invalid_all i0 i j hj hM =>
      refine memVal_internal_parent hm hm.release ?_ ?_ (fun hM' hno => hm.parent hM' hno)
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantM _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantS _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
    | upgrade_to_M_invalid_all1 i0 i j hj hS =>
      refine memVal_internal_parent hm hm.release ?_ ?_ (fun hM' hno => hm.parent hM' hno)
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantM _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantS _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
    | upgrade_to_M_invalid_all2 i0 i j hj hne hS =>
      refine memVal_internal_parent hm hm.release ?_ ?_ (fun hM' hno => hm.parent hM' hno)
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantM _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantS _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
    | upgrade_to_M_invalid_all3 i0 i j hj hM =>
      refine memVal_internal_parent hm hm.release ?_ ?_ (fun hM' hno => hm.parent hM' hno)
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantM _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantM k v' hv
      · intro k v' hv
        by_cases hk : k = i
        · subst hk
          simp only [update_Fin_gss, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
          exact hm.grantS _ v' hv
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hv; exact hm.grantS k v' hv
  | parent_no_queue p' e i hp => cases hp

/-- Un passo interno non tocca le `extqueue`. -/
theorem extqueue_internal {n} {s s' : MSIState n} {t : MSIInternalEvent n}
    (h : msi_step_internal s t s') : ∀ k, (s'.caches k).extqueue = (s.caches k).extqueue := by
  cases h with
  | cache c' i e hc =>
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [update_Fin_gss]
      cases hc <;> rfl
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | parent_upd_queue p' e i hp =>
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [update_Fin_gss]
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | parent_no_queue p' e i hp => cases hp

theorem sim_internal {n} {i i' : MSIState n} {s : SeqState n} {t : MSIInternalEvent n}
    (hs : synced i) (hnb : NoBad i) (hsim : sim i s) (h : msi_step_internal i t i') : sim i' s :=
  ⟨fun k => (hsim.1 k).trans (extqueue_internal h k).symm, memVal_internal hs hnb hsim.2 h⟩

/-- Su uno stato `synced` il riallineamento delle code del parent dopo un passo esterno è
l'identità: lo stato di arrivo cambia solo la cache `p`. -/
theorem sim_external_parent {n} {s : MSIState n} {c' : CacheState} {e : Event} {p : Fin n}
    (hs : synced s) (hc : cache_msi_step (s.caches p) e c') :
    ({ s with caches := update_Fin p c' s.caches,
              parent.queue_cip := update_Fin p c'.queue_cp s.parent.queue_cip,
              parent.queue_pci := update_Fin p c'.queue_pc s.parent.queue_pci } : MSIState n)
      = { s with caches := update_Fin p c' s.caches } := by
  obtain ⟨_, hcp, hpc⟩ := cache_msi_step_frame hc
  obtain ⟨h1, h2⟩ := hs p
  rw [hcp, hpc, ← h1, ← h2, update_Fin_self, update_Fin_self]

/-- Le code esterne dello spec seguono quelle dell'implementazione. -/
theorem sim_external_extq {n} {i : MSIState n} {s : SeqState n}
    (hq : ∀ k, s.extqueue k = (i.caches k).extqueue) (p : Fin n) (c' : CacheState)
    (q : RsRqEvent) (hc : c'.extqueue = q) :
    ∀ k, update_Fin p q s.extqueue k = (update_Fin p c' i.caches k).extqueue := by
  intro k
  by_cases hk : k = p
  · rw [hk, update_Fin_gss, update_Fin_gss, hc]
  · rw [update_Fin_gso2 _ _ _ _ hk, update_Fin_gso2 _ _ _ _ hk]
    exact hq k

/-- Se la cache `p` non cambia né stato né valore, il valore della linea resta `m`. -/
theorem sim_external_memVal_same {n} {i : MSIState n} {m : Value} (hm : memVal i m)
    (p : Fin n) (c' : CacheState)
    (hst : c'.state = (i.caches p).state) (hv : c'.value = (i.caches p).value) :
    memVal { i with caches := update_Fin p c' i.caches } m where
  cacheM := fun k hk => by
    by_cases hkp : k = p
    · rw [hkp] at hk ⊢
      simp only [update_Fin_gss] at hk ⊢
      rw [hv]; exact hm.cacheM p (hst.symm.trans hk)
    · simp only [update_Fin_gso2 _ _ _ _ hkp] at hk ⊢
      exact hm.cacheM k hk
  cacheS := fun k hk => by
    by_cases hkp : k = p
    · rw [hkp] at hk ⊢
      simp only [update_Fin_gss] at hk ⊢
      rw [hv]; exact hm.cacheS p (hst.symm.trans hk)
    · simp only [update_Fin_gso2 _ _ _ _ hkp] at hk ⊢
      exact hm.cacheS k hk
  release := fun k v h => hm.release k v h
  grantM := fun k v h => hm.grantM k v h
  grantS := fun k v h => hm.grantS k v h
  parent := fun hM hrel => hm.parent (fun k => by
    have hk := hM k
    by_cases hkp : k = p
    · rw [hkp] at hk ⊢
      simp only [update_Fin_gss] at hk
      rwa [hst] at hk
    · simp only [update_Fin_gso2 _ _ _ _ hkp] at hk
      exact hk) hrel

/-- Con la cache `p` in `M` nessun altro indice è registrato dal parent. -/
theorem sim_external_rowI {n} {i : MSIState n} (hnb : NoBad i) {p : Fin n}
    (hM : (i.caches p).state = Bstate.M) {k : Fin n} (hk : ¬ k = p) :
    i.parent.shared_state k = Bstate.I :=
  rowI_of_rowM hnb (fun h => hk h.symm) (rowM_of_M hnb hM)

/-- La store servita in `M`: il nuovo valore `v` della cache `p` è il valore della linea, perché la
cache in `M` è l'unico detentore (nessun'altra cache in `M`/`S`, nessun token in volo). -/
theorem sim_external_memVal_store {n} {i : MSIState n} (hnb : NoBad i) {p : Fin n}
    (hM : (i.caches p).state = Bstate.M) (c' : CacheState) {v : Value}
    (hst : c'.state = Bstate.M) (hv : c'.value = v) :
    memVal { i with caches := update_Fin p c' i.caches } v where
  cacheM := fun k hk => by
    by_cases hkp : k = p
    · rw [hkp]
      simp only [update_Fin_gss]
      exact hv
    · simp only [update_Fin_gso2 _ _ _ _ hkp] at hk
      exact absurd (rowM_of_M hnb hk) (by rw [sim_external_rowI hnb hM hkp]; simp)
  cacheS := fun k hk => by
    by_cases hkp : k = p
    · rw [hkp] at hk
      simp only [update_Fin_gss] at hk
      rw [hst] at hk
      cases hk
    · simp only [update_Fin_gso2 _ _ _ _ hkp] at hk
      exact absurd (rowS_of_S hnb hk) (by rw [sim_external_rowI hnb hM hkp]; simp)
  release := fun k v' h => by
    have hne : muMsgs i.parent k ≠ 0 := muMsgs_ne_zero_of_release (s := i) h
    by_cases hkp : k = p
    · rw [hkp] at hne
      exact absurd (no_mu_of_M hnb hM) hne
    · exact absurd (rowM_of_mu hnb hne) (by rw [sim_external_rowI hnb hM hkp]; simp)
  grantM := fun k v' h => by
    have hne : muMsgs i.parent k ≠ 0 := muMsgs_ne_zero_of_grant (s := i) h
    by_cases hkp : k = p
    · rw [hkp] at hne
      exact absurd (no_mu_of_M hnb hM) hne
    · exact absurd (rowM_of_mu hnb hne) (by rw [sim_external_rowI hnb hM hkp]; simp)
  grantS := fun k v' h => by
    have hne : sigMsgs i.parent k ≠ 0 := sigMsgs_ne_zero_of_grant (s := i) h
    by_cases hkp : k = p
    · rw [hkp] at hne
      exact absurd (no_sig_of_M hnb hM) hne
    · exact absurd (rowS_of_sig hnb hne) (by rw [sim_external_rowI hnb hM hkp]; simp)
  parent := fun hM' _ => by
    have hk := hM' p
    simp only [update_Fin_gss] at hk
    exact absurd hst hk

/-- **Simulazione dei passi esterni**: ogni passo esterno dell'implementazione da uno stato
`synced` senza viste cattive è simulato da un passo dello spec. Le richieste accodano; la load
servita (in `S` o in `M`) restituisce il valore della cache, che è il valore della linea; la store
servita (in `M`) scrive `v`, che diventa il nuovo valore della linea perché la cache in `M` è l'unico
detentore. -/
theorem sim_external {n} {i i' : MSIState n} {s : SeqState n} {e : MSIExternalEvent n}
    (hs : synced i) (hnb : NoBad i) (hsim : sim i s) (h : msi_step_external i e i') :
    ∃ s', seq_step s e s' ∧ sim i' s' := by
  cases h with
  | cache e c' p hc =>
    obtain ⟨hq, hm⟩ := hsim
    rw [sim_external_parent hs hc]
    cases hc with
    | ld_rq =>
      exact ⟨_, seq_step.ld_rq s p,
        ⟨sim_external_extq hq p _ _ (by rw [hq p]), sim_external_memVal_same hm p _ rfl rfl⟩⟩
    | st_rq v =>
      exact ⟨_, seq_step.st_rq s v p,
        ⟨sim_external_extq hq p _ _ (by rw [hq p]), sim_external_memVal_same hm p _ rfl rfl⟩⟩
    | ld_rq_data_available1 rst hrq hS =>
      exact ⟨_, seq_step.ld_rs s _ p rst (by rw [hq p]; exact hrq) (hm.cacheS p hS).symm,
        ⟨sim_external_extq hq p _ _ (by rw [hq p]), sim_external_memVal_same hm p _ rfl rfl⟩⟩
    | ld_rq_data_available rst hrq hM =>
      exact ⟨_, seq_step.ld_rs s _ p rst (by rw [hq p]; exact hrq) (hm.cacheM p hM).symm,
        ⟨sim_external_extq hq p _ _ (by rw [hq p]), sim_external_memVal_same hm p _ rfl rfl⟩⟩
    | st_rq_M_state v rst hrq hM =>
      exact ⟨_, seq_step.st_rs s v p rst (by rw [hq p]; exact hrq),
        ⟨sim_external_extq hq p _ _ (by rw [hq p]), sim_external_memVal_store hnb hM _ hM rfl⟩⟩

/-! ## 4. La dimostrazione nello stile di `FormalMSI.SI`

Come nel file `SI`: una struttura `φ i s` con le clausole della relazione fra implementazione e
spec, un lemma per i passi esterni (`enough`), uno per i passi interni (`enough_internal`),
l'induzione sulla traccia (`enough_star`), lo stato iniziale (`φ_init`) e il teorema
(`trace_inclusion`). Le clausole di `φ`:
* `ext`: le code esterne coincidono (come in `SI`);
* `val`: le clausole di `flush` rese valide ad ogni passo. In `SI` erano "la memoria del parent è
  quella dello spec, e chi tiene la linea (cache in `S`, `rsS` in volo) porta quel valore"; qui, dove
  le cache scrivono, sono `memVal`: la memoria dello spec è il valore della linea, portato da chi la
  tiene (cache in `M` o `S`, `rsIμ`/`rsM`/`rsS` in volo) e dal parent quando nessuno tiene `M` e nessun
  rilascio è in volo. Su uno stato flushed si riducono a `parent.value = memory`;
* `conn`: `synced` (le `connections` di `SI`);
* `reach`: **`badView`** al posto della `ψ` scritta a mano di `SI`. La clausola tiene il risultato
  della tattica (`badView_unreachable_from_default`) attraverso `shape`; `φ.noBad` ne ricava
  "nessuna vista cattiva", e `badView_is_invariant_internal`/`_external` sono gli analoghi di
  `ψ_is_invariant_internal`/`_external`, senza rifare a mano la chiusura dei 13 pattern. -/

structure φ {n} (i : MSIState n) (s : SeqState n) : Prop where
  ext : ∀ c, (i.caches c).extqueue = s.extqueue c
  val : memVal i s.memory
  conn : synced i
  reach : ReflTransGen MSI.atrans (default : MSIState n) (shape i)

/-- Da `reach`: nessuna vista cattiva (`badView_unreachable`, letto attraverso `shape`). -/
theorem φ.noBad {n} {i : MSIState n} {s : SeqState n} (h : φ i s) : NoBad i :=
  fun a b hb => badView_unreachable_from_default (shape i)
    ⟨a, b, by show badView (msiView (shape i) a b); rw [msiView_shape]; exact hb⟩ h.reach

/-- Analogo di `ψ_is_invariant_internal`: la parte strutturale di `φ` (`synced` e `badView`) è
conservata da un passo interno. -/
theorem badView_is_invariant_internal {n} {i i' : MSIState n} {e : MSIInternalEvent n}
    (hc : synced i) (hr : ReflTransGen MSI.atrans (default : MSIState n) (shape i))
    (h : msi_step_internal i e i') :
    synced i' ∧ ReflTransGen MSI.atrans (default : MSIState n) (shape i') := by
  obtain ⟨t', ht'⟩ := shape_internal h
  exact ⟨synced_step hc h, ReflTransGen.tail hr (Exists.intro t' ht')⟩

/-- Analogo di `ψ_is_invariant_external`. -/
theorem badView_is_invariant_external {n} {i i' : MSIState n} {e : MSIExternalEvent n}
    (hc : synced i) (hr : ReflTransGen MSI.atrans (default : MSIState n) (shape i))
    (h : msi_step_external i e i') :
    synced i' ∧ ReflTransGen MSI.atrans (default : MSIState n) (shape i') := by
  refine ⟨synced_ext hc h, ?_⟩
  rw [shape_external hc h]
  exact hr

/-- **Passi interni** (`enough_internal` di `SI`): lo spec sta fermo e `φ` si conserva. -/
theorem enough_internal {n} {i i' : MSIState n} {s : SeqState n} {e : MSIInternalEvent n}
    (h : φ i s) (hstep : msi_step_internal i e i') : φ i' s := by
  obtain ⟨hc', hr'⟩ := badView_is_invariant_internal h.conn h.reach hstep
  exact ⟨fun c => (extqueue_internal hstep c).trans (h.ext c),
         memVal_internal h.conn h.noBad h.val hstep, hc', hr'⟩

/-- **Passi esterni** (`enough` di `SI`): lo spec fa il passo corrispondente e `φ` si conserva. -/
theorem enough {n} {i i' : MSIState n} {s : SeqState n} {e : MSIExternalEvent n}
    (h : φ i s) (hstep : msi_step_external i e i') : ∃ s', seq_step s e s' ∧ φ i' s' := by
  obtain ⟨s', hs', hsim'⟩ := sim_external h.conn h.noBad ⟨fun c => (h.ext c).symm, h.val⟩ hstep
  obtain ⟨hc', hr'⟩ := badView_is_invariant_external h.conn h.reach hstep
  exact ⟨s', hs', fun c => (hsim'.1 c).symm, hsim'.2, hc', hr'⟩

/-- **Induzione sulla traccia** (`enough_star` di `SI`). -/
theorem enough_star {n} {i i' : MSIState n} {s : SeqState n} {l : List (MSIExternalEvent n)}
    (h : φ i s) (hstar : star_extend msi_step_external msi_step_internal i l i') :
    ∃ s', star seq_step s l s' ∧ φ i' s' := by
  induction hstar with
  | refl => exact ⟨s, star.refl _, h⟩
  | step_int l a b ie _ hstep ih =>
    obtain ⟨s', hs', hφ⟩ := ih
    exact ⟨s', hs', enough_internal hφ hstep⟩
  | step_ext l a b e _ hstep ih =>
    obtain ⟨s', hs', hφ⟩ := ih
    obtain ⟨s'', hs'', hφ'⟩ := enough hφ hstep
    exact ⟨s'', star.step _ _ _ _ _ hs' hs'', hφ'⟩

theorem φ_init {n} : φ (default : MSIState n) (seq_init n) :=
  ⟨fun _ => rfl, memVal_default, fun _ => ⟨rfl, rfl⟩, by rw [shape_default]⟩

/-- **Inclusione delle tracce** (`trace_inclusion` di `SI`). -/
theorem trace_inclusion {n} (l : List (MSIExternalEvent n)) :
    imp_behaviour n l → spec_behaviour n l := by
  rintro ⟨i', hstar⟩
  obtain ⟨s', hs', _⟩ := enough_star φ_init hstar
  exact Exists.intro s' hs'

end Normale
