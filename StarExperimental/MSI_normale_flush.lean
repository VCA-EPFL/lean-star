import StarExperimental.MSI_normale_list

open THEORY
open Relation
open MSIView
open Normale


/-! # `MSI_normale_flush`: il tentativo con soli `badView` e `flush`

Stesso obiettivo di `MSI_normale.lean` (inclusione delle tracce per induzione sulla traccia, senza
ARS), ma con la relazione di simulazione costruita **solo** con `flush` di `MSI_flush_proof.lean`:

  `simF i s := (le code esterne coincidono) ∧ ∃ i₀, flush i₀ s ∧ i₀ →* i`

cioè "`i` è raggiungibile con passi interni da uno stato flushed per `s`" (l'ancora flushed sta
*dietro* a `i`: così un passo interno conserva la relazione senza bisogno del diamante). φ è
`badView` (`Normale.noBad_of_trace`). L'uguaglianza delle code esterne non è un invariante
dell'implementazione: è la parte di stato che spec e implementazione condividono, e senza di essa
lo spec non può nemmeno servire una load (la sua guardia legge la testa di `rq`).

Risultato del tentativo:
* stato iniziale, passi interni, richieste `ld_rq`/`st_rq` e servizi `ld_rs`: **dimostrati**. Per le
  load il valore servito è una *conseguenza* di `flush` lungo il cammino interno (`memVal_path`):
  in uno stato flushed solo il parent porta un valore, e i passi interni lo copiano soltanto;
* la store `st_rs v`: **impossibile**, non per difficoltà di prova ma perché la relazione è falsa:
  dopo la store la cache in `M` porta `v` e il parent ancora il valore vecchio, mentre lungo ogni
  cammino interno da uno stato flushed per `memory = v` il parent porta sempre `v`
  (`parent_val_path`). È `store_breaks_simF`. L'unico rimedio è dire dove sta il valore *adesso*
  (`memVal` in `MSI_normale.lean`) oppure mettere l'ancora *davanti* (`φ_ind` di ARS), che però
  richiede il diamante per i passi interni.

`trace_inclusion_flush` in fondo mostra la struttura dell'induzione con il solo caso della store
lasciato aperto (`sorry`), a fianco del teorema che dice che non si può chiudere. -/

namespace NormaleFlush

/-! ## 1. `flush` e la relazione `simF` -/

/-- `flush` di `MSI_flush_proof.lean` (copia letterale): nessun messaggio in volo, tutte le cache
in `I`, directory tutta a `I`, valore del parent uguale alla memoria dello spec. -/
inductive flush {n} (i : MSIState n) (s : SeqState n) : Prop where
  | intro :
      (∀ k, (i.caches k).state = Bstate.I ∧ (i.caches k).queue_cp = [] ∧ (i.caches k).queue_pc = []) →
      (∀ k, i.parent.shared_state k = Bstate.I ∧ i.parent.queue_cip k = [] ∧ i.parent.queue_pci k = []) →
      i.parent.value = s.memory →
      flush i s

/-- La relazione di simulazione: code esterne uguali, e `i` raggiungibile con passi interni da uno
stato flushed per `s`. -/
def simF {n} (i : MSIState n) (s : SeqState n) : Prop :=
  (∀ k, s.extqueue k = (i.caches k).extqueue) ∧ ∃ i₀, flush i₀ s ∧ ReflTransGen MSI.atrans i₀ i

theorem flush_default {n} : flush (default : MSIState n) (seq_init n) :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

theorem simF_default {n} : simF (default : MSIState n) (seq_init n) :=
  ⟨fun _ => rfl, default, flush_default, ReflTransGen.refl⟩

/-- **Passi interni**: gratis, l'ancora resta la stessa. -/
theorem simF_internal {n} {i i' : MSIState n} {s : SeqState n} {t : MSIInternalEvent n}
    (h : msi_step_internal i t i') (hs : simF i s) : simF i' s :=
  let ⟨hq, i₀, hf, hp⟩ := hs
  ⟨fun k => (hq k).trans (extqueue_internal h k).symm, i₀, hf, ReflTransGen.tail hp (Exists.intro t h)⟩


/-! ## 2. Cosa segue da `flush` lungo un cammino interno -/

theorem flush_synced {n} {i : MSIState n} {s : SeqState n} (hf : flush i s) : synced i := by
  obtain ⟨hc, hp, _⟩ := hf
  intro k
  rw [(hc k).2.1, (hc k).2.2, (hp k).2.1, (hp k).2.2]
  exact ⟨rfl, rfl⟩

/-- Uno stato flushed ha la forma dello stato iniziale. -/
theorem shape_flush {n} {i : MSIState n} {s : SeqState n} (hf : flush i s) : shape i = default := by
  obtain ⟨hc, hp, _⟩ := hf
  refine MSIState.ext_all ?_ rfl ?_ ?_ ?_
  · intro k
    obtain ⟨h1, h2, h3⟩ := hc k
    simp [shape, shapeCache, h1, h2, h3]
    rfl
  · intro k; exact (hp k).1
  · intro k; exact congrArg (List.map stripCP) (hp k).2.1
  · intro k; exact congrArg (List.map stripPC) (hp k).2.2

/-- In uno stato flushed la memoria dello spec è il valore della linea, banalmente: solo il parent
lo porta. -/
theorem memVal_of_flush {n} {i : MSIState n} {s : SeqState n} (hf : flush i s) :
    memVal i s.memory := by
  obtain ⟨hc, hp, hv⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ _ => hv⟩
  · intro k hM; rw [(hc k).1] at hM; cases hM
  · intro k hS; rw [(hc k).1] at hS; cases hS
  · intro k v h; rw [(hp k).2.1] at h; cases h
  · intro k v h; rw [(hp k).2.2] at h; cases h
  · intro k v h; rw [(hp k).2.2] at h; cases h

/-- Lungo un cammino interno da uno stato flushed per `s`: `synced`, nessuna vista cattiva, e la
memoria dello spec resta il valore della linea. È qui che `badView` fa il suo lavoro (tramite
`memVal_internal`), e il tutto è una conseguenza di `flush`. -/
theorem path_facts {n} {i₀ i : MSIState n} {s : SeqState n} (hf : flush i₀ s)
    (hp : ReflTransGen MSI.atrans i₀ i) :
    synced i ∧ NoBad i ∧ memVal i s.memory := by
  have key : ∀ x, ReflTransGen MSI.atrans i₀ x →
      synced x ∧ ReflTransGen MSI.atrans (default : MSIState n) (shape x) ∧ memVal x s.memory := by
    intro x hx
    induction hx with
    | refl => exact ⟨flush_synced hf, by rw [shape_flush hf], memVal_of_flush hf⟩
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      obtain ⟨hs, hr, hm⟩ := ih
      have hnb : NoBad _ := fun a b hb =>
        badView_unreachable_from_default (shape _)
          ⟨a, b, by show badView (msiView (shape _) a b); rw [msiView_shape]; exact hb⟩ hr
      obtain ⟨t', ht'⟩ := shape_internal ht
      exact ⟨synced_step hs ht, ReflTransGen.tail hr (Exists.intro t' ht'), memVal_internal hs hnb hm ht⟩
  obtain ⟨hs, hr, hm⟩ := key i hp
  refine ⟨hs, fun a b hb => ?_, hm⟩
  exact badView_unreachable_from_default (shape i)
    ⟨a, b, by show badView (msiView (shape i) a b); rw [msiView_shape]; exact hb⟩ hr

/-- Il valore del parent cambia solo consumando un `rsIμ`, che porta il valore della linea. -/
theorem parent_val_step {n} {x x' : MSIState n} {t : MSIInternalEvent n} {m : Value}
    (hm : memVal x m) (h : msi_step_internal x t x') (hv : x.parent.value = m) :
    x'.parent.value = m := by
  cases h with
  | cache c' i e hc => exact hv
  | parent_upd_queue p' e i hp =>
    cases hp with
    | downgrade_from_M_rq1 v i j hj => exact hm.release i v (List.mem_of_getElem? hj)
    | downgrade_from_M_rq2 => exact hv
    | upgrade_to_M_data_avilable_rq1 => exact hv
    | upgrade_to_M_data_avilable_rq2 => exact hv
    | upgrade_to_M_invalid_all => exact hv
    | upgrade_to_M_invalid_all1 => exact hv
    | upgrade_to_M_invalid_all2 => exact hv
    | upgrade_to_M_invalid_all3 => exact hv
  | parent_no_queue p' e i hp => cases hp

/-- **Lungo un cammino interno da uno stato flushed il parent porta sempre la memoria dello spec.**
È la proprietà che la store viola. -/
theorem parent_val_path {n} {i₀ i : MSIState n} {s : SeqState n} (hf : flush i₀ s)
    (hp : ReflTransGen MSI.atrans i₀ i) : i.parent.value = s.memory := by
  induction hp with
  | refl => exact hf.3
  | tail hpre hstep ih =>
    obtain ⟨t, ht⟩ := hstep
    exact parent_val_step (path_facts hf hpre).2.2 ht ih


/-! ## 3. I passi esterni: le code esterne non contano per i passi interni -/

/-- Cambiare la coda esterna della cache `k`. -/
def setExt {n} (i : MSIState n) (k : Fin n) (q : RsRqEvent) : MSIState n :=
  { i with caches := update_Fin k { i.caches k with extqueue := q } i.caches }

/-- Le regole interne di cache non guardano `extqueue`. -/
theorem cache_internal_setExt {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c') (q : RsRqEvent) :
    cache_msi_step_internal { c with extqueue := q } e { c' with extqueue := q } := by
  cases h with
  | rq_data_not_available hM => exact .rq_data_not_available _ hM
  | rq_data_not_available1 hS => exact .rq_data_not_available1 _ hS
  | upgrade_from_I_rq hI => exact .upgrade_from_I_rq _ hI
  | upgrade_from_I_rq1 hI => exact .upgrade_from_I_rq1 _ hI
  | upgrade_from_I_rs v j hj hI => exact .upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact .upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM => exact .downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS => exact .downgrade_from_M_rs1 _ j hj hS

theorem step_setExt {n} {a b : MSIState n} {t : MSIInternalEvent n} (h : msi_step_internal a t b)
    (k : Fin n) (q : RsRqEvent) : msi_step_internal (setExt a k q) t (setExt b k q) := by
  cases h with
  | cache c' i e hc =>
    by_cases hk : i = k
    · subst hk
      refine msi_step_congr (msi_step_internal.cache (setExt a i q) { c' with extqueue := q } i e ?_) ?_
      · simp only [setExt, update_Fin_gss]
        exact cache_internal_setExt hc q
      · refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
        · intro j; simp only [setExt, update_Fin_update_Fin_same, update_Fin_gss]
        · intro j; rfl
        · intro j; rfl
    · refine msi_step_congr (msi_step_internal.cache (setExt a k q) c' i e ?_) ?_
      · simp only [setExt, update_Fin_gso2 _ _ _ _ hk]
        exact hc
      · refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        intro j
        simp only [setExt]
        by_cases hj : j = i
        · subst hj; simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hk]
        · by_cases hjk : j = k
          · subst hjk; simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hj]
          · simp only [update_Fin_gso2 _ _ _ _ hj, update_Fin_gso2 _ _ _ _ hjk]
  | parent_upd_queue p' e i hp =>
    refine msi_step_congr (msi_step_internal.parent_upd_queue (setExt a k q) p' e i hp) ?_
    refine MSIState.ext_all ?_ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro j
    simp only [setExt]
    by_cases hj : j = i
    · subst hj
      by_cases hjk : j = k
      · subst hjk; simp only [update_Fin_gss]
      · simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hjk]
    · by_cases hjk : j = k
      · subst hjk; simp only [update_Fin_gss, update_Fin_gso2 _ _ _ _ hj]
      · simp only [update_Fin_gso2 _ _ _ _ hj, update_Fin_gso2 _ _ _ _ hjk]
  | parent_no_queue p' e i hp => cases hp

theorem reach_setExt {n} {a b : MSIState n} (h : ReflTransGen MSI.atrans a b) (k : Fin n)
    (q : RsRqEvent) : ReflTransGen MSI.atrans (setExt a k q) (setExt b k q) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨t, ht⟩ := hstep
    exact ReflTransGen.tail ih (Exists.intro t (step_setExt ht k q))

/-- `flush` non guarda le code esterne. -/
theorem flush_setExt {n} {i : MSIState n} {s s' : SeqState n} (hf : flush i s)
    (hm : s'.memory = s.memory) (k : Fin n) (q : RsRqEvent) : flush (setExt i k q) s' := by
  obtain ⟨hc, hp, hv⟩ := hf
  refine ⟨?_, hp, hv.trans hm.symm⟩
  intro j
  simp only [setExt]
  by_cases hj : j = k
  · subst hj; simp only [update_Fin_gss]; exact hc j
  · simp only [update_Fin_gso2 _ _ _ _ hj]; exact hc j

/-- Un passo esterno che non cambia `value` è un `setExt` (su stati `synced`). -/
theorem ext_eq_setExt {n} {i : MSIState n} {k : Fin n} {e : Event} {c' : CacheState}
    (hs : synced i) (hc : cache_msi_step (i.caches k) e c') (hv : c'.value = (i.caches k).value) :
    { i with caches := update_Fin k c' i.caches,
             parent.queue_cip := update_Fin k c'.queue_cp i.parent.queue_cip,
             parent.queue_pci := update_Fin k c'.queue_pc i.parent.queue_pci }
      = setExt i k c'.extqueue := by
  obtain ⟨hst, hcp, hpc⟩ := cache_msi_step_frame hc
  have hcache : c' = { i.caches k with extqueue := c'.extqueue } := by
    cases c'
    simp only at hst hcp hpc hv
    simp [hst, hcp, hpc, hv]
  refine MSIState.ext_all ?_ rfl (fun _ => rfl) ?_ ?_
  · intro j; simp only [setExt]; rw [← hcache]
  · intro j; simp only [setExt]; rw [hcp, ← (hs k).1, update_Fin_self]
  · intro j; simp only [setExt]; rw [hpc, ← (hs k).2, update_Fin_self]

/-- **Richieste e load**: simulate, con l'ancora spostata sulla stessa coda esterna. Per la load il
valore servito è il valore della linea, che è la memoria dello spec (`path_facts`). -/
theorem simF_external_nonstore {n} {i i' : MSIState n} {s : SeqState n} {e : Event} {k : Fin n}
    (hs : simF i s) (h : msi_step_external i (.cache e k) i') (hne : e ≠ Event.st_rs) :
    ∃ s', seq_step s (.cache e k) s' ∧ simF i' s' := by
  obtain ⟨hq, i₀, hf, hp⟩ := hs
  have hsync : synced i := (path_facts hf hp).1
  have hm : memVal i s.memory := (path_facts hf hp).2.2
  obtain ⟨c', hc, rfl⟩ := ext_inv h
  -- lo spec fa il passo corrispondente; la memoria non cambia
  have hspec : ∃ s', seq_step s (.cache e k) s' ∧ s'.memory = s.memory
      ∧ ∀ j, s'.extqueue j = (update_Fin k c' i.caches j).extqueue := by
    cases hc with
    | ld_rq =>
      refine ⟨_, seq_step.ld_rq s k, rfl, ?_⟩
      intro j; by_cases hj : j = k
      · subst hj; simp only [update_Fin_gss, hq j]
      · simp only [update_Fin_gso2 _ _ _ _ hj, hq j]
    | st_rq v =>
      refine ⟨_, seq_step.st_rq s v k, rfl, ?_⟩
      intro j; by_cases hj : j = k
      · subst hj; simp only [update_Fin_gss, hq j]
      · simp only [update_Fin_gso2 _ _ _ _ hj, hq j]
    | ld_rq_data_available1 rst hrq hS =>
      refine ⟨_, seq_step.ld_rs s _ k rst (by rw [hq k]; exact hrq) (hm.cacheS k hS).symm, rfl, ?_⟩
      intro j; by_cases hj : j = k
      · subst hj; simp only [update_Fin_gss, hq j]
      · simp only [update_Fin_gso2 _ _ _ _ hj, hq j]
    | ld_rq_data_available rst hrq hM =>
      refine ⟨_, seq_step.ld_rs s _ k rst (by rw [hq k]; exact hrq) (hm.cacheM k hM).symm, rfl, ?_⟩
      intro j; by_cases hj : j = k
      · subst hj; simp only [update_Fin_gss, hq j]
      · simp only [update_Fin_gso2 _ _ _ _ hj, hq j]
    | st_rq_M_state v rst hrq hM => exact absurd rfl hne
  obtain ⟨s', hstep, hmem, hq'⟩ := hspec
  -- il valore della cache non cambia (non è una store), quindi lo stato di arrivo è un `setExt`
  have hv : c'.value = (i.caches k).value := by
    cases hc with
    | st_rq_M_state v rst hrq hM => exact absurd rfl hne
    | _ => rfl
  refine ⟨s', hstep, hq', setExt i₀ k c'.extqueue, flush_setExt hf hmem k _, ?_⟩
  rw [ext_eq_setExt hsync hc hv]
  exact reach_setExt hp k _


/-! ## 4. La store: dove `flush` non basta -/

/-- **Ostruzione.** Se la store scrive un valore diverso da quello corrente della linea, nessuno
stato flushed per la nuova memoria può precedere lo stato di arrivo: dopo la store il parent porta
ancora il valore vecchio, e lungo un cammino interno da uno stato flushed per `v` il parent porta
`v` (`parent_val_path`). Quindi `simF` non è una relazione di simulazione, qualunque cosa si
dimostri di `badView`. -/
theorem store_breaks_simF {n} {i i' : MSIState n} {s : SeqState n} {k : Fin n} {v : Value}
    (hs : simF i s) (h : msi_step_external i (.cache Event.st_rs k) i')
    (hchg : v ≠ s.memory) (hv : (i'.caches k).value = v) :
    ∀ s', s'.memory = v → ¬ simF i' s' := by
  intro s' hs' ⟨_, i₁, hf₁, hp₁⟩
  obtain ⟨hq, i₀, hf, hp⟩ := hs
  -- il parent di `i'` è quello di `i`, che porta `s.memory`
  have hpar : i'.parent.value = i.parent.value := by
    obtain ⟨c', hc, rfl⟩ := ext_inv h
    rfl
  have h1 : i.parent.value = s.memory := parent_val_path hf hp
  -- ma per `simF i' s'` dovrebbe portare `v`
  have h2 : i'.parent.value = s'.memory := parent_val_path hf₁ hp₁
  rw [hs', hpar, h1] at h2
  exact hchg h2.symm

/-- **Ostruzione generale.** Nessuna relazione che imponga `parent.value = memory` in *ogni* stato
può essere conservata da una store che cambia il valore, perché la store non tocca il parent.
Copre `flush` (clausola `parent.value = s.memory`), `flushInv` di `MSI_flush_proof.lean` (clausola
`value`, incondizionata: giusta lungo i cammini interni, falsa dopo una store esterna) e `simF`
(tramite `parent_val_path`). L'unico rimedio è condizionare la clausola sul parent a "nessuna cache
in `M` e nessun `rsIμ` in volo": è la clausola `parent` di `memVal`. -/
theorem store_breaks_parent_eq {n} (R : MSIState n → SeqState n → Prop)
    (hR : ∀ i s, R i s → i.parent.value = s.memory)
    {i i' : MSIState n} {s : SeqState n} {k : Fin n} {v : Value}
    (h : msi_step_external i (.cache Event.st_rs k) i') (hi : R i s) (hchg : v ≠ s.memory) :
    ∀ s', s'.memory = v → ¬ R i' s' := by
  intro s' hs' hi'
  have hpar : i'.parent.value = i.parent.value := by
    obtain ⟨c', hc, rfl⟩ := ext_inv h
    rfl
  have h1 := hR i s hi
  have h2 := hR i' s' hi'
  rw [hs', hpar, h1] at h2
  exact hchg h2.symm

/-- `simF` è un caso dell'ostruzione generale. -/
theorem store_breaks_simF' {n} {i i' : MSIState n} {s : SeqState n} {k : Fin n} {v : Value}
    (hs : simF i s) (h : msi_step_external i (.cache Event.st_rs k) i') (hchg : v ≠ s.memory) :
    ∀ s', s'.memory = v → ¬ simF i' s' :=
  store_breaks_parent_eq simF (fun _ _ ⟨_, _, hf, hp⟩ => parent_val_path hf hp) h hs hchg

/-- L'induzione sulla traccia con `simF`: tutto chiuso tranne la store. Il `sorry` non è una
lacuna di prova: `store_breaks_simF` dice che in quel caso la relazione è falsa. -/
theorem trace_inclusion_flush {n} (l : List (MSIExternalEvent n)) :
    imp_behaviour n l → spec_behaviour n l := by
  rintro ⟨s, hs⟩
  suffices key : ∀ a i : MSIState n, ∀ l, star_extend msi_step_external msi_step_internal a l i →
      a = default → ∃ q, star seq_step (seq_init n) l q ∧ simF i q by
    obtain ⟨q, hq, _⟩ := key _ _ _ hs rfl
    exact Exists.intro q hq
  intro a i l h
  induction h with
  | refl => intro ha; subst ha; exact ⟨seq_init n, star.refl _, simF_default⟩
  | step_int l s' s'' ie _ hstep ih =>
    intro ha
    obtain ⟨q, hq, hsim⟩ := ih ha
    exact ⟨q, hq, simF_internal hstep hsim⟩
  | step_ext l s' s'' e _ hstep ih =>
    intro ha
    obtain ⟨q, hq, hsim⟩ := ih ha
    obtain ⟨ev, k⟩ := e
    by_cases hne : ev = Event.st_rs
    · -- la store: non chiudibile con `simF` (vedi `store_breaks_simF`)
      sorry
    · obtain ⟨q', hq', hsim'⟩ := simF_external_nonstore hsim hstep hne
      exact ⟨q', star.step _ _ _ _ _ hq hq', hsim'⟩

end NormaleFlush
