import StarExperimental.MESI_def
import Star.Commute.ARS
import StarExperimental.SumListLemmas

/-! # `MESI_flush_proof`: l'inclusione delle tracce di MESI nello spec sequenziale

Stessa struttura di `MSI_flush_proof.lean`, da cui questo file è derivato: relazioni di ARS
istanziate su MESI, ritorno a flush (`flushInv`, tre fasi con misure), confluenza sui raggiungibili
(`cohInv`, valore logico `LV`, stato canonico), commutazione a meno di passi interni, e
`trace_inclusion` via `ReachingStar.trace_inclusion`. Rispetto a MSI cambia solo ciò che dipende da
`E`: i token esclusivi contano insieme `M` ed `E` (cache in `M` o `E`, grant `rsM` o `rsE`,
rilascio `rsIμ`), e le righe `M` ed `E` della directory sono trattate allo stesso modo, perché il
passaggio `E → M` è silenzioso. I lemmi generici su somme e liste sono in `SumListLemmas.lean`,
condivisi con MSI. -/

open THEORY
open Relation
open ReachingStar (Rule Method trans_refl relation_flush relation_flush_method relation_method
  relation_init φ_ind)

namespace MESI

/-! ## Code sincronizzate e predicati sui messaggi (come `MSIView` per MSI) -/

/-- Grant di un token *esclusivo*: `rsM` o `rsE`. -/
def isGrantX : PCEvent → Bool
  | .rsM _ => true
  | .rsE _ => true
  | .rsS _ => false
  | .rqIμ => false
  | .rqIσ => false

def isGrantS : PCEvent → Bool
  | .rsS _ => true
  | .rsM _ => false
  | .rsE _ => false
  | .rqIμ => false
  | .rqIσ => false

/-- Rilascio di un token esclusivo (da `M` o da `E`): `rsIμ`. -/
def isReleaseX : CPEvent → Bool
  | .rsIμ _ => true
  | .rsIσ => false
  | .rqS => false
  | .rqM => false

def isReleaseS : CPEvent → Bool
  | .rsIσ => true
  | .rsIμ _ => false
  | .rqS => false
  | .rqM => false

/-- Le due copie di ogni coda (lato parent e lato cache) coincidono. -/
def synced (s : MESIState n) : Prop :=
  ∀ k, s.parent.queue_cip k = (s.caches k).queue_cp ∧ s.parent.queue_pci k = (s.caches k).queue_pc

/-- Un passo del parent modifica solo l'indice dell'evento. -/
theorem parent_step_local {p1 p2 : ParentState n} {e i}
    (h : parent_mesi_step p1 (.upd_queue e i) p2) :
    ∀ k, ¬(k = i) → p2.queue_cip k = p1.queue_cip k ∧ p2.queue_pci k = p1.queue_pci k
                    ∧ p2.shared_state k = p1.shared_state k := by
  cases h <;> intro k hk <;>
    exact ⟨by simp [update_Fin_gso2 _ _ _ _ hk], by simp [update_Fin_gso2 _ _ _ _ hk],
           by simp [update_Fin_gso2 _ _ _ _ hk]⟩

theorem synced_step {s s' : MESIState n} {t} (hs : synced s) (h : mesi_step_internal s t s') :
    synced s' := by
  cases h with
  | cache cache' p e hc =>
      intro k
      by_cases hk : k = p
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2]
  | parent_upd_queue parent' e q hp =>
      intro k
      by_cases hk : k = q
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        obtain ⟨h3, h4, _⟩ := parent_step_local hp k hk
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2, h3, h4]

/-- Le regole interne di MSI come `Rule` del framework: un passo interno con una qualunque
etichetta. È `MSI.atrans` (`msi_rule_eq_atrans`). -/
def mesi_rule (n : Nat) : Rule (MESIState n) := fun a b => ∃ e, mesi_step_internal a e b

theorem mesi_rule_of_step {a b : MESIState n} {e : MESIInternalEvent n}
    (h : mesi_step_internal a e b) : mesi_rule n a b :=
  Exists.intro e h

/-- `relation_init` di ARS per `flush0`: ogni stato iniziale di MSI è flushed rispetto a `seq_init n`. -/
theorem mesi_relation_init0 (i : MESIState n) (hi : mesi_init i) :
    relation_init flush0 i (seq_init n) := by
  unfold relation_init
  obtain ⟨hc, hp, hv⟩ := hi
  constructor
  · intro k
    obtain ⟨h1, h2, h3, _, _, _⟩ := hc k
    exact ⟨h1, h2, h3⟩
  · intro k
    exact hp k
  · rw [hv]; rfl


/-! ## `relation_flush` di ARS per MSI: ritorno a flush0 da ogni stato raggiunto con passi interni

Strategia. `flushInv x s` è un invariante degli stati raggiunti con passi interni da uno stato
flushed per `s`: code sincronizzate (`synced`), *token* (se la riga `k` della directory è
`M`, il token `M` di `k` è da qualche parte: la cache `k` è in `M`, o c'è un grant `rsM` in volo per
`k`, o un rilascio `rsIμ` di `k` in volo; lo stesso per `S`) e *valori* (il valore del parent, quelli
delle cache non in `I`, quelli dei grant e dei rilasci `rsIμ` in volo sono tutti `s.memory`: i passi
interni non introducono valori nuovi). `flushInv` vale negli stati flushed ed è conservato dai
passi interni. Da uno stato `flushInv` si torna a flush0 in tre fasi, ognuna con una misura che
decresce strettamente:
1. `μ1 = Σ_k (3·grant in volo per k + 2·[cache k non in I] + rilasci in volo di k)`: una cache in
   `M`/`S` rilascia spontaneamente; un rilascio in volo viene preso dal parent; un grant in volo
   (con tutte le cache in `I`) viene preso dalla cache. A `μ1 = 0` tutte le cache sono in `I`, non ci
   sono grant né rilasci e, per i token, tutte le righe sono a `I`.
2. `μ2 = Σ_k richieste rqM/rqS pendenti di k`: una richiesta si consuma con grant → presa del grant →
   rilascio spontaneo → presa del rilascio (quattro passi), tornando a `μ1 = 0`.
3. `μ3 = Σ_k invalidate rqIμ/rqIσ stantii per k`: un invalidate stantio si consuma riprendendo prima
   lo stato che chiede (`rqM`, grant, presa, poi `downgrade_from_M_rs`, poi presa del rilascio).
A misure nulle lo stato è flushed. Il modello indicizza le code per posizione (`[j]?`), quindi
nessun messaggio resta bloccato dietro un altro. -/

section ReturnToFlush

/-- Messaggi parent → cache che sono grant. -/
def isGrant : PCEvent → Bool
  | .rsM _ => true
  | .rsS _ => true
  | .rsE _ => true
  | .rqIμ => false
  | .rqIσ => false

/-- Messaggi parent → cache che sono invalidate. -/
def isInval : PCEvent → Bool
  | .rsM _ => false
  | .rsS _ => false
  | .rsE _ => false
  | .rqIμ => true
  | .rqIσ => true

/-- Messaggi cache → parent che sono rilasci. -/
def isRelease : CPEvent → Bool
  | .rsIμ _ => true
  | .rsIσ => true
  | .rqS => false
  | .rqM => false

/-- Messaggi cache → parent che sono richieste. -/
def isRequest : CPEvent → Bool
  | .rsIμ _ => false
  | .rsIσ => false
  | .rqS => true
  | .rqM => true

/-- Il token `M` dell'indice `k` è da qualche parte. -/
def tokenM (x : MESIState n) (k : Fin n) : Prop :=
  ((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
    ∨ (∃ v, PCEvent.rsM v ∈ (x.caches k).queue_pc) ∨ (∃ v, PCEvent.rsE v ∈ (x.caches k).queue_pc)
    ∨ (∃ v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp)

/-- Il token `S` dell'indice `k` è da qualche parte. -/
def tokenS (x : MESIState n) (k : Fin n) : Prop :=
  (x.caches k).state = Bstate.S ∨ (∃ v, PCEvent.rsS v ∈ (x.caches k).queue_pc)
    ∨ CPEvent.rsIσ ∈ (x.caches k).queue_cp

/-- L'invariante degli stati raggiunti con passi interni da uno stato flushed per `s`. -/
structure flushInv (x : MESIState n) (s : SeqState n) : Prop where
  synced : synced x
  rowM : ∀ k, (x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E) → tokenM x k
  rowS : ∀ k, x.parent.shared_state k = Bstate.S → tokenS x k
  value : x.parent.value = s.memory
  cacheVal : ∀ k, (x.caches k).state ≠ Bstate.I → (x.caches k).value = s.memory
  grantVal : ∀ k v, (PCEvent.rsM v ∈ (x.caches k).queue_pc ∨ PCEvent.rsS v ∈ (x.caches k).queue_pc
      ∨ PCEvent.rsE v ∈ (x.caches k).queue_pc) → v = s.memory
  releaseVal : ∀ k v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp → v = s.memory

/-- Il contributo dell'indice `k` alla misura della fase 1. -/
def m1 (x : MESIState n) (k : Fin n) : Nat :=
  3 * (x.caches k).queue_pc.countP isGrant
    + 2 * (if (x.caches k).state = Bstate.I then 0 else 1)
    + (x.caches k).queue_cp.countP isRelease

def μ1 (x : MESIState n) : Nat := Finset.univ.sum (fun k => m1 x k)
def μ2 (x : MESIState n) : Nat := Finset.univ.sum (fun k => (x.caches k).queue_cp.countP isRequest)
def μ3 (x : MESIState n) : Nat := Finset.univ.sum (fun k => (x.caches k).queue_pc.countP isInval)

/-! ### Lemmi di supporto su somme e liste: in `SumListLemmas.lean` -/

/-! ### L'invariante: vale negli stati flushed ed è conservato dai passi interni -/

theorem inv_of_flush {x : MESIState n} {s : SeqState n} (hf : flush0 x s) : flushInv x s := by
  obtain ⟨hc, hp, hv⟩ := hf
  refine ⟨?_, ?_, ?_, hv, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨_, hcp, hpc⟩ := hc k
    obtain ⟨_, hcip, hpci⟩ := hp k
    exact ⟨by rw [hcip, hcp], by rw [hpci, hpc]⟩
  · intro k hk
    rcases hk with hk | hk <;> (rw [(hp k).1] at hk; cases hk)
  · intro k hk
    rw [(hp k).1] at hk
    cases hk
  · intro k hk
    exact absurd (hc k).1 hk
  · intro k v hv'
    rcases hv' with hv' | hv' | hv' <;> (rw [(hc k).2.2] at hv'; simp at hv')
  · intro k v hv'
    rw [(hc k).2.1] at hv'
    simp at hv'

/-- Il token `M` di una cache è conservato da ogni passo interno della cache. -/
theorem inv_step_cache_aux1 {s1 c' : CacheState} {e : CacheInternalEvent}
    (h : cache_mesi_step_internal s1 e c')
    (ht : s1.state = Bstate.M ∨ (∃ v, PCEvent.rsM v ∈ s1.queue_pc)
      ∨ (∃ v, CPEvent.rsIμ v ∈ s1.queue_cp)) :
    c'.state = Bstate.M ∨ (∃ v, PCEvent.rsM v ∈ c'.queue_pc)
      ∨ (∃ v, CPEvent.rsIμ v ∈ c'.queue_cp) := by
  cases h with
  | rq_data_not_available hM =>
    exact Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)
  | rq_data_not_available1 hS =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩)
  | rq_data_not_availableE hE =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hE.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩)
  | upgrade_from_I_rq hI =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩)
  | upgrade_from_I_rq1 hI =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩)
  | upgrade_from_I_rs v j hj hI => exact Or.inl rfl
  | upgrade_from_I_rsS v j hj hI =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨u, hu⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr ⟨u, hu⟩)
  | upgrade_from_I_rsE v j hj hI =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨u, hu⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr ⟨u, hu⟩)
  | upgrade_from_E hE => exact Or.inl rfl
  | downgrade_from_M_rs j hj hM =>
    exact Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)
  | downgrade_from_E_rs j hj hE =>
    exact Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)
  | downgrade_from_M_rs1 j hj hS =>
    rcases ht with h1 | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩)

/-- Il token `S` di una cache è conservato da ogni passo interno della cache. -/
theorem inv_step_cache_aux2 {s1 c' : CacheState} {e : CacheInternalEvent}
    (h : cache_mesi_step_internal s1 e c')
    (ht : s1.state = Bstate.S ∨ (∃ v, PCEvent.rsS v ∈ s1.queue_pc) ∨ CPEvent.rsIσ ∈ s1.queue_cp) :
    c'.state = Bstate.S ∨ (∃ v, PCEvent.rsS v ∈ c'.queue_pc) ∨ CPEvent.rsIσ ∈ c'.queue_cp := by
  cases h with
  | rq_data_not_available hM =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hM.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | rq_data_not_available1 hS =>
    exact Or.inr (Or.inr (List.mem_append_right _ (List.mem_singleton_self _)))
  | rq_data_not_availableE hE =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hE.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | upgrade_from_I_rq hI =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | upgrade_from_I_rq1 hI =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | upgrade_from_I_rs v j hj hI =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr hv)
  | upgrade_from_I_rsS v j hj hI => exact Or.inl rfl
  | upgrade_from_I_rsE v j hj hI =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr hv)
  | upgrade_from_E hE =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hE.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr hv)
  | downgrade_from_M_rs j hj hM =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hM.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | downgrade_from_E_rs j hj hE =>
    rcases ht with h1 | ⟨w, hw⟩ | hv
    · exact Bstate.noConfusion (hE.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
  | downgrade_from_M_rs1 j hj hS =>
    exact Or.inr (Or.inr (List.mem_append_right _ (List.mem_singleton_self _)))

/-- Un passo interno della cache non aggiunge messaggi a `queue_pc`. -/
theorem inv_step_cache_aux4 {s1 c' : CacheState} {e : CacheInternalEvent}
    (h : cache_mesi_step_internal s1 e c') (a : PCEvent) (ha : a ∈ c'.queue_pc) :
    a ∈ s1.queue_pc := by
  cases h with
  | rq_data_not_available hM => exact ha
  | rq_data_not_available1 hS => exact ha
  | rq_data_not_availableE hE => exact ha
  | upgrade_from_I_rq hI => exact ha
  | upgrade_from_I_rq1 hI => exact ha
  | upgrade_from_I_rs v j hj hI => exact List.mem_of_mem_eraseIdx ha
  | upgrade_from_I_rsS v j hj hI => exact List.mem_of_mem_eraseIdx ha
  | upgrade_from_I_rsE v j hj hI => exact List.mem_of_mem_eraseIdx ha
  | upgrade_from_E hE => exact ha
  | downgrade_from_M_rs j hj hM => exact List.mem_of_mem_eraseIdx ha
  | downgrade_from_E_rs j hj hE => exact List.mem_of_mem_eraseIdx ha
  | downgrade_from_M_rs1 j hj hS => exact List.mem_of_mem_eraseIdx ha

/-- I rilasci `rsIμ v` in `queue_cp` portano il valore della memoria dello spec. -/
theorem inv_step_cache_aux5 {s1 c' : CacheState} {e : CacheInternalEvent} {m : Value}
    (h : cache_mesi_step_internal s1 e c')
    (hcv : s1.state ≠ Bstate.I → s1.value = m)
    (hrv : ∀ v, CPEvent.rsIμ v ∈ s1.queue_cp → v = m) :
    ∀ v, CPEvent.rsIμ v ∈ c'.queue_cp → v = m := by
  cases h with
  | rq_data_not_available hM =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · obtain rfl := CPEvent.rsIμ.inj (List.mem_singleton.mp h1)
      exact hcv (fun hh => Bstate.noConfusion (hM.symm.trans hh))
  | rq_data_not_available1 hS =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · exact CPEvent.noConfusion (List.mem_singleton.mp h1)
  | rq_data_not_availableE hE =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · obtain rfl := CPEvent.rsIμ.inj (List.mem_singleton.mp h1)
      exact hcv (fun hh => Bstate.noConfusion (hE.symm.trans hh))
  | upgrade_from_I_rq hI =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · exact CPEvent.noConfusion (List.mem_singleton.mp h1)
  | upgrade_from_I_rq1 hI =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · exact CPEvent.noConfusion (List.mem_singleton.mp h1)
  | upgrade_from_I_rs v j hj hI => exact hrv
  | upgrade_from_I_rsS v j hj hI => exact hrv
  | upgrade_from_I_rsE v j hj hI => exact hrv
  | upgrade_from_E hE => exact hrv
  | downgrade_from_M_rs j hj hM =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · obtain rfl := CPEvent.rsIμ.inj (List.mem_singleton.mp h1)
      exact hcv (fun hh => Bstate.noConfusion (hM.symm.trans hh))
  | downgrade_from_E_rs j hj hE =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · obtain rfl := CPEvent.rsIμ.inj (List.mem_singleton.mp h1)
      exact hcv (fun hh => Bstate.noConfusion (hE.symm.trans hh))
  | downgrade_from_M_rs1 j hj hS =>
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrv v h1
    · exact CPEvent.noConfusion (List.mem_singleton.mp h1)

/-- Ausiliario di `inv_step_cache`: il token esclusivo (`M` o `E`) di una cache, nella forma a
cinque disgiunti di `tokenM`, è conservato da ogni passo interno della cache. -/
theorem inv_step_cache_aux6 {s1 c' : CacheState} {e : CacheInternalEvent}
    (h : cache_mesi_step_internal s1 e c')
    (ht : (s1.state = Bstate.M ∨ s1.state = Bstate.E) ∨ (∃ v, PCEvent.rsM v ∈ s1.queue_pc)
      ∨ (∃ v, PCEvent.rsE v ∈ s1.queue_pc) ∨ (∃ v, CPEvent.rsIμ v ∈ s1.queue_cp)) :
    (c'.state = Bstate.M ∨ c'.state = Bstate.E) ∨ (∃ v, PCEvent.rsM v ∈ c'.queue_pc)
      ∨ (∃ v, PCEvent.rsE v ∈ c'.queue_pc) ∨ (∃ v, CPEvent.rsIμ v ∈ c'.queue_cp) := by
  cases h with
  | rq_data_not_available hM =>
    exact Or.inr (Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩))
  | rq_data_not_available1 hS =>
    rcases ht with (h1 | h1) | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, hw⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩))
  | rq_data_not_availableE hE =>
    exact Or.inr (Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩))
  | upgrade_from_I_rq hI =>
    rcases ht with (h1 | h1) | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, hw⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩))
  | upgrade_from_I_rq1 hI =>
    rcases ht with (h1 | h1) | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, hw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, hw⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩))
  | upgrade_from_I_rs v j hj hI => exact Or.inl (Or.inl rfl)
  | upgrade_from_I_rsS v j hj hI =>
    rcases ht with (h1 | h1) | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨u, hu⟩
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Bstate.noConfusion (hI.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨u, hu⟩))
  | upgrade_from_I_rsE v j hj hI => exact Or.inl (Or.inr rfl)
  | upgrade_from_E hE => exact Or.inl (Or.inl rfl)
  | downgrade_from_M_rs j hj hM =>
    exact Or.inr (Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩))
  | downgrade_from_E_rs j hj hE =>
    exact Or.inr (Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩))
  | downgrade_from_M_rs1 j hj hS =>
    rcases ht with (h1 | h1) | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨v, hv⟩
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Bstate.noConfusion (hS.symm.trans h1)
    · exact Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, mem_eraseIdx_of_ne hw hj (fun hh => PCEvent.noConfusion hh)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, List.mem_append_left _ hv⟩))

/-- Ausiliario di `inv_step_cache`: come `inv_step_cache_aux3`, ma con l'ipotesi sui grant che
copre anche `rsE` (è la forma di `flushInv.grantVal`), necessaria per `upgrade_from_I_rsE`. -/
theorem inv_step_cache_aux7 {s1 c' : CacheState} {e : CacheInternalEvent} {m : Value}
    (h : cache_mesi_step_internal s1 e c')
    (hcv : s1.state ≠ Bstate.I → s1.value = m)
    (hgv : ∀ v, (PCEvent.rsM v ∈ s1.queue_pc ∨ PCEvent.rsS v ∈ s1.queue_pc
      ∨ PCEvent.rsE v ∈ s1.queue_pc) → v = m) :
    c'.state ≠ Bstate.I → c'.value = m := by
  cases h with
  | rq_data_not_available hM => intro hne; exact (hne rfl).elim
  | rq_data_not_available1 hS => intro hne; exact (hne rfl).elim
  | rq_data_not_availableE hE => intro hne; exact (hne rfl).elim
  | upgrade_from_I_rq hI => intro hne; exact hcv hne
  | upgrade_from_I_rq1 hI => intro hne; exact hcv hne
  | upgrade_from_I_rs v j hj hI => intro _; exact hgv v (Or.inl (List.mem_of_getElem? hj))
  | upgrade_from_I_rsS v j hj hI =>
    intro _; exact hgv v (Or.inr (Or.inl (List.mem_of_getElem? hj)))
  | upgrade_from_I_rsE v j hj hI =>
    intro _; exact hgv v (Or.inr (Or.inr (List.mem_of_getElem? hj)))
  | upgrade_from_E hE => intro _; exact hcv (fun hh => Bstate.noConfusion (hE.symm.trans hh))
  | downgrade_from_M_rs j hj hM => intro hne; exact (hne rfl).elim
  | downgrade_from_E_rs j hj hE => intro hne; exact (hne rfl).elim
  | downgrade_from_M_rs1 j hj hS => intro hne; exact (hne rfl).elim


theorem inv_step_cache {x : MESIState n} {s : SeqState n} {k : Fin n} {e : CacheInternalEvent}
    {c' : CacheState} (hI : flushInv x s) (h : cache_mesi_step_internal (x.caches k) e c') :
    flushInv { x with caches := update_Fin k c' x.caches,
                      parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                      parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } s := by
  obtain ⟨hsync, hM, hS, hval, hcv, hgv, hrv⟩ := hI
  have hsync' := synced_step hsync (mesi_step_internal.cache x c' k e h)
  refine ⟨hsync', ?_, ?_, hval, ?_, ?_, ?_⟩
  · intro k' hk'
    unfold tokenM
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
      exact inv_step_cache_aux6 h (hM _ hk')
    · simp only [update_Fin_gso2 _ _ _ _ hk]
      exact hM _ hk'
  · intro k' hk'
    unfold tokenS
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
      exact inv_step_cache_aux2 h (hS _ hk')
    · simp only [update_Fin_gso2 _ _ _ _ hk]
      exact hS _ hk'
  · intro k' hne
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hne ⊢
      exact inv_step_cache_aux7 h (hcv _) (hgv _) hne
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hne ⊢
      exact hcv _ hne
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact hgv _ v (hv.imp (inv_step_cache_aux4 h _)
        (fun h' => h'.imp (inv_step_cache_aux4 h _) (inv_step_cache_aux4 h _)))
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hgv _ v hv
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact inv_step_cache_aux5 h (hcv _) (hrv _) v hv
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hrv _ v hv

/-- Ausiliario di `inv_step_parent`: un grant in `P ++ [a]` o stava in `P` o è `a`. -/
theorem inv_step_parent_aux2 {P : List PCEvent} {a : PCEvent} {v : Value}
    (h : PCEvent.rsM v ∈ P ++ [a] ∨ PCEvent.rsS v ∈ P ++ [a]) :
    (PCEvent.rsM v ∈ P ∨ PCEvent.rsS v ∈ P) ∨ (a = PCEvent.rsM v ∨ a = PCEvent.rsS v) := by
  rcases h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (List.mem_singleton.1 h).symm)
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr (List.mem_singleton.1 h).symm)

/-- Ausiliario di `inv_step_parent` (versione MESI di `inv_step_parent_aux1`: le righe `M` ed `E`
sono trattate insieme e i grant comprendono `rsE`): l'invariante nello stato dopo un passo del
parent segue dalle condizioni all'indice `k` (le altre cache e le altre righe non cambiano). -/
theorem inv_step_parent_aux3 {x : MESIState n} {s : SeqState n} {k : Fin n} {p' : ParentState n}
    (hI : flushInv x s)
    (hsync : synced
      { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k, queue_pc := p'.queue_pci k } x.caches,
               parent := p' })
    (hval : p'.value = s.memory)
    (hother : ∀ k', ¬ k' = k → p'.shared_state k' = x.parent.shared_state k')
    (hM : (p'.shared_state k = Bstate.M ∨ p'.shared_state k = Bstate.E) →
      ((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
        ∨ (∃ v, PCEvent.rsM v ∈ p'.queue_pci k) ∨ (∃ v, PCEvent.rsE v ∈ p'.queue_pci k)
        ∨ (∃ v, CPEvent.rsIμ v ∈ p'.queue_cip k))
    (hS : p'.shared_state k = Bstate.S →
      (x.caches k).state = Bstate.S ∨ (∃ v, PCEvent.rsS v ∈ p'.queue_pci k)
        ∨ CPEvent.rsIσ ∈ p'.queue_cip k)
    (hgv : ∀ v, (PCEvent.rsM v ∈ p'.queue_pci k ∨ PCEvent.rsS v ∈ p'.queue_pci k
        ∨ PCEvent.rsE v ∈ p'.queue_pci k) → v = s.memory)
    (hrv : ∀ v, CPEvent.rsIμ v ∈ p'.queue_cip k → v = s.memory) :
    flushInv
      { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k, queue_pc := p'.queue_pci k } x.caches,
               parent := p' } s := by
  obtain ⟨_, hM0, hS0, _, hcv0, hgv0, hrv0⟩ := hI
  refine ⟨hsync, ?_, ?_, hval, ?_, ?_, ?_⟩
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      unfold tokenM
      simp only [update_Fin_gss]
      exact hM hk'
    · have ht := hM0 k' (by rw [← hother k' hk]; exact hk')
      unfold tokenM at ht ⊢
      simp only [update_Fin_gso2 _ _ _ _ hk]
      exact ht
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      unfold tokenS
      simp only [update_Fin_gss]
      exact hS hk'
    · have ht := hS0 k' (by rw [← hother k' hk]; exact hk')
      unfold tokenS at ht ⊢
      simp only [update_Fin_gso2 _ _ _ _ hk]
      exact ht
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hcv0 _ hk'
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcv0 k' hk'
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hgv v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hgv0 k' v hmem
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hrv v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hrv0 k' v hmem

/-- Ausiliario di `inv_step_parent`: un grant (`rsM`, `rsS` o `rsE`) in `P ++ [a]` o stava in `P`
o è `a`. -/
theorem inv_step_parent_aux4 {P : List PCEvent} {a : PCEvent} {v : Value}
    (h : PCEvent.rsM v ∈ P ++ [a] ∨ PCEvent.rsS v ∈ P ++ [a] ∨ PCEvent.rsE v ∈ P ++ [a]) :
    (PCEvent.rsM v ∈ P ∨ PCEvent.rsS v ∈ P ∨ PCEvent.rsE v ∈ P)
      ∨ (a = PCEvent.rsM v ∨ a = PCEvent.rsS v ∨ a = PCEvent.rsE v) := by
  rcases h with h | h | h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (List.mem_singleton.1 h).symm)
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl (List.mem_singleton.1 h).symm))
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h).symm))

theorem inv_step_parent {x : MESIState n} {s : SeqState n} {k : Fin n}
    {e : ParentUpdQueueInternalEvent n} {p' : ParentState n}
    (hI : flushInv x s) (h : parent_mesi_step x.parent (.upd_queue e k) p') :
    flushInv { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                                queue_pc := p'.queue_pci k } x.caches,
                      parent := p' } s := by
  have hsync' := synced_step hI.synced (mesi_step_internal.parent_upd_queue x p' e k h)
  have hother : ∀ k', ¬ k' = k → p'.shared_state k' = x.parent.shared_state k' :=
    fun k' hk => (parent_step_local h k' hk).2.2
  have hcp := (hI.synced k).1
  have hpc := (hI.synced k).2
  have hval := hI.value
  have hM := hI.rowM
  have hS := hI.rowS
  have hgv := hI.grantVal
  have hrv := hI.releaseVal
  cases h
  case downgrade_from_M_rq1 v j hj =>
    refine inv_step_parent_aux3 hI hsync' ?_ hother ?_ ?_ ?_ ?_
    · have hmem : CPEvent.rsIμ v ∈ (x.caches k).queue_cp := by
        rw [← hcp]; exact List.mem_of_getElem? hj
      exact hrv k v hmem
    · intro hc; simp at hc
    · intro hc; simp at hc
    · intro v' hmem
      apply hgv k v'
      rw [← hpc]; exact hmem
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hrv k v' hmem'
  case downgrade_from_M_rq2 =>
    refine inv_step_parent_aux3 hI hsync' hval hother ?_ ?_ ?_ ?_
    · intro hc; simp at hc
    · intro hc; simp at hc
    · intro v' hmem
      apply hgv k v'
      rw [← hpc]; exact hmem
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hrv k v' hmem'
  case upgrade_to_M_data_avilable_rq1 =>
    refine inv_step_parent_aux3 hI hsync' hval hother ?_ ?_ ?_ ?_
    · intro _
      refine Or.inr (Or.inl ⟨x.parent.value, ?_⟩)
      simp only [update_Fin_gss]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · intro hc; simp at hc
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases inv_step_parent_aux4 hmem with h | h | h | h
      · rw [hpc] at h; exact hgv k v' h
      · cases h; exact hval
      · cases h
      · cases h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hrv k v' hmem'
  case upgrade_to_M_data_avilable_rq2 =>
    refine inv_step_parent_aux3 hI hsync' hval hother ?_ ?_ ?_ ?_
    · intro hc; simp at hc
    · intro _
      refine Or.inr (Or.inl ⟨x.parent.value, ?_⟩)
      simp only [update_Fin_gss]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases inv_step_parent_aux4 hmem with h | h | h | h
      · rw [hpc] at h; exact hgv k v' h
      · cases h
      · cases h; exact hval
      · cases h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hrv k v' hmem'
  case upgrade_to_E =>
    refine inv_step_parent_aux3 hI hsync' hval hother ?_ ?_ ?_ ?_
    · intro _
      refine Or.inr (Or.inr (Or.inl ⟨x.parent.value, ?_⟩))
      simp only [update_Fin_gss]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · intro hc; simp at hc
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases inv_step_parent_aux4 hmem with h | h | h | h
      · rw [hpc] at h; exact hgv k v' h
      · cases h
      · cases h
      · cases h; exact hval
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hrv k v' hmem'
  all_goals
    refine inv_step_parent_aux3 hI hsync' hval hother ?_ ?_ ?_ ?_
    · intro hc
      have ht := hM k hc
      unfold tokenM at ht
      simp only [update_Fin_gss]
      rcases ht with h | ⟨v, h⟩ | ⟨v, h⟩ | ⟨v, h⟩
      · exact Or.inl h
      · rw [← hpc] at h
        exact Or.inr (Or.inl ⟨v, List.mem_append_left _ h⟩)
      · rw [← hpc] at h
        exact Or.inr (Or.inr (Or.inl ⟨v, List.mem_append_left _ h⟩))
      · rw [← hcp] at h
        exact Or.inr (Or.inr (Or.inr ⟨v, h⟩))
    · intro hc
      have ht := hS k hc
      unfold tokenS at ht
      simp only [update_Fin_gss]
      rcases ht with h | ⟨v, h⟩ | h
      · exact Or.inl h
      · rw [← hpc] at h
        exact Or.inr (Or.inl ⟨v, List.mem_append_left _ h⟩)
      · rw [← hcp] at h
        exact Or.inr (Or.inr h)
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases inv_step_parent_aux4 hmem with h | h | h | h
      · rw [hpc] at h; exact hgv k v' h
      · cases h
      · cases h
      · cases h
    · intro v' hmem
      apply hrv k v'
      rw [← hcp]; exact hmem

theorem inv_step {x y : MESIState n} {s : SeqState n} {e : MESIInternalEvent n}
    (hI : flushInv x s) (h : mesi_step_internal x e y) : flushInv y s := by
  cases h with
  | cache c' k e' hc => exact inv_step_cache hI hc
  | parent_upd_queue p' e' k hp => exact inv_step_parent hI hp

theorem inv_trans {x y : MESIState n} {s : SeqState n}
    (hI : flushInv x s) (h : trans_refl (mesi_rule n) x y) : flushInv y s := by
  revert hI
  induction h with
  | refl => exact id
  | step hab _ ih =>
    intro hI
    obtain ⟨e, he⟩ := hab
    exact ih (inv_step hI he)

/-! ### Fase 1: svuotare cache non in `I`, grant e rilasci -/

/-- Sostituire la cache `k` (non in `I`) con una cache in `I`, stessa `queue_pc` e un rilascio in
più in `queue_cp` fa scendere `μ1` (il parent non conta). -/
theorem phase1_step_release_aux1 {x : MESIState n} {k : Fin n} (hk : (x.caches k).state ≠ Bstate.I)
    {c' : CacheState} (hst : c'.state = Bstate.I) (hpc : c'.queue_pc = (x.caches k).queue_pc)
    (hcp : c'.queue_cp.countP isRelease = (x.caches k).queue_cp.countP isRelease + 1)
    (p' : ParentState n) :
    μ1 { caches := update_Fin k c' x.caches, parent := p' } < μ1 x := by
  have hlt : m1 { caches := update_Fin k c' x.caches, parent := p' } k < m1 x k := by
    unfold m1
    simp only [update_Fin_gss]
    rw [hpc, hcp, if_pos hst, if_neg hk]
    omega
  unfold μ1
  apply sum_lt_of_pointwise (k₀ := k) _ hlt
  intro k'
  by_cases hk' : k' = k
  · subst hk'
    exact le_of_lt hlt
  · have heq : m1 { caches := update_Fin k c' x.caches, parent := p' } k' = m1 x k' := by
      unfold m1
      simp only [update_Fin_gso2 _ _ _ _ hk']
    exact le_of_eq heq

/-- Una cache non in `I` rilascia spontaneamente. -/
theorem phase1_step_release {x : MESIState n} {s : SeqState n} {k : Fin n} (_hI : flushInv x s)
    (hk : (x.caches k).state ≠ Bstate.I) : ∃ y, mesi_rule n x y ∧ μ1 y < μ1 x := by
  cases hst : (x.caches k).state with
  | I => exact absurd hst hk
  | M =>
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.rq_data_not_available _ hst)), ?_⟩
    refine phase1_step_release_aux1 hk ?_ ?_ ?_ _
    · rfl
    · rfl
    · simp [List.countP_append, isRelease]
  | S =>
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.rq_data_not_available1 _ hst)), ?_⟩
    refine phase1_step_release_aux1 hk ?_ ?_ ?_ _
    · rfl
    · rfl
    · simp [List.countP_append, isRelease]
  | E =>
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.rq_data_not_availableE _ hst)), ?_⟩
    refine phase1_step_release_aux1 hk ?_ ?_ ?_ _
    · rfl
    · rfl
    · simp [List.countP_append, isRelease]

/-- Un passo del parent all'indice `k` cambia `m1` solo in `k`: se lì cala, cala `μ1`. -/
theorem phase1_step_proc_aux1 {x : MESIState n} {c' : CacheState} {p' : ParentState n} {k : Fin n}
    (hlt : m1 { x with caches := update_Fin k c' x.caches, parent := p' } k < m1 x k) :
    μ1 { x with caches := update_Fin k c' x.caches, parent := p' } < μ1 x := by
  unfold μ1
  refine sum_lt_of_pointwise (fun k' => ?_) k hlt
  by_cases hk : k' = k
  · subst hk
    exact hlt.le
  · apply le_of_eq
    simp only [m1, update_Fin_gso2 _ _ _ _ hk]

/-- Il parent prende un rilascio in volo. -/
theorem phase1_step_proc {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} {m : CPEvent}
    (hI : flushInv x s) (hj : (x.caches k).queue_cp[j]? = some m) (hm : isRelease m = true) :
    ∃ y, mesi_rule n x y ∧ μ1 y < μ1 x := by
  have hs1 := (hI.synced k).1
  have hs2 := (hI.synced k).2
  have hj' : (x.parent.queue_cip k)[j]? = some m := by rw [hs1]; exact hj
  have hcount : ((x.caches k).queue_cp.eraseIdx j).countP isRelease + 1
      = (x.caches k).queue_cp.countP isRelease := countP_eraseIdx_pos hj hm
  cases m with
  | rsIμ v =>
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.parent_upd_queue x _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x.parent v k j hj')), ?_⟩
    apply phase1_step_proc_aux1
    simp only [m1, update_Fin_gss, hs1, hs2]
    omega
  | rsIσ =>
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.parent_upd_queue x _ _ k
      (parent_mesi_step.downgrade_from_M_rq2 x.parent k j hj')), ?_⟩
    apply phase1_step_proc_aux1
    simp only [m1, update_Fin_gss, hs1, hs2]
    omega
  | rqS => simp [isRelease] at hm
  | rqM => simp [isRelease] at hm

/-- Un passo di cache che fa calare `m1` all'indice `k` fa calare `μ1`: gli altri indici non cambiano. -/
theorem phase1_step_take_aux1 {x : MESIState n} {k : Fin n} {c' : CacheState}
    (hlt : m1 { x with caches := update_Fin k c' x.caches,
                       parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                       parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } k < m1 x k) :
    μ1 { x with caches := update_Fin k c' x.caches,
                parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } < μ1 x := by
  unfold μ1
  refine sum_lt_of_pointwise (fun k' => ?_) k hlt
  by_cases hk : k' = k
  · subst hk
    exact le_of_lt hlt
  · unfold m1
    simp only [update_Fin_gso2 _ _ _ _ hk]
    exact le_refl _

/-- Con tutte le cache in `I`, la cache `k` prende un grant in volo. -/
theorem phase1_step_take {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} {m : PCEvent}
    (_hI : flushInv x s) (hall : ∀ k, (x.caches k).state = Bstate.I)
    (hj : (x.caches k).queue_pc[j]? = some m) (hm : isGrant m = true) :
    ∃ y, mesi_rule n x y ∧ μ1 y < μ1 x := by
  cases m with
  | rqIμ => simp [isGrant] at hm
  | rqIσ => simp [isGrant] at hm
  | rsM v =>
    have hstep := cache_mesi_step_internal.upgrade_from_I_rs (x.caches k) v j hj (hall k)
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache x _ k _ hstep), phase1_step_take_aux1 ?_⟩
    have hc := countP_eraseIdx_pos (p := isGrant) hj rfl
    unfold m1
    simp only [update_Fin_gss]
    rw [if_pos (hall k), if_neg (fun h => Bstate.noConfusion h)]
    omega
  | rsS v =>
    have hstep := cache_mesi_step_internal.upgrade_from_I_rsS (x.caches k) v j hj (hall k)
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache x _ k _ hstep), phase1_step_take_aux1 ?_⟩
    have hc := countP_eraseIdx_pos (p := isGrant) hj rfl
    unfold m1
    simp only [update_Fin_gss]
    rw [if_pos (hall k), if_neg (fun h => Bstate.noConfusion h)]
    omega
  | rsE v =>
    have hstep := cache_mesi_step_internal.upgrade_from_I_rsE (x.caches k) v j hj (hall k)
    refine ⟨_, mesi_rule_of_step (mesi_step_internal.cache x _ k _ hstep), phase1_step_take_aux1 ?_⟩
    have hc := countP_eraseIdx_pos (p := isGrant) hj rfl
    unfold m1
    simp only [update_Fin_gss]
    rw [if_pos (hall k), if_neg (fun h => Bstate.noConfusion h)]
    omega

theorem phase1_step {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (hpos : 0 < μ1 x) :
    ∃ y, mesi_rule n x y ∧ μ1 y < μ1 x := by
  by_cases hall : ∀ k, (x.caches k).state = Bstate.I
  · unfold μ1 at hpos
    obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
    have hk' : 0 < m1 x k := hk
    unfold m1 at hk'
    rw [if_pos (hall k)] at hk'
    have hcases : 0 < (x.caches k).queue_pc.countP isGrant
        ∨ 0 < (x.caches k).queue_cp.countP isRelease := by omega
    rcases hcases with hg | hr
    · obtain ⟨m, hm, hmg⟩ := List.countP_pos_iff.mp hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      exact phase1_step_take hI hall hj hmg
    · obtain ⟨m, hm, hmr⟩ := List.countP_pos_iff.mp hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      exact phase1_step_proc hI hj hmr
  · obtain ⟨k, hk⟩ := not_forall.mp hall
    exact phase1_step_release hI hk

theorem phase1 {x : MESIState n} {s : SeqState n} (hI : flushInv x s) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 := by
  suffices H : ∀ m, ∀ x : MESIState n, flushInv x s → μ1 x ≤ m →
      ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 from H _ x hI le_rfl
  intro m
  induction m with
  | zero =>
    intro x hI hm
    exact ⟨x, trans_refl.refl, hI, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hI hm
    by_cases h0 : μ1 x = 0
    · exact ⟨x, trans_refl.refl, hI, h0⟩
    · obtain ⟨y, hxy, hlt⟩ := phase1_step hI (Nat.pos_of_ne_zero h0)
      obtain ⟨e, he⟩ := hxy
      obtain ⟨z, hyz, hIz, hz⟩ := ih y (inv_step hI he) (by omega)
      exact ⟨z, trans_refl.step (mesi_rule_of_step he) hyz, hIz, hz⟩

/-! ### Che cosa dice `μ1 x = 0` -/

theorem quiet_caches {x : MESIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).state = Bstate.I := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  by_cases hs : (x.caches k).state = Bstate.I
  · exact hs
  · rw [if_neg hs] at hk
    omega

theorem quiet_grants {x : MESIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).queue_pc.countP isGrant = 0 := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  omega

theorem quiet_releases {x : MESIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).queue_cp.countP isRelease = 0 := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  omega

theorem quiet_of {x : MESIState n} (hc : ∀ k, (x.caches k).state = Bstate.I)
    (hg : ∀ k, (x.caches k).queue_pc.countP isGrant = 0)
    (hr : ∀ k, (x.caches k).queue_cp.countP isRelease = 0) : μ1 x = 0 := by
  show Finset.univ.sum (fun k => m1 x k) = 0
  apply sum_eq_zero_iff_pointwise.mpr
  intro k
  show m1 x k = 0
  unfold m1
  simp [hg k, hr k, hc k]

/-- A `μ1 x = 0`, per i token, tutte le righe della directory sono a `I`. -/
theorem quiet_rows {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0) (k : Fin n) :
    x.parent.shared_state k = Bstate.I := by
  have hc := quiet_caches h0 k
  have hg := quiet_grants h0 k
  have hr := quiet_releases h0 k
  rw [List.countP_eq_zero] at hg hr
  cases hrow : x.parent.shared_state k with
  | I => rfl
  | M =>
    have ht := hI.rowM k (Or.inl hrow)
    unfold tokenM at ht
    rcases ht with (h | h) | ⟨v, h⟩ | ⟨v, h⟩ | ⟨v, h⟩
    · rw [hc] at h; cases h
    · rw [hc] at h; cases h
    · exact (hg _ h rfl).elim
    · exact (hg _ h rfl).elim
    · exact (hr _ h rfl).elim
  | E =>
    have ht := hI.rowM k (Or.inr hrow)
    unfold tokenM at ht
    rcases ht with (h | h) | ⟨v, h⟩ | ⟨v, h⟩ | ⟨v, h⟩
    · rw [hc] at h; cases h
    · rw [hc] at h; cases h
    · exact (hg _ h rfl).elim
    · exact (hg _ h rfl).elim
    · exact (hr _ h rfl).elim
  | S =>
    have ht := hI.rowS k hrow
    unfold tokenS at ht
    rcases ht with h | ⟨v, h⟩ | h
    · rw [hc] at h; cases h
    · exact (hg _ h rfl).elim
    · exact (hr _ h rfl).elim

/-! ### Fase 2: consumare le richieste pendenti -/

/-- Una `rqM` pendente di `k` si consuma in quattro passi: grant di `M`, presa del grant, rilascio
spontaneo, presa del rilascio. -/
theorem phase2_step_M {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} (hI : flushInv x s)
    (h0 : μ1 x = 0) (hj : (x.caches k).queue_cp[j]? = some CPEvent.rqM) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x := by
  -- Fatti da `h0` e dall'invariante.
  have hs : synced x := hI.synced
  have hall := quiet_caches h0
  have hg := quiet_grants h0
  have hr := quiet_releases h0
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hI h0
  have hj1 : (x.parent.queue_cip k)[j]? = some CPEvent.rqM := by
    rw [(hs k).1]; exact hj
  -- Passo 1: il parent concede `M` a `k`.
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, mesi_rule n x x1
        ∧ synced x1
        ∧ (x1.caches k).state = Bstate.I
        ∧ (x1.caches k).queue_pc = (x.caches k).queue_pc ++ [PCEvent.rsM x.parent.value]
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp.eraseIdx j
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    have hstep := mesi_step_internal.parent_upd_queue x _ _ k
      (parent_mesi_step.upgrade_to_M_data_avilable_rq1 x.parent k j hj1 hrows)
    refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact hall k
    · simp only [update_Fin_gss]; rw [(hs k).2]
    · simp only [update_Fin_gss]; rw [(hs k).1]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: la cache `k` prende il grant.
  obtain ⟨x2, step2, h2s, h2state, h2pc, h2cp, h2val, h2oth⟩ :
      ∃ x2, mesi_rule n x1 x2
        ∧ synced x2
        ∧ (x2.caches k).state = Bstate.M
        ∧ (x2.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp.eraseIdx j
        ∧ (x2.caches k).value = x.parent.value
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    have hg3 : (x1.caches k).queue_pc[(x.caches k).queue_pc.length]?
        = some (PCEvent.rsM x.parent.value) := by
      rw [h1pc]; exact List.getElem?_concat_length
    have hstep := mesi_step_internal.cache x1 _ k _
      (cache_mesi_step_internal.upgrade_from_I_rs (x1.caches k) x.parent.value
        (x.caches k).queue_pc.length hg3 h1state)
    refine ⟨_, mesi_rule_of_step hstep, synced_step h1s hstep, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; rw [h1pc]; exact eraseIdx_concat _ _
    · simp only [update_Fin_gss]; exact h1cp
    · simp only [update_Fin_gss]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  -- Passo 3: la cache `k` rilascia spontaneamente.
  obtain ⟨x3, step3, h3s, h3state, h3pc, h3cp, h3oth⟩ :
      ∃ x3, mesi_rule n x2 x3
        ∧ synced x3
        ∧ (x3.caches k).state = Bstate.I
        ∧ (x3.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x3.caches k).queue_cp
            = (x.caches k).queue_cp.eraseIdx j ++ [CPEvent.rsIμ x.parent.value]
        ∧ (∀ k', k' ≠ k → x3.caches k' = x.caches k') := by
    have hstep := mesi_step_internal.cache x2 _ k _
      (cache_mesi_step_internal.rq_data_not_available (x2.caches k) h2state)
    refine ⟨_, mesi_rule_of_step hstep, synced_step h2s hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; exact h2pc
    · simp only [update_Fin_gss]; rw [h2cp, h2val]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h2oth k' hk
  -- Passo 4: il parent prende il rilascio.
  obtain ⟨x4, step4, h4state, h4pc, h4cp, h4oth⟩ :
      ∃ x4, mesi_rule n x3 x4
        ∧ (x4.caches k).state = Bstate.I
        ∧ (x4.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x4.caches k).queue_cp = (x.caches k).queue_cp.eraseIdx j
        ∧ (∀ k', k' ≠ k → x4.caches k' = x.caches k') := by
    have hg6 : (x3.parent.queue_cip k)[((x.caches k).queue_cp.eraseIdx j).length]?
        = some (CPEvent.rsIμ x.parent.value) := by
      rw [(h3s k).1, h3cp]; exact List.getElem?_concat_length
    have hstep := mesi_step_internal.parent_upd_queue x3 _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x3.parent x.parent.value k _ hg6)
    refine ⟨_, mesi_rule_of_step hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h3state
    · simp only [update_Fin_gss]; rw [(h3s k).2, h3pc]
    · simp only [update_Fin_gss]; rw [(h3s k).1, h3cp]; exact eraseIdx_concat _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h3oth k' hk
  -- Conclusione.
  refine ⟨x4, trans_refl.step step1 (trans_refl.step step2 (trans_refl.step step3
    (trans_refl.step step4 trans_refl.refl))), ?_, ?_⟩
  · -- `μ1 x4 = 0`
    have hc : ∀ k', (x4.caches k').state = Bstate.I := by
      intro k'
      by_cases hk : k' = k
      · rw [hk]; exact h4state
      · rw [h4oth k' hk]; exact hall k'
    have hg' : ∀ k', (x4.caches k').queue_pc.countP isGrant = 0 := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, h4pc]; exact hg k
      · rw [h4oth k' hk]; exact hg k'
    have hr' : ∀ k', (x4.caches k').queue_cp.countP isRelease = 0 := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, h4cp, countP_eraseIdx_neg (p := isRelease) hj rfl]; exact hr k
      · rw [h4oth k' hk]; exact hr k'
    exact quiet_of hc hg' hr'
  · -- `μ2 x4 < μ2 x`
    have hpos := countP_eraseIdx_pos (p := isRequest) hj rfl
    have hle : ∀ k', (x4.caches k').queue_cp.countP isRequest
        ≤ (x.caches k').queue_cp.countP isRequest := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, h4cp]; omega
      · rw [h4oth k' hk]
    have hlt : (x4.caches k).queue_cp.countP isRequest < (x.caches k).queue_cp.countP isRequest := by
      rw [h4cp]; omega
    unfold μ2
    exact sum_lt_of_pointwise hle k hlt

/-- Come `phase2_step_M` per una `rqS` pendente, con `S`. -/
theorem phase2_step_S {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} (hI : flushInv x s)
    (h0 : μ1 x = 0) (hj : (x.caches k).queue_cp[j]? = some CPEvent.rqS) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x := by
  obtain ⟨hs1, hs2⟩ := hI.synced k
  have hj' : (x.parent.queue_cip k)[j]? = some CPEvent.rqS := by rw [hs1]; exact hj
  have g2 : x.parent.shared_state k = Bstate.I := quiet_rows hI h0 k
  have g3 : ∀ i, ¬ x.parent.shared_state i = Bstate.M := fun i h => by
    rw [quiet_rows hI h0 i] at h; exact Bstate.noConfusion h
  have g3E : ∀ i, ¬ x.parent.shared_state i = Bstate.E := fun i h => by
    rw [quiet_rows hI h0 i] at h; exact Bstate.noConfusion h
  have hcnt := countP_eraseIdx_pos (p := isRequest) hj (rfl : isRequest CPEvent.rqS = true)
  refine ⟨_,
    trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
        (parent_mesi_step.upgrade_to_M_data_avilable_rq2 _ k j hj' g2 g3 g3E)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
        (cache_mesi_step_internal.upgrade_from_I_rsS _ x.parent.value (x.parent.queue_pci k).length
          ?g4 ?g5)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
        (cache_mesi_step_internal.rq_data_not_available1 _ ?g6)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
        (parent_mesi_step.downgrade_from_M_rq2 _ k ((x.parent.queue_cip k).eraseIdx j).length ?g7)))
    trans_refl.refl))), ?h1, ?h2⟩
  case g4 =>
    simp only [update_Fin_gss]
    exact List.getElem?_concat_length
  case g5 =>
    simp only [update_Fin_gss]
    exact quiet_caches h0 k
  case g6 =>
    simp only [update_Fin_gss]
  case g7 =>
    simp only [update_Fin_gss]
    exact List.getElem?_concat_length
  case h1 =>
    apply quiet_of
    · intro k'
      by_cases hk : k' = k
      · rw [hk]
        simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
        exact quiet_caches h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk]
        simp only [update_Fin_gss, eraseIdx_concat]
        rw [hs2]
        exact quiet_grants h0 k
      · simp only [update_Fin_gso2 _ _ _ _ hk]
        exact quiet_grants h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk]
        simp only [update_Fin_gss, eraseIdx_concat]
        rw [hs1, countP_eraseIdx_neg (p := isRelease) hj rfl]
        exact quiet_releases h0 k
      · simp only [update_Fin_gso2 _ _ _ _ hk]
        exact quiet_releases h0 k'
  case h2 =>
    unfold μ2
    refine sum_lt_of_pointwise ?_ k ?_
    · intro k'
      by_cases hk : k' = k
      · rw [hk]
        simp only [update_Fin_gss, eraseIdx_concat]
        rw [hs1]
        omega
      · simp only [update_Fin_gso2 _ _ _ _ hk]
        exact le_refl _
    · simp only [update_Fin_gss, eraseIdx_concat]
      rw [hs1]
      omega

theorem phase2_step {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0)
    (hpos : 0 < μ2 x) : ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x := by
  unfold μ2 at hpos
  obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
  obtain ⟨m, hm, hmr⟩ := List.countP_pos_iff.mp hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  cases m with
  | rsIμ v => simp [isRequest] at hmr
  | rsIσ => simp [isRequest] at hmr
  | rqS => exact phase2_step_S hI h0 hj
  | rqM => exact phase2_step_M hI h0 hj

/-- Transitività di `trans_refl` (helper per `phase2`, `phase3`, `mesi_relation_flush`). -/
theorem phase2_aux1 {A : Type} {r : A → A → Prop} {a b c : A} (hab : trans_refl r a b)
    (hbc : trans_refl r b c) : trans_refl r a c := by
  revert hbc
  induction hab with
  | refl => exact id
  | step h _ ih =>
    intro hbc
    exact trans_refl.step h (ih hbc)

theorem phase2 {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 ∧ μ2 y = 0 := by
  suffices H : ∀ m, ∀ x : MESIState n, flushInv x s → μ1 x = 0 → μ2 x ≤ m →
      ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 ∧ μ2 y = 0 from
    H _ x hI h0 le_rfl
  intro m
  induction m with
  | zero =>
    intro x hI h0 hm
    exact ⟨x, trans_refl.refl, hI, h0, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hI h0 hm
    by_cases h2 : μ2 x = 0
    · exact ⟨x, trans_refl.refl, hI, h0, h2⟩
    · obtain ⟨y, hxy, h0y, hlt⟩ := phase2_step hI h0 (Nat.pos_of_ne_zero h2)
      obtain ⟨z, hyz, hIz, h0z, h2z⟩ := ih y (inv_trans hI hxy) h0y (by omega)
      exact ⟨z, phase2_aux1 hxy hyz, hIz, h0z, h2z⟩

/-! ### Fase 3: consumare gli invalidate stantii -/

/-- Un `rqIμ` stantio per `k` si consuma in cinque passi: `rqM`, grant di `M`, presa del grant,
`downgrade_from_M_rs` (che consuma l'invalidate e rilascia), presa del rilascio. -/
theorem phase3_step_M {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} (hI : flushInv x s)
    (h0 : μ1 x = 0) (h2 : μ2 x = 0) (hj : (x.caches k).queue_pc[j]? = some PCEvent.rqIμ) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  have hc0 : (x.caches k).state = Bstate.I := quiet_caches h0 k
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hI h0
  have h2' : ∀ k', (x.caches k').queue_cp.countP isRequest = 0 := sum_eq_zero_iff_pointwise.mp h2
  have hinv := countP_eraseIdx_pos (p := isInval) hj rfl
  refine ⟨_, trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache x _ k _
      (cache_mesi_step_internal.upgrade_from_I_rq (x.caches k) hc0)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
      (parent_mesi_step.upgrade_to_M_data_avilable_rq1 _ k (x.caches k).queue_cp.length ?g1 ?g2)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.upgrade_from_I_rs _ x.parent.value (x.caches k).queue_pc.length ?g3 ?g4)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.downgrade_from_M_rs _ j ?g5 ?g6)))
    (trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 _ x.parent.value k (x.caches k).queue_cp.length ?g7)))
    trans_refl.refl)))), ?m1, ?m2, ?m3⟩
  case g1 => simp only [update_Fin_gss, List.getElem?_concat_length]
  case g2 => intro i; exact hrows i
  case g3 => simp only [update_Fin_gss, List.getElem?_concat_length]
  case g4 => simp only [update_Fin_gss, hc0]
  case g5 => simp only [update_Fin_gss, eraseIdx_concat, hj]
  case g6 => simp only [update_Fin_gss]
  case g7 => simp only [update_Fin_gss, eraseIdx_concat, List.getElem?_concat_length]
  case m1 =>
    refine quiet_of (fun k' => ?_) (fun k' => ?_) (fun k' => ?_)
    · by_cases hk : k' = k
      · rw [hk]; simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]; exact quiet_caches h0 k'
    · by_cases hk : k' = k
      · rw [hk]; simp only [update_Fin_gss, eraseIdx_concat]
        rw [countP_eraseIdx_neg hj rfl]; exact quiet_grants h0 k
      · simp only [update_Fin_gso2 _ _ _ _ hk]; exact quiet_grants h0 k'
    · by_cases hk : k' = k
      · rw [hk]; simp only [update_Fin_gss, eraseIdx_concat]; exact quiet_releases h0 k
      · simp only [update_Fin_gso2 _ _ _ _ hk]; exact quiet_releases h0 k'
  case m2 =>
    unfold μ2
    refine sum_eq_zero_iff_pointwise.mpr (fun k' => ?_)
    by_cases hk : k' = k
    · rw [hk]; simp only [update_Fin_gss, eraseIdx_concat]; exact h2' k
    · simp only [update_Fin_gso2 _ _ _ _ hk]; exact h2' k'
  case m3 =>
    unfold μ3
    refine sum_lt_of_pointwise (fun k' => ?_) k ?_
    · by_cases hk : k' = k
      · rw [hk]; simp only [update_Fin_gss, eraseIdx_concat]; omega
      · simp only [update_Fin_gso2 _ _ _ _ hk]; exact le_refl _
    · simp only [update_Fin_gss, eraseIdx_concat]; omega

/-- I cinque passi di `phase3_step_S`: lo stato di arrivo `y` ha la cache `k` con il valore del
parent e senza la posizione `j` della sua `queue_pc`, e le altre cache inalterate. -/
theorem phase3_step_S_aux1 {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat}
    (hI : flushInv x s) (h0 : μ1 x = 0) (hj : (x.caches k).queue_pc[j]? = some PCEvent.rqIσ) :
    ∃ y, trans_refl (mesi_rule n) x y ∧
      y.caches k = { x.caches k with
          value := x.parent.value, queue_pc := (x.caches k).queue_pc.eraseIdx j } ∧
      ∀ k', k' ≠ k → y.caches k' = x.caches k' := by
  have hI0 : (x.caches k).state = Bstate.I := quiet_caches h0 k
  have hrow : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hI h0
  refine ⟨?_, ?chain, ?eqk, ?eqo⟩
  case chain =>
    -- 1. la cache `k` accoda `rqS`
    refine trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache x _ k _
      (cache_mesi_step_internal.upgrade_from_I_rq1 _ hI0))) ?_
    -- 2. il parent concede `S`
    refine trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
      (parent_mesi_step.upgrade_to_M_data_avilable_rq2 _ k (x.caches k).queue_cp.length
        ?g21 ?g22 ?g23 ?g24))) ?_
    case g21 => simp only [update_Fin_gss, List.getElem?_concat_length]
    case g22 => exact hrow k
    case g23 =>
      intro i h
      have h' : x.parent.shared_state i = Bstate.M := h
      rw [hrow i] at h'
      cases h'
    case g24 =>
      intro i h
      have h' : x.parent.shared_state i = Bstate.E := h
      rw [hrow i] at h'
      cases h'
    -- 3. la cache `k` prende il grant di `S`
    refine trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.upgrade_from_I_rsS _ x.parent.value (x.caches k).queue_pc.length
        ?g31 ?g32))) ?_
    case g31 => simp only [update_Fin_gss, eraseIdx_concat, List.getElem?_concat_length]
    case g32 => simp only [update_Fin_gss, hI0]
    -- 4. la cache `k` consuma il `rqIσ` stantio e rilascia
    refine trans_refl.step (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.downgrade_from_M_rs1 _ j ?g41 ?g42))) ?_
    case g41 => simp only [update_Fin_gss, eraseIdx_concat, hj]
    case g42 => simp only [update_Fin_gss]
    -- 5. il parent prende il rilascio `rsIσ`
    refine trans_refl.step (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
      (parent_mesi_step.downgrade_from_M_rq2 _ k (x.caches k).queue_cp.length ?g51))) ?_
    case g51 => simp only [update_Fin_gss, eraseIdx_concat, List.getElem?_concat_length]
    exact trans_refl.refl
  case eqk => simp only [update_Fin_gss, eraseIdx_concat, hI0]
  case eqo =>
    intro k' hk
    simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Come `phase3_step_M` per un `rqIσ` stantio, con `S` (`rqS`, grant di `S`, presa,
`downgrade_from_M_rs1`, presa del rilascio). -/
theorem phase3_step_S {x : MESIState n} {s : SeqState n} {k : Fin n} {j : Nat} (hI : flushInv x s)
    (h0 : μ1 x = 0) (h2 : μ2 x = 0) (hj : (x.caches k).queue_pc[j]? = some PCEvent.rqIσ) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  obtain ⟨y, hxy, hyk, hyo⟩ := phase3_step_S_aux1 hI h0 hj
  have hinv : ((x.caches k).queue_pc.eraseIdx j).countP isInval + 1
      = (x.caches k).queue_pc.countP isInval :=
    countP_eraseIdx_pos hj (rfl : isInval PCEvent.rqIσ = true)
  refine ⟨y, hxy, ?_, ?_, ?_⟩
  · apply quiet_of
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]; exact quiet_caches h0 k
      · rw [hyo k' hk]; exact quiet_caches h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]
        show ((x.caches k).queue_pc.eraseIdx j).countP isGrant = 0
        rw [countP_eraseIdx_neg hj (rfl : isGrant PCEvent.rqIσ = false)]
        exact quiet_grants h0 k
      · rw [hyo k' hk]; exact quiet_grants h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]; exact quiet_releases h0 k
      · rw [hyo k' hk]; exact quiet_releases h0 k'
  · have h2' := sum_eq_zero_iff_pointwise.1 h2
    unfold μ2
    refine sum_eq_zero_iff_pointwise.2 fun k' => ?_
    show (y.caches k').queue_cp.countP isRequest = 0
    by_cases hk : k' = k
    · rw [hk, hyk]; exact h2' k
    · rw [hyo k' hk]; exact h2' k'
  · unfold μ3
    refine sum_lt_of_pointwise (fun k' => ?_) k ?_
    · show (y.caches k').queue_pc.countP isInval ≤ (x.caches k').queue_pc.countP isInval
      by_cases hk : k' = k
      · rw [hk, hyk]
        show ((x.caches k).queue_pc.eraseIdx j).countP isInval ≤ _
        omega
      · exact le_of_eq (congrArg (fun c : CacheState => c.queue_pc.countP isInval) (hyo k' hk))
    · show (y.caches k).queue_pc.countP isInval < (x.caches k).queue_pc.countP isInval
      rw [hyk]
      show ((x.caches k).queue_pc.eraseIdx j).countP isInval < _
      omega

theorem phase3_step {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0)
    (h2 : μ2 x = 0) (hpos : 0 < μ3 x) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  unfold μ3 at hpos
  obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
  obtain ⟨m, hm, hmi⟩ := List.countP_pos_iff.mp hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  cases m with
  | rsM v => simp [isInval] at hmi
  | rsS v => simp [isInval] at hmi
  | rsE v => simp [isInval] at hmi
  | rqIμ => exact phase3_step_M hI h0 h2 hj
  | rqIσ => exact phase3_step_S hI h0 h2 hj

theorem phase3 {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0) (h2 : μ2 x = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y = 0 := by
  suffices H : ∀ m, ∀ x : MESIState n, flushInv x s → μ1 x = 0 → μ2 x = 0 → μ3 x ≤ m →
      ∃ y, trans_refl (mesi_rule n) x y ∧ flushInv y s ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y = 0 from
    H _ x hI h0 h2 le_rfl
  intro m
  induction m with
  | zero =>
    intro x hI h0 h2 hm
    exact ⟨x, trans_refl.refl, hI, h0, h2, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hI h0 h2 hm
    by_cases h3 : μ3 x = 0
    · exact ⟨x, trans_refl.refl, hI, h0, h2, h3⟩
    · obtain ⟨y, hxy, h0y, h2y, hlt⟩ := phase3_step hI h0 h2 (Nat.pos_of_ne_zero h3)
      obtain ⟨z, hyz, hIz, h0z, h2z, h3z⟩ := ih y (inv_trans hI hxy) h0y h2y (by omega)
      exact ⟨z, phase2_aux1 hxy hyz, hIz, h0z, h2z, h3z⟩

/-! ### A misure nulle lo stato è flushed; il teorema -/

theorem flush_of_quiet {x : MESIState n} {s : SeqState n} (hI : flushInv x s) (h0 : μ1 x = 0)
    (h2 : μ2 x = 0) (h3 : μ3 x = 0) : flush0 x s := by
  have hcp : ∀ k, (x.caches k).queue_cp = [] := by
    intro k
    have hr := quiet_releases h0 k
    have h2' : Finset.univ.sum (fun k => (x.caches k).queue_cp.countP isRequest) = 0 := h2
    have hq : (x.caches k).queue_cp.countP isRequest = 0 := sum_eq_zero_iff_pointwise.mp h2' k
    rw [List.countP_eq_zero] at hr hq
    cases hl : (x.caches k).queue_cp with
    | nil => rfl
    | cons m t =>
      exfalso
      have hm : m ∈ (x.caches k).queue_cp := by rw [hl]; simp
      cases m
      · exact hr _ hm rfl
      · exact hr _ hm rfl
      · exact hq _ hm rfl
      · exact hq _ hm rfl
  have hpc : ∀ k, (x.caches k).queue_pc = [] := by
    intro k
    have hg := quiet_grants h0 k
    have h3' : Finset.univ.sum (fun k => (x.caches k).queue_pc.countP isInval) = 0 := h3
    have hq : (x.caches k).queue_pc.countP isInval = 0 := sum_eq_zero_iff_pointwise.mp h3' k
    rw [List.countP_eq_zero] at hg hq
    cases hl : (x.caches k).queue_pc with
    | nil => rfl
    | cons m t =>
      exfalso
      have hm : m ∈ (x.caches k).queue_pc := by rw [hl]; simp
      cases m
      · exact hq _ hm rfl
      · exact hq _ hm rfl
      · exact hg _ hm rfl
      · exact hg _ hm rfl
      · exact hg _ hm rfl
  refine flush0.intro ?_ ?_ hI.value
  · intro k
    exact ⟨quiet_caches h0 k, hcp k, hpc k⟩
  · intro k
    obtain ⟨hs1, hs2⟩ := hI.synced k
    exact ⟨quiet_rows hI h0 k, by rw [hs1, hcp k], by rw [hs2, hpc k]⟩

/-- `relation_flush` di ARS per `flush0`: da uno stato flushed, dopo una sequenza qualunque di passi
interni, si può tornare con passi interni a uno stato flushed per lo stesso `s`. -/
theorem mesi_relation_flush0 (i i' : MESIState n) (s : SeqState n) :
    relation_flush flush0 i i' s (mesi_rule n) := by
  unfold relation_flush
  intro hf htr
  have hI := inv_trans (inv_of_flush hf) htr
  obtain ⟨y1, h1, hI1, hq1⟩ := phase1 hI
  obtain ⟨y2, h2, hI2, hq1', hq2⟩ := phase2 hI1 hq1
  obtain ⟨y3, h3, hI3, a, b, c⟩ := phase3 hI2 hq1' hq2
  exact ⟨y3, phase2_aux1 (phase2_aux1 h1 h2) h3, flush_of_quiet hI3 a b c⟩

/-- Il caso a un passo del ritorno a flush (per `flush0`), da `mesi_relation_flush0`. -/
theorem mesi_relation_flush_one (i i' : MESIState n) (s : SeqState n) (e : MESIInternalEvent n) :
    flush0 i s → mesi_step_internal i e i' →
    ∃ i'', trans_refl (mesi_rule n) i' i'' ∧ flush0 i'' s := by
  intro hf h
  exact mesi_relation_flush0 i i' s hf (trans_refl.step (mesi_rule_of_step h) trans_refl.refl)

/-- Lo stesso fatto nel linguaggio di ARS: `φ_ind flush0 rule i' s` è "da `i'` si arriva con
`trans_refl rule` a uno stato flushed per `s`", cioè la proprietà che il framework propaga. -/
theorem mesi_flush_step_φ_ind (i i' : MESIState n) (s : SeqState n) (e : MESIInternalEvent n)
    (hf : flush0 i s) (h : mesi_step_internal i e i') : φ_ind flush0 (mesi_rule n) i' s := by
  obtain ⟨i'', htr, hf''⟩ := mesi_relation_flush_one i i' s e hf h
  exact φ_ind.rule_step _ _ _ (φ_ind.base _ _ hf'') htr


end ReturnToFlush



/-! ## Confluenza dei passi interni sugli stati raggiungibili (`h4` di `trace_inclusion`)

`has_diamond_property_on Reach (trans_refl (mesi_rule n))`: in ogni stato `a` raggiungibile da
`default` (passi interni ed esterni, `ReachingStar.reachable`) due riduzioni interne `a →* b` e
`a →* c` si ricongiungono. Non segue dalle commutazioni a un passo di MSI.lean (confluenza locale,
senza terminazione); la prova è per **stato canonico**: `canon a m` (tutte le cache in `I` con valore
`m`, code vuote, righe a `I`, parent a `m`, e in ogni `extqueue` le `ld_rq` in testa già servite con
`ld_rs m`) è raggiungibile con passi interni da ogni stato raggiungibile ed è invariante lungo i
passi interni, quindi è il ricongiungimento comune di `b` e `c`. Servono:
* `cohInv`, l'invariante di coerenza degli stati raggiungibili: le code sono sincronizzate, la riga
  della directory di `k` dice esattamente quanti token `M`/`S` di `k` esistono (`mtok`/`stok`, che
  contano cache in `M`/`S`, grant `rsM`/`rsS` e rilasci `rsIμ`/`rsIσ` in volo) e una riga `M`
  esclude tutte le altre; i passi interni della cache spostano i token senza cambiarne il numero;
* `LV x m`, il *valore logico*: il valore di ogni token `M`, di ogni cache/grant `S`, e del parent
  quando nessun token `M` è in giro. È unico ed è invariante lungo i passi interni (i passi interni
  non introducono valori nuovi); i passi esterni possono cambiarlo (`st_rs`), ma ne esiste sempre uno.
Il cammino verso `canon`: (1) `predrain`, si completa il ciclo dell'eventuale token `M` in giro, così
il parent vale `m` e vale `flushInv x ⟨m, _⟩`; (2) le tre fasi di `ReturnToFlush` portano a uno stato
flushed; (3) `serve_all` serve le `ld_rq` in testa a ogni `extqueue` (acquisendo `M`, servendo,
rilasciando); (4) `fix_all` porta a `m` i valori delle cache in `I` (acquisendo e rilasciando `M`).
Lo stato ottenuto è `canon` (`canon_of_flush`). -/

section ConfluenceOnReachable

/-- Raggiungibilità nel senso di ARS: da `default` con passi interni ed esterni. -/
def Reach (x : MESIState n) : Prop :=
  ReachingStar.reachable (mesi_rule n) mesi_step_external x (default : MESIState n)

/-- Token `M` di una cache: stato `M`, grant `rsM` in volo, rilasci `rsIμ` in volo. -/
def mtokC (c : CacheState) : Nat :=
  (if c.state = Bstate.M ∨ c.state = Bstate.E then 1 else 0) + c.queue_pc.countP isGrantX
    + c.queue_cp.countP isReleaseX

/-- Token `S` di una cache: stato `S`, grant `rsS` in volo, rilasci `rsIσ` in volo. -/
def stokC (c : CacheState) : Nat :=
  (if c.state = Bstate.S then 1 else 0) + c.queue_pc.countP isGrantS
    + c.queue_cp.countP isReleaseS

def mtok (x : MESIState n) (k : Fin n) : Nat := mtokC (x.caches k)
def stok (x : MESIState n) (k : Fin n) : Nat := stokC (x.caches k)

/-- L'invariante di coerenza degli stati raggiungibili. -/
structure cohInv (x : MESIState n) : Prop where
  synced : synced x
  rowM : ∀ k, (x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E) → mtok x k = 1 ∧ stok x k = 0
  rowS : ∀ k, x.parent.shared_state k = Bstate.S → stok x k = 1 ∧ mtok x k = 0
  rowI : ∀ k, x.parent.shared_state k = Bstate.I → mtok x k = 0 ∧ stok x k = 0
  excl : ∀ k k', (x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E) → k' ≠ k →
    x.parent.shared_state k' = Bstate.I

/-- `m` è il valore logico di `x`. -/
structure LV (x : MESIState n) (m : Value) : Prop where
  cacheM : ∀ k, ((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E) → (x.caches k).value = m
  cacheS : ∀ k, (x.caches k).state = Bstate.S → (x.caches k).value = m
  grantM : ∀ k v, (PCEvent.rsM v ∈ (x.caches k).queue_pc ∨ PCEvent.rsE v ∈ (x.caches k).queue_pc) → v = m
  grantS : ∀ k v, PCEvent.rsS v ∈ (x.caches k).queue_pc → v = m
  release : ∀ k v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp → v = m
  parent : (∀ k, mtok x k = 0) → x.parent.value = m

/-- Lo stato canonico di `x` con valore logico `m`: tutte le cache in `I` con valore `m`, code
vuote, righe a `I`, parent a `m`, `extqueue` quelle di `x` (i passi interni non le toccano). -/
def canon (x : MESIState n) (m : Value) : MESIState n :=
  ⟨fun k => ⟨Bstate.I, m, [], [], (x.caches k).extqueue⟩,
   ⟨m, fun _ => Bstate.I, fun _ => [], fun _ => []⟩⟩

/-- Misura di `fix_all`: cache con valore diverso da `m`. -/
def μ4 (x : MESIState n) (m : Value) : Nat :=
  Finset.univ.sum (fun k => if (x.caches k).value = m then 0 else 1)

/-! ### Lemmi sui token -/

/-- Un passo interno della cache non cambia il numero dei suoi token. -/
theorem tok_cache_step {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_mesi_step_internal c e c') : mtokC c' = mtokC c ∧ stokC c' = stokC c := by
  cases h with
  | rq_data_not_available hM =>
    unfold mtokC stokC
    simp [hM, List.countP_append, isReleaseX, isReleaseS]
    omega
  | rq_data_not_available1 hS =>
    unfold mtokC stokC
    simp [hS, List.countP_append, isReleaseX, isReleaseS]
    omega
  | rq_data_not_availableE hE =>
    unfold mtokC stokC
    simp [hE, List.countP_append, isReleaseX, isReleaseS]
    omega
  | upgrade_from_I_rq hI =>
    unfold mtokC stokC
    simp [hI, List.countP_append, isReleaseX, isReleaseS]
  | upgrade_from_I_rq1 hI =>
    unfold mtokC stokC
    simp [hI, List.countP_append, isReleaseX, isReleaseS]
  | upgrade_from_I_rs v j hj hI =>
    have h1 := countP_eraseIdx_pos hj (rfl : isGrantX (PCEvent.rsM v) = true)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantS (PCEvent.rsM v) = false)
    unfold mtokC stokC
    simp [hI]
    omega
  | upgrade_from_I_rsS v j hj hI =>
    have h1 := countP_eraseIdx_pos hj (rfl : isGrantS (PCEvent.rsS v) = true)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantX (PCEvent.rsS v) = false)
    unfold mtokC stokC
    simp [hI]
    omega
  | upgrade_from_I_rsE v j hj hI =>
    have h1 := countP_eraseIdx_pos hj (rfl : isGrantX (PCEvent.rsE v) = true)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantS (PCEvent.rsE v) = false)
    unfold mtokC stokC
    simp [hI]
    omega
  | upgrade_from_E hE =>
    unfold mtokC stokC
    simp [hE]
  | downgrade_from_M_rs j hj hM =>
    have h1 := countP_eraseIdx_neg hj (rfl : isGrantX PCEvent.rqIμ = false)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantS PCEvent.rqIμ = false)
    unfold mtokC stokC
    simp [hM, List.countP_append, isReleaseX, isReleaseS]
    omega
  | downgrade_from_E_rs j hj hE =>
    have h1 := countP_eraseIdx_neg hj (rfl : isGrantX PCEvent.rqIμ = false)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantS PCEvent.rqIμ = false)
    unfold mtokC stokC
    simp [hE, List.countP_append, isReleaseX, isReleaseS]
    omega
  | downgrade_from_M_rs1 j hj hS =>
    have h1 := countP_eraseIdx_neg hj (rfl : isGrantX PCEvent.rqIσ = false)
    have h2 := countP_eraseIdx_neg hj (rfl : isGrantS PCEvent.rqIσ = false)
    unfold mtokC stokC
    simp [hS, List.countP_append, isReleaseX, isReleaseS]
    omega

/-- Un passo esterno della cache non cambia il numero dei suoi token. -/
theorem tok_cache_step_ext {c c' : CacheState} {e : Event}
    (h : cache_mesi_step c e c') : mtokC c' = mtokC c ∧ stokC c' = stokC c := by
  cases h with
  | ld_rq => exact ⟨rfl, rfl⟩
  | st_rq v => exact ⟨rfl, rfl⟩
  | ld_rq_data_available1 rst hrq hS => exact ⟨rfl, rfl⟩
  | ld_rq_data_available rst hrq hM => exact ⟨rfl, rfl⟩
  | ld_rq_data_availableE rst hrq hE => exact ⟨rfl, rfl⟩
  | st_rq_M_state v rst hrq hM => exact ⟨rfl, rfl⟩

/-- Un solo token `M`: è la cache in `M`, oppure un `rsM` in volo, oppure un `rsIμ` in volo. -/
theorem mtok_one_cases {x : MESIState n} {k : Fin n} (h : mtok x k = 1) :
    (((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
        ∧ (x.caches k).queue_pc.countP isGrantX = 0
        ∧ (x.caches k).queue_cp.countP isReleaseX = 0)
    ∨ (¬((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
        ∧ (∃ v, PCEvent.rsM v ∈ (x.caches k).queue_pc ∨ PCEvent.rsE v ∈ (x.caches k).queue_pc)
        ∧ (x.caches k).queue_cp.countP isReleaseX = 0)
    ∨ (¬((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
        ∧ (x.caches k).queue_pc.countP isGrantX = 0
        ∧ (∃ v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp)) := by
  unfold mtok mtokC at h
  by_cases hx : ((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
  · rw [if_pos hx] at h
    exact Or.inl ⟨hx, by omega, by omega⟩
  · rw [if_neg hx] at h
    by_cases hg : (x.caches k).queue_pc.countP isGrantX = 0
    · have hpos : 0 < (x.caches k).queue_cp.countP isReleaseX := by omega
      obtain ⟨m, hm, hp⟩ := List.countP_pos_iff.mp hpos
      refine Or.inr (Or.inr ⟨hx, hg, ?_⟩)
      cases m with
      | rsIμ v => exact ⟨v, hm⟩
      | rsIσ => simp [isReleaseX] at hp
      | rqS => simp [isReleaseX] at hp
      | rqM => simp [isReleaseX] at hp
    · have hpos : 0 < (x.caches k).queue_pc.countP isGrantX := Nat.pos_of_ne_zero hg
      obtain ⟨m, hm, hp⟩ := List.countP_pos_iff.mp hpos
      refine Or.inr (Or.inl ⟨hx, ?_, by omega⟩)
      cases m with
      | rsM v => exact ⟨v, Or.inl hm⟩
      | rsE v => exact ⟨v, Or.inr hm⟩
      | rsS v => simp [isGrantX] at hp
      | rqIμ => simp [isGrantX] at hp
      | rqIσ => simp [isGrantX] at hp

theorem tokenS_of_stok_pos {x : MESIState n} {k : Fin n} (h : 0 < stok x k) : tokenS x k := by
  unfold stok stokC at h
  unfold tokenS
  by_cases hS : (x.caches k).state = Bstate.S
  · exact Or.inl hS
  · rw [if_neg hS] at h
    by_cases hg : (x.caches k).queue_pc.countP isGrantS = 0
    · have hpos : 0 < (x.caches k).queue_cp.countP isReleaseS := by omega
      obtain ⟨m, hm, hp⟩ := List.countP_pos_iff.mp hpos
      cases m with
      | rsIσ => exact Or.inr (Or.inr hm)
      | rsIμ v => simp [isReleaseS] at hp
      | rqS => simp [isReleaseS] at hp
      | rqM => simp [isReleaseS] at hp
    · have hpos : 0 < (x.caches k).queue_pc.countP isGrantS := Nat.pos_of_ne_zero hg
      obtain ⟨m, hm, hp⟩ := List.countP_pos_iff.mp hpos
      cases m with
      | rsS v => exact Or.inr (Or.inl ⟨v, hm⟩)
      | rsM v => simp [isGrantS] at hp
      | rsE v => simp [isGrantS] at hp
      | rqIμ => simp [isGrantS] at hp
      | rqIσ => simp [isGrantS] at hp

theorem mtok_zero_facts {x : MESIState n} {k : Fin n} (h : mtok x k = 0) :
    ¬((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
      ∧ (∀ v, PCEvent.rsM v ∉ (x.caches k).queue_pc ∧ PCEvent.rsE v ∉ (x.caches k).queue_pc)
      ∧ (∀ v, CPEvent.rsIμ v ∉ (x.caches k).queue_cp) := by
  unfold mtok mtokC at h
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    rw [if_pos hx] at h
    omega
  · intro v
    have hg : (x.caches k).queue_pc.countP isGrantX = 0 := by omega
    exact ⟨fun hv => List.countP_eq_zero.mp hg _ hv rfl,
           fun hv => List.countP_eq_zero.mp hg _ hv rfl⟩
  · intro v hv
    have hr : (x.caches k).queue_cp.countP isReleaseX = 0 := by omega
    exact List.countP_eq_zero.mp hr _ hv rfl

theorem stok_zero_facts {x : MESIState n} {k : Fin n} (h : stok x k = 0) :
    (x.caches k).state ≠ Bstate.S ∧ (∀ v, PCEvent.rsS v ∉ (x.caches k).queue_pc)
      ∧ CPEvent.rsIσ ∉ (x.caches k).queue_cp := by
  unfold stok stokC at h
  refine ⟨?_, ?_, ?_⟩
  · intro hS
    rw [if_pos hS] at h
    omega
  · intro v hv
    have hg : (x.caches k).queue_pc.countP isGrantS = 0 := by omega
    exact List.countP_eq_zero.mp hg _ hv rfl
  · intro hv
    have hr : (x.caches k).queue_cp.countP isReleaseS = 0 := by omega
    exact List.countP_eq_zero.mp hr _ hv rfl

/-! ### `cohInv`: vale in `default`, conservato da passi interni ed esterni -/

theorem coh_default : cohInv (default : MESIState n) := by
  refine ⟨fun k => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro k h
    rcases h with h | h
    · change Bstate.I = Bstate.M at h
      cases h
    · change Bstate.I = Bstate.E at h
      cases h
  · intro k h
    change Bstate.I = Bstate.S at h
    cases h
  · intro k _
    exact ⟨rfl, rfl⟩
  · intro k k' h _
    rcases h with h | h
    · change Bstate.I = Bstate.M at h
      cases h
    · change Bstate.I = Bstate.E at h
      cases h

theorem coh_step_cache_aux1 {x : MESIState n} {k : Fin n} {c' : CacheState}
    (htm : mtokC c' = mtokC (x.caches k)) (k' : Fin n) :
    mtokC (update_Fin k c' x.caches k') = mtokC (x.caches k') := by
  by_cases hk : k' = k
  · subst hk
    simp only [update_Fin_gss]
    exact htm
  · simp only [update_Fin_gso2 _ _ _ _ hk]

theorem coh_step_cache_aux2 {x : MESIState n} {k : Fin n} {c' : CacheState}
    (hts : stokC c' = stokC (x.caches k)) (k' : Fin n) :
    stokC (update_Fin k c' x.caches k') = stokC (x.caches k') := by
  by_cases hk : k' = k
  · subst hk
    simp only [update_Fin_gss]
    exact hts
  · simp only [update_Fin_gso2 _ _ _ _ hk]

theorem coh_step_cache {x : MESIState n} {k : Fin n} {e : CacheInternalEvent} {c' : CacheState}
    (hc : cohInv x) (h : cache_mesi_step_internal (x.caches k) e c') :
    cohInv { x with caches := update_Fin k c' x.caches,
                    parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                    parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } := by
  obtain ⟨hs, hM, hS, hI, hex⟩ := hc
  obtain ⟨htm, hts⟩ := tok_cache_step h
  refine ⟨synced_step hs (mesi_step_internal.cache x c' k e h), ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    show mtokC (update_Fin k c' x.caches k') = 1 ∧ stokC (update_Fin k c' x.caches k') = 0
    rw [coh_step_cache_aux1 htm, coh_step_cache_aux2 hts]
    exact hM k' hk'
  · intro k' hk'
    show stokC (update_Fin k c' x.caches k') = 1 ∧ mtokC (update_Fin k c' x.caches k') = 0
    rw [coh_step_cache_aux1 htm, coh_step_cache_aux2 hts]
    exact hS k' hk'
  · intro k' hk'
    show mtokC (update_Fin k c' x.caches k') = 0 ∧ stokC (update_Fin k c' x.caches k') = 0
    rw [coh_step_cache_aux1 htm, coh_step_cache_aux2 hts]
    exact hI k' hk'
  · intro k1 k2 hk1 hne
    exact hex k1 k2 hk1 hne

/-- Una riga aggiornata con `update_Fin` non può leggersi come un valore diverso. -/
theorem coh_step_parent_aux0 {f : Fin n → Bstate} {k : Fin n} {b c : Bstate} (hbc : b ≠ c)
    (h : update_Fin k b f k = c) : False := by
  rw [update_Fin_gss] at h
  exact hbc h

/-- Come `coh_step_parent_aux1`, ma con le premesse `M ∨ E` (quelle di `cohInv.rowM`/`excl`). -/
theorem coh_step_parent_aux3 {x y : MESIState n} {k : Fin n} (hc : cohInv x)
    (hs' : synced y)
    (hyc : ∀ k', k' ≠ k → y.caches k' = x.caches k')
    (hyp : ∀ k', k' ≠ k → y.parent.shared_state k' = x.parent.shared_state k')
    (hkM : (y.parent.shared_state k = Bstate.M ∨ y.parent.shared_state k = Bstate.E) →
      mtok y k = 1 ∧ stok y k = 0)
    (hkS : y.parent.shared_state k = Bstate.S → stok y k = 1 ∧ mtok y k = 0)
    (hkI : y.parent.shared_state k = Bstate.I → mtok y k = 0 ∧ stok y k = 0)
    (hexcl : (y.parent.shared_state k = Bstate.M ∨ y.parent.shared_state k = Bstate.E) →
      ∀ k', k' ≠ k → x.parent.shared_state k' = Bstate.I)
    (hexcl' : ∀ k', k' ≠ k →
      (x.parent.shared_state k' = Bstate.M ∨ x.parent.shared_state k' = Bstate.E) →
      y.parent.shared_state k = Bstate.I) :
    cohInv y := by
  obtain ⟨_, hM, hS, hI, hex⟩ := hc
  have hmt : ∀ k', k' ≠ k → mtok y k' = mtok x k' := fun k' hk' => by
    unfold mtok; rw [hyc k' hk']
  have hst : ∀ k', k' ≠ k → stok y k' = stok x k' := fun k' hk' => by
    unfold stok; rw [hyc k' hk']
  refine ⟨hs', ?_, ?_, ?_, ?_⟩
  · intro k' hr
    by_cases hk' : k' = k
    · subst hk'; exact hkM hr
    · rw [hmt k' hk', hst k' hk']
      exact hM k' (by rw [← hyp k' hk']; exact hr)
  · intro k' hr
    by_cases hk' : k' = k
    · subst hk'; exact hkS hr
    · rw [hmt k' hk', hst k' hk']
      exact hS k' (by rw [← hyp k' hk']; exact hr)
  · intro k' hr
    by_cases hk' : k' = k
    · subst hk'; exact hkI hr
    · rw [hmt k' hk', hst k' hk']
      exact hI k' (by rw [← hyp k' hk']; exact hr)
  · intro a b ha hab
    by_cases hak : a = k
    · subst hak
      rw [hyp b hab]
      exact hexcl ha b hab
    · by_cases hbk : b = k
      · subst hbk
        exact hexcl' a hak (by rw [← hyp a hak]; exact ha)
      · rw [hyp b hbk]
        exact hex a b (by rw [← hyp a hak]; exact ha) hab

/-- Le quattro invalidazioni: il parent accoda a `queue_pci k` un messaggio senza token
(`rqIμ`/`rqIσ`), righe e token restano uguali. -/
theorem coh_step_parent_aux2 {x : MESIState n} {k : Fin n} {P : ParentState n} {a : PCEvent}
    (hc : cohInv x)
    (hs' : synced { x with
        caches := update_Fin k { x.caches k with queue_cp := P.queue_cip k, queue_pc := P.queue_pci k } x.caches,
        parent := P })
    (hloc : ∀ k', k' ≠ k → P.queue_cip k' = x.parent.queue_cip k' ∧ P.queue_pci k' = x.parent.queue_pci k'
                    ∧ P.shared_state k' = x.parent.shared_state k')
    (hrow : P.shared_state k = x.parent.shared_state k)
    (hcip : P.queue_cip k = x.parent.queue_cip k)
    (hpci : P.queue_pci k = x.parent.queue_pci k ++ [a])
    (ha : List.countP isGrantX [a] = 0) (hb : List.countP isGrantS [a] = 0) :
    cohInv { x with
      caches := update_Fin k { x.caches k with queue_cp := P.queue_cip k, queue_pc := P.queue_pci k } x.caches,
      parent := P } := by
  have hs := hc.synced
  have hm : mtokC { x.caches k with queue_cp := P.queue_cip k, queue_pc := P.queue_pci k }
      = mtok x k := by
    unfold mtok mtokC
    simp only [hcip, hpci, List.countP_append, (hs k).1, (hs k).2, ha, Nat.add_zero]
  have hst : stokC { x.caches k with queue_cp := P.queue_cip k, queue_pc := P.queue_pci k }
      = stok x k := by
    unfold stok stokC
    simp only [hcip, hpci, List.countP_append, (hs k).1, (hs k).2, hb, Nat.add_zero]
  refine coh_step_parent_aux3 hc hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
    (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
  · intro hr
    have hr' : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E := by
      rw [← hrow]; exact hr
    unfold mtok stok
    simp only [update_Fin_gss]
    rw [hm, hst]
    exact hc.rowM k hr'
  · intro hr
    have hr' : x.parent.shared_state k = Bstate.S := by rw [← hrow]; exact hr
    unfold mtok stok
    simp only [update_Fin_gss]
    rw [hm, hst]
    exact hc.rowS k hr'
  · intro hr
    have hr' : x.parent.shared_state k = Bstate.I := by rw [← hrow]; exact hr
    unfold mtok stok
    simp only [update_Fin_gss]
    rw [hm, hst]
    exact hc.rowI k hr'
  · intro hr k' hk'
    have hr' : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E := by
      rw [← hrow]; exact hr
    exact hc.excl k k' hr' hk'
  · intro k' hk' hM'
    show P.shared_state k = Bstate.I
    rw [hrow]
    exact hc.excl k' k hM' (Ne.symm hk')

theorem coh_step_parent {x : MESIState n} {k : Fin n} {e : ParentUpdQueueInternalEvent n}
    {p' : ParentState n} (hc : cohInv x) (h : parent_mesi_step x.parent (.upd_queue e k) p') :
    cohInv { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                              queue_pc := p'.queue_pci k } x.caches,
                    parent := p' } := by
  have hs' := synced_step hc.synced (mesi_step_internal.parent_upd_queue x p' e k h)
  have hloc := parent_step_local h
  have hc0 := hc
  obtain ⟨hs, hM, hS, hI, hex⟩ := hc
  cases h with
  | downgrade_from_M_rq1 v i j hj =>
    -- rilascio da `M`/`E`: la riga di `k` era `M` o `E`, ora `I`, il token `rsIμ` sparisce
    refine coh_step_parent_aux3 hc0 hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
      (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro _
      rw [(hs k).1] at hj
      have e1 := countP_eraseIdx_pos (p := isReleaseX) hj rfl
      have e2 := countP_eraseIdx_neg (p := isReleaseS) hj rfl
      have hrow : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E := by
        cases hr : x.parent.shared_state k with
        | M => exact Or.inl rfl
        | E => exact Or.inr rfl
        | I => have := (hI k hr).1; unfold mtok mtokC at this; omega
        | S => have := (hS k hr).2; unfold mtok mtokC at this; omega
      obtain ⟨h1, h0⟩ := hM k hrow
      unfold mtok mtokC at h1
      unfold stok stokC at h0
      unfold mtok mtokC stok stokC
      simp only [update_Fin_gss, (hs k).1, (hs k).2]
      exact ⟨by omega, by omega⟩
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro k' _ _; exact update_Fin_gss k Bstate.I x.parent.shared_state
  | downgrade_from_M_rq2 i j hj =>
    -- rilascio da `S`: la riga di `k` era `S`, ora `I`, il token `rsIσ` sparisce
    refine coh_step_parent_aux3 hc0 hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
      (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro _
      rw [(hs k).1] at hj
      have e1 := countP_eraseIdx_pos (p := isReleaseS) hj rfl
      have e2 := countP_eraseIdx_neg (p := isReleaseX) hj rfl
      have hrow : x.parent.shared_state k = Bstate.S := by
        cases hr : x.parent.shared_state k with
        | S => rfl
        | I => have := (hI k hr).2; unfold stok stokC at this; omega
        | M => have := (hM k (Or.inl hr)).2; unfold stok stokC at this; omega
        | E => have := (hM k (Or.inr hr)).2; unfold stok stokC at this; omega
      obtain ⟨h1, h0⟩ := hS k hrow
      unfold stok stokC at h1
      unfold mtok mtokC at h0
      unfold mtok mtokC stok stokC
      simp only [update_Fin_gss, (hs k).1, (hs k).2]
      exact ⟨by omega, by omega⟩
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro k' _ _; exact update_Fin_gss k Bstate.I x.parent.shared_state
  | upgrade_to_M_data_avilable_rq1 i j hj hall =>
    -- grant di `M`: tutte le righe a `I`, la riga di `k` diventa `M` e nasce il token `rsM`
    refine coh_step_parent_aux3 hc0 hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
      (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
    · intro _
      rw [(hs k).1] at hj
      have e1 := countP_eraseIdx_neg (p := isReleaseX) hj rfl
      have e2 := countP_eraseIdx_neg (p := isReleaseS) hj rfl
      have e3 : List.countP isGrantX [PCEvent.rsM x.parent.value] = 1 := rfl
      have e4 : List.countP isGrantS [PCEvent.rsM x.parent.value] = 0 := rfl
      obtain ⟨h1, h0⟩ := hI k (hall k)
      unfold mtok mtokC at h1
      unfold stok stokC at h0
      unfold mtok mtokC stok stokC
      simp only [update_Fin_gss, List.countP_append, (hs k).1, (hs k).2]
      exact ⟨by omega, by omega⟩
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro _ k' _; exact hall k'
    · intro k' _ hM'
      rw [hall k'] at hM'
      rcases hM' with h | h <;> cases h
  | upgrade_to_M_data_avilable_rq2 i j hj hIk hnoM hnoE =>
    -- grant di `S`: la riga di `k` era `I`, diventa `S` e nasce il token `rsS`
    refine coh_step_parent_aux3 hc0 hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
      (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro _
      rw [(hs k).1] at hj
      have e1 := countP_eraseIdx_neg (p := isReleaseX) hj rfl
      have e2 := countP_eraseIdx_neg (p := isReleaseS) hj rfl
      have e3 : List.countP isGrantX [PCEvent.rsS x.parent.value] = 0 := rfl
      have e4 : List.countP isGrantS [PCEvent.rsS x.parent.value] = 1 := rfl
      obtain ⟨h1, h0⟩ := hI k hIk
      unfold mtok mtokC at h1
      unfold stok stokC at h0
      unfold mtok mtokC stok stokC
      simp only [update_Fin_gss, List.countP_append, (hs k).1, (hs k).2]
      exact ⟨by omega, by omega⟩
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro hr
      rcases hr with hr | hr <;> exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro k' _ hM'
      rcases hM' with hM' | hM'
      · exact absurd hM' (hnoM k')
      · exact absurd hM' (hnoE k')
  | upgrade_to_E i j hj hall =>
    -- grant di `E`: tutte le righe a `I`, la riga di `k` diventa `E` e nasce il token `rsE`
    refine coh_step_parent_aux3 hc0 hs' (fun k' hk' => update_Fin_gso2 _ _ _ _ hk')
      (fun k' hk' => (hloc k' hk').2.2) ?_ ?_ ?_ ?_ ?_
    · intro _
      rw [(hs k).1] at hj
      have e1 := countP_eraseIdx_neg (p := isReleaseX) hj rfl
      have e2 := countP_eraseIdx_neg (p := isReleaseS) hj rfl
      have e3 : List.countP isGrantX [PCEvent.rsE x.parent.value] = 1 := rfl
      have e4 : List.countP isGrantS [PCEvent.rsE x.parent.value] = 0 := rfl
      obtain ⟨h1, h0⟩ := hI k (hall k)
      unfold mtok mtokC at h1
      unfold stok stokC at h0
      unfold mtok mtokC stok stokC
      simp only [update_Fin_gss, List.countP_append, (hs k).1, (hs k).2]
      exact ⟨by omega, by omega⟩
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro hr; exact (coh_step_parent_aux0 (by intro h; cases h) hr).elim
    · intro _ k' _; exact hall k'
    · intro k' _ hM'
      rw [hall k'] at hM'
      rcases hM' with h | h <;> cases h
  | upgrade_to_M_invalid_all i i' j hj hM' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl
  | upgrade_to_M_invalid_allE i i' j hj hE' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl
  | upgrade_to_M_invalid_all1 i i' j hj hS' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl
  | upgrade_to_M_invalid_all2 i i' j hj hne hS' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl
  | upgrade_to_M_invalid_all3 i i' j hj hM' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl
  | upgrade_to_S_invalid_E i i' j hj hE' =>
    exact coh_step_parent_aux2 hc0 hs' hloc rfl rfl (update_Fin_gss _ _ _) rfl rfl

theorem coh_step {x y : MESIState n} {e : MESIInternalEvent n} (hc : cohInv x)
    (h : mesi_step_internal x e y) : cohInv y := by
  cases h with
  | cache c' k e' hc' => exact coh_step_cache hc hc'
  | parent_upd_queue p' e' k hp => exact coh_step_parent hc hp

/-- Trasferimento di `cohInv` a uno stato con le stesse righe e gli stessi token. -/
theorem coh_step_ext_aux1 {x y : MESIState n} (hc : cohInv x) (hs : synced y)
    (hrow : ∀ k, y.parent.shared_state k = x.parent.shared_state k)
    (hm : ∀ k, mtok y k = mtok x k) (hst : ∀ k, stok y k = stok x k) : cohInv y := by
  obtain ⟨_, hM, hS, hI, hex⟩ := hc
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · intro k h
    rw [hm, hst]
    exact hM k (by rw [← hrow k]; exact h)
  · intro k h
    rw [hm, hst]
    exact hS k (by rw [← hrow k]; exact h)
  · intro k h
    rw [hm, hst]
    exact hI k (by rw [← hrow k]; exact h)
  · intro k k' h hne
    rw [hrow k']
    exact hex k k' (by rw [← hrow k]; exact h) hne

theorem coh_step_ext {x y : MESIState n} {e : MSIExternalEvent n} (hc : cohInv x) (h : mesi_step_external x e y) :
    cohInv y := by
  cases h with
  | cache ev c' k hc' =>
    obtain ⟨hm, hst⟩ := tok_cache_step_ext hc'
    refine coh_step_ext_aux1 hc ?_ (fun _ => rfl) ?_ ?_
    · intro k'
      by_cases hk : k' = k
      · subst hk
        constructor <;> simp only [update_Fin_gss]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
        exact hc.synced k'
    · intro k'
      by_cases hk : k' = k
      · subst hk
        simp only [mtok, update_Fin_gss]
        exact hm
      · simp only [mtok, update_Fin_gso2 _ _ _ _ hk]
    · intro k'
      by_cases hk : k' = k
      · subst hk
        simp only [stok, update_Fin_gss]
        exact hst
      · simp only [stok, update_Fin_gso2 _ _ _ _ hk]

/-! ### `LV`: esiste in `default`, conservato dai passi interni, esiste dopo i passi esterni -/

theorem lv_default : LV (default : MESIState n) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h
    rcases h with h | h
    · change Bstate.I = Bstate.M at h
      cases h
    · change Bstate.I = Bstate.E at h
      cases h
  · intro k h
    change Bstate.I = Bstate.S at h
    cases h
  · intro k v h
    rcases h with h | h
    · change PCEvent.rsM v ∈ ([] : List PCEvent) at h
      simp at h
    · change PCEvent.rsE v ∈ ([] : List PCEvent) at h
      simp at h
  · intro k v h
    change PCEvent.rsS v ∈ ([] : List PCEvent) at h
    simp at h
  · intro k v h
    change CPEvent.rsIμ v ∈ ([] : List CPEvent) at h
    simp at h
  · intro _
    rfl

/-- Ausiliario di `lv_step_cache` (variante MESI di `lv_step_cache_aux1`): una cache non in `I`
ha il valore logico, con l'ipotesi su `M` estesa a `M ∨ E` come in `LV.cacheM`. -/
theorem lv_step_cache_aux2 {s1 : CacheState} {m : Value}
    (hcM : (s1.state = Bstate.M ∨ s1.state = Bstate.E) → s1.value = m)
    (hcS : s1.state = Bstate.S → s1.value = m) :
    s1.state ≠ Bstate.I → s1.value = m := by
  intro hne
  cases hs : s1.state with
  | M => exact hcM (Or.inl hs)
  | E => exact hcM (Or.inr hs)
  | S => exact hcS hs
  | I => exact (hne hs).elim

/-- Ausiliario di `lv_step_cache` (variante MESI di `inv_step_cache_aux3`): il valore di una cache
non in `I` resta il valore logico, tenendo conto anche dei grant `rsE`. -/
theorem lv_step_cache_aux3 {s1 c' : CacheState} {e : CacheInternalEvent} {m : Value}
    (h : cache_mesi_step_internal s1 e c')
    (hcv : s1.state ≠ Bstate.I → s1.value = m)
    (hgv : ∀ v, (PCEvent.rsM v ∈ s1.queue_pc ∨ PCEvent.rsE v ∈ s1.queue_pc) → v = m)
    (hgS : ∀ v, PCEvent.rsS v ∈ s1.queue_pc → v = m) :
    c'.state ≠ Bstate.I → c'.value = m := by
  cases h with
  | rq_data_not_available hM => intro hne; exact (hne rfl).elim
  | rq_data_not_available1 hS => intro hne; exact (hne rfl).elim
  | rq_data_not_availableE hE => intro hne; exact (hne rfl).elim
  | upgrade_from_I_rq hI => intro hne; exact hcv hne
  | upgrade_from_I_rq1 hI => intro hne; exact hcv hne
  | upgrade_from_I_rs v j hj hI => intro _; exact hgv v (Or.inl (List.mem_of_getElem? hj))
  | upgrade_from_I_rsS v j hj hI => intro _; exact hgS v (List.mem_of_getElem? hj)
  | upgrade_from_I_rsE v j hj hI => intro _; exact hgv v (Or.inr (List.mem_of_getElem? hj))
  | upgrade_from_E hE => intro _; exact hcv (fun hh => Bstate.noConfusion (hE.symm.trans hh))
  | downgrade_from_M_rs j hj hM => intro hne; exact (hne rfl).elim
  | downgrade_from_E_rs j hj hE => intro hne; exact (hne rfl).elim
  | downgrade_from_M_rs1 j hj hS => intro hne; exact (hne rfl).elim

theorem lv_step_cache {x : MESIState n} {m : Value} {k : Fin n} {e : CacheInternalEvent}
    {c' : CacheState} (_hc : cohInv x) (hl : LV x m) (h : cache_mesi_step_internal (x.caches k) e c') :
    LV { x with caches := update_Fin k c' x.caches,
                parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } m := by
  obtain ⟨hcM, hcS, hgM, hgS, hrel, hpar⟩ := hl
  have hcv : (x.caches k).state ≠ Bstate.I → (x.caches k).value = m :=
    lv_step_cache_aux2 (hcM k) (hcS k)
  have hval := lv_step_cache_aux3 h hcv (hgM k) (hgS k)
  have hpc := inv_step_cache_aux4 h
  have hrel' := inv_step_cache_aux5 h hcv (hrel k)
  obtain ⟨htm, _⟩ := tok_cache_step h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      refine hval (fun hh => ?_)
      rcases hk' with hk' | hk'
      · exact Bstate.noConfusion (hk'.symm.trans hh)
      · exact Bstate.noConfusion (hk'.symm.trans hh)
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcM _ hk'
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hval (fun hh => Bstate.noConfusion (hk'.symm.trans hh))
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcS _ hk'
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      rcases hv with hv | hv
      · exact hgM _ v (Or.inl (hpc _ hv))
      · exact hgM _ v (Or.inr (hpc _ hv))
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hgM _ v hv
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact hgS _ v (hpc _ hv)
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hgS _ v hv
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact hrel' v hv
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hrel _ v hv
  · intro hall
    show x.parent.value = m
    apply hpar
    intro k'
    have hk0 := hall k'
    unfold mtok at hk0 ⊢
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk0
      rw [← htm]
      exact hk0
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk0
      exact hk0

/-- Versione di `lv_step_parent_aux1` con l'ipotesi sui grant `rsE` (necessaria per il campo
`grantM` di `LV`, che in MESI copre `rsM` e `rsE`). -/
theorem lv_step_parent_aux1_aux1 {x : MESIState n} {m : Value} {k : Fin n} {p' : ParentState n}
    (hl : LV x m)
    (hgM : ∀ v, PCEvent.rsM v ∈ p'.queue_pci k → v = m)
    (hgE : ∀ v, PCEvent.rsE v ∈ p'.queue_pci k → v = m)
    (hgS : ∀ v, PCEvent.rsS v ∈ p'.queue_pci k → v = m)
    (hrel : ∀ v, CPEvent.rsIμ v ∈ p'.queue_cip k → v = m)
    (hpar : (∀ k', mtok { x with
                caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } k' = 0) → p'.value = m) :
    LV { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } m := by
  obtain ⟨hcM, hcS, hgM0, hgS0, hrel0, _⟩ := hl
  refine ⟨?_, ?_, ?_, ?_, ?_, hpar⟩
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hcM _ hk'
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcM k' hk'
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hcS _ hk'
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcS k' hk'
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      rcases hmem with hmem | hmem
      · exact hgM v hmem
      · exact hgE v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hgM0 k' v hmem
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hgS v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hgS0 k' v hmem
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hrel v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hrel0 k' v hmem

/-- Ausiliario di `lv_step_parent`: se i token `M` di `k` nelle copie lato parent non cambiano,
"nessun token `M`" dopo il passo dà "nessun token `M`" prima. -/
theorem lv_step_parent_aux2 {x : MESIState n} {k : Fin n} {p' : ParentState n}
    (hM : (p'.queue_pci k).countP isGrantX = (x.caches k).queue_pc.countP isGrantX)
    (hR : (p'.queue_cip k).countP isReleaseX
            = (x.caches k).queue_cp.countP isReleaseX)
    (h0 : ∀ k', mtok { x with
                caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } k' = 0) :
    ∀ k', mtok x k' = 0 := by
  intro k'
  have this := h0 k'
  by_cases hk : k' = k
  · subst hk
    unfold mtok mtokC at this ⊢
    simp only [update_Fin_gss] at this
    rw [hM, hR] at this
    exact this
  · unfold mtok at this ⊢
    simp only [update_Fin_gso2 _ _ _ _ hk] at this
    exact this

theorem lv_step_parent {x : MESIState n} {m : Value} {k : Fin n} {e : ParentUpdQueueInternalEvent n}
    {p' : ParentState n} (hc : cohInv x) (hl : LV x m) (h : parent_mesi_step x.parent (.upd_queue e k) p') :
    LV { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } m := by
  have hcp := (hc.synced k).1
  have hpc := (hc.synced k).2
  cases h
  case downgrade_from_M_rq1 v j hj =>
    have hv : v = m := by
      apply hl.release k v
      rw [← hcp]; exact List.mem_of_getElem? hj
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      apply hl.grantM k v'
      rw [← hpc]; exact Or.inl hmem
    · intro v' hmem
      apply hl.grantM k v'
      rw [← hpc]; exact Or.inr hmem
    · intro v' hmem
      apply hl.grantS k v'
      rw [← hpc]; exact hmem
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hl.release k v' hmem'
    · intro _; exact hv
  case downgrade_from_M_rq2 j hj =>
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      apply hl.grantM k v'
      rw [← hpc]; exact Or.inl hmem
    · intro v' hmem
      apply hl.grantM k v'
      rw [← hpc]; exact Or.inr hmem
    · intro v' hmem
      apply hl.grantS k v'
      rw [← hpc]; exact hmem
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hl.release k v' hmem'
    · intro h0
      refine hl.parent (lv_step_parent_aux2 ?_ ?_ h0)
      · exact congrArg (List.countP isGrantX) hpc
      · simp only [update_Fin_gss]
        rw [countP_eraseIdx_neg hj rfl, hcp]
  case upgrade_to_M_data_avilable_rq1 =>
    have hall : ∀ i, x.parent.shared_state i = Bstate.I := by assumption
    have hpv : x.parent.value = m := hl.parent (fun i => (hc.rowI i (hall i)).1)
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inl h)
      · have hv := PCEvent.rsM.inj (List.mem_singleton.1 h)
        rw [hv]; exact hpv
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inr h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantS k v' h
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hl.release k v' hmem'
    · intro _; exact hpv
  case upgrade_to_M_data_avilable_rq2 =>
    have hnoM : ∀ i, ¬ (x.parent.shared_state i = Bstate.M) := by assumption
    have hnoE : ∀ i, ¬ (x.parent.shared_state i = Bstate.E) := by assumption
    have hpv : x.parent.value = m := by
      refine hl.parent (fun i => ?_)
      cases hrow : x.parent.shared_state i
      all_goals first
        | exact absurd hrow (hnoM i)
        | exact absurd hrow (hnoE i)
        | exact (hc.rowS i hrow).2
        | exact (hc.rowI i hrow).1
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inl h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inr h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantS k v' h
      · have hv := PCEvent.rsS.inj (List.mem_singleton.1 h)
        rw [hv]; exact hpv
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hl.release k v' hmem'
    · intro _; exact hpv
  case upgrade_to_E =>
    have hall : ∀ i, x.parent.shared_state i = Bstate.I := by assumption
    have hpv : x.parent.value = m := hl.parent (fun i => (hc.rowI i (hall i)).1)
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inl h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inr h)
      · have hv := PCEvent.rsE.inj (List.mem_singleton.1 h)
        rw [hv]; exact hpv
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantS k v' h
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      have hmem' := List.mem_of_mem_eraseIdx hmem
      rw [hcp] at hmem'
      exact hl.release k v' hmem'
    · intro _; exact hpv
  all_goals
    refine lv_step_parent_aux1_aux1 hl ?_ ?_ ?_ ?_ ?_
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inl h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantM k v' (Or.inr h)
      · cases List.mem_singleton.1 h
    · intro v' hmem
      simp only [update_Fin_gss] at hmem
      rcases List.mem_append.1 hmem with h | h
      · rw [hpc] at h; exact hl.grantS k v' h
      · cases List.mem_singleton.1 h
    · intro v' hmem
      apply hl.release k v'
      rw [← hcp]; exact hmem
    · intro h0
      refine hl.parent (lv_step_parent_aux2 ?_ ?_ h0)
      · simp only [update_Fin_gss, List.countP_append, hpc]
        rfl
      · exact congrArg (List.countP isReleaseX) hcp

theorem lv_step {x y : MESIState n} {m : Value} {e : MESIInternalEvent n} (hc : cohInv x) (hl : LV x m)
    (h : mesi_step_internal x e y) : LV y m := by
  cases h with
  | cache c' k e' hc' => exact lv_step_cache hc hl hc'
  | parent_upd_queue p' e' k hp => exact lv_step_parent hc hl hp

theorem lv_step_ext_aux1 {x y : MESIState n} {m : Value} (hl : LV x m)
    (hs : ∀ k, (y.caches k).state = (x.caches k).state)
    (hv : ∀ k, (y.caches k).value = (x.caches k).value)
    (hcp : ∀ k, (y.caches k).queue_cp = (x.caches k).queue_cp)
    (hpc : ∀ k, (y.caches k).queue_pc = (x.caches k).queue_pc)
    (hp : y.parent.value = x.parent.value) : LV y m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hM; rw [hv]; rw [hs] at hM; exact h1 k hM
  · intro k hS; rw [hv]; exact h2 k ((hs k).symm.trans hS)
  · intro k v hmem; rw [hpc] at hmem; exact h3 k v hmem
  · intro k v hmem; rw [hpc] at hmem; exact h4 k v hmem
  · intro k v hmem; rw [hcp] at hmem; exact h5 k v hmem
  · intro hall; rw [hp]; apply h6; intro k
    have := hall k
    unfold mtok mtokC at this ⊢
    rw [hs, hcp, hpc] at this
    exact this

theorem lv_step_ext_aux2 {x : MESIState n} {m : Value} {k : Fin n} {c' : CacheState}
    (hl : LV x m) (hs : c'.state = (x.caches k).state) (hv : c'.value = (x.caches k).value)
    (hcp : c'.queue_cp = (x.caches k).queue_cp) (hpc : c'.queue_pc = (x.caches k).queue_pc) :
    LV { x with caches := update_Fin k c' x.caches,
                parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } m := by
  apply lv_step_ext_aux1 hl
  · intro k'
    by_cases hk : k' = k
    · subst hk; simp only [update_Fin_gss]; exact hs
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  · intro k'
    by_cases hk : k' = k
    · subst hk; simp only [update_Fin_gss]; exact hv
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  · intro k'
    by_cases hk : k' = k
    · subst hk; simp only [update_Fin_gss]; exact hcp
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  · intro k'
    by_cases hk : k' = k
    · subst hk; simp only [update_Fin_gss]; exact hpc
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  · rfl

theorem lv_step_ext {x y : MESIState n} {m : Value} {e : MSIExternalEvent n} (hc : cohInv x) (hl : LV x m)
    (h : mesi_step_external x e y) : ∃ m', LV y m' := by
  cases h with
  | cache ev c' k hc' =>
    cases hc' with
    | ld_rq => exact ⟨m, lv_step_ext_aux2 hl rfl rfl rfl rfl⟩
    | st_rq v => exact ⟨m, lv_step_ext_aux2 hl rfl rfl rfl rfl⟩
    | ld_rq_data_available1 rst hrq hS => exact ⟨m, lv_step_ext_aux2 hl rfl rfl rfl rfl⟩
    | ld_rq_data_available rst hrq hM => exact ⟨m, lv_step_ext_aux2 hl rfl rfl rfl rfl⟩
    | ld_rq_data_availableE rst hrq hE => exact ⟨m, lv_step_ext_aux2 hl rfl rfl rfl rfl⟩
    | st_rq_M_state v rst hrq hM =>
      -- la cache `k` è in `M`: la sua riga è `M` (o `E`), ha un solo token esclusivo, nessun
      -- token `S`, e tutte le altre cache non hanno token
      have hpos : mtok x k ≠ 0 := by
        unfold mtok mtokC; rw [if_pos (Or.inl hM)]; omega
      have hrow : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E := by
        have hr : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.I
            ∨ x.parent.shared_state k = Bstate.S ∨ x.parent.shared_state k = Bstate.E := by
          cases x.parent.shared_state k <;> simp
        rcases hr with hr | hr | hr | hr
        · exact Or.inl hr
        · exact absurd (hc.rowI k hr).1 hpos
        · exact absurd (hc.rowS k hr).2 hpos
        · exact Or.inr hr
      obtain ⟨hm1, hs0⟩ := hc.rowM k hrow
      have hother : ∀ k', k' ≠ k → mtok x k' = 0 ∧ stok x k' = 0 :=
        fun k' hne => hc.rowI k' (hc.excl k k' hrow hne)
      have hcnt : (x.caches k).queue_pc.countP isGrantX = 0 ∧
          (x.caches k).queue_cp.countP isReleaseX = 0 := by
        unfold mtok mtokC at hm1; rw [if_pos (Or.inl hM)] at hm1; omega
      refine ⟨v, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k' hM'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]
        · exfalso
          simp only [update_Fin_gso2 _ _ _ _ hk] at hM'
          exact (mtok_zero_facts (hother k' hk).1).1 hM'
      · intro k' hS'
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hS'
          rw [hM] at hS'
          cases hS'
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hS'
          exact (stok_zero_facts (hother k' hk).2).1 hS'
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          rcases hmem with hmem | hmem
          · exact List.countP_eq_zero.1 hcnt.1 _ hmem rfl
          · exact List.countP_eq_zero.1 hcnt.1 _ hmem rfl
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          rcases hmem with hmem | hmem
          · exact ((mtok_zero_facts (hother k' hk).1).2.1 w).1 hmem
          · exact ((mtok_zero_facts (hother k' hk).1).2.1 w).2 hmem
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          exact (stok_zero_facts hs0).2.1 w hmem
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          exact (stok_zero_facts (hother k' hk).2).2.1 w hmem
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          exact List.countP_eq_zero.1 hcnt.2 _ hmem rfl
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          exact (mtok_zero_facts (hother k' hk).1).2.2 w hmem
      · intro hall
        exfalso
        have := hall k
        unfold mtok mtokC at this
        simp [update_Fin_gss, hM] at this

theorem coh_lv_trans {x y : MESIState n} {m : Value} (hc : cohInv x) (hl : LV x m)
    (h : trans_refl (mesi_rule n) x y) : cohInv y ∧ LV y m := by
  revert hc hl
  induction h with
  | refl => exact fun hc hl => ⟨hc, hl⟩
  | step hab _ ih =>
    intro hc hl
    obtain ⟨e, he⟩ := hab
    exact ih (coh_step hc he) (lv_step hc hl he)

/-- Ogni stato raggiungibile soddisfa `cohInv` e ha un valore logico. -/
theorem reach_inv {x : MESIState n} (h : Reach x) : cohInv x ∧ ∃ m, LV x m := by
  unfold Reach ReachingStar.reachable at h
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact ⟨coh_default, 0, lv_default⟩
  | step_int l s' s'' _ hstep ih =>
    obtain ⟨hc, m, hlv⟩ := ih
    obtain ⟨hc', hlv'⟩ := coh_lv_trans hc hlv hstep
    exact ⟨hc', m, hlv'⟩
  | step_ext l s' s'' e _ hstep ih =>
    obtain ⟨hc, m, hlv⟩ := ih
    exact ⟨coh_step_ext hc hstep, lv_step_ext hc hlv hstep⟩

/-! ### Lo stato canonico è invariante lungo i passi interni -/

/-! ### Le `extqueue` non cambiano con i passi interni; lo stato canonico è invariante -/

/-- Nessun passo interno tocca le `extqueue`: la load servita in `M` è ora un passo esterno. -/
theorem ext_step {x y : MESIState n} {e : MESIInternalEvent n} (h : mesi_step_internal x e y) :
    ∀ k, (y.caches k).extqueue = (x.caches k).extqueue := by
  intro k'
  cases h with
  | cache c' k e' hc' =>
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
      cases hc' <;> rfl
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | parent_upd_queue p' e' k hp =>
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
    · simp only [update_Fin_gso2 _ _ _ _ hk]

theorem ext_trans {x y : MESIState n} (h : trans_refl (mesi_rule n) x y) :
    ∀ k, (y.caches k).extqueue = (x.caches k).extqueue := by
  induction h with
  | refl => intro k; rfl
  | step hab _ ih =>
    intro k
    obtain ⟨e, he⟩ := hab
    rw [ih k, ext_step he k]

/-- Lo stato canonico dipende solo dalle `extqueue`, che i passi interni non cambiano. -/
theorem canon_trans {x y : MESIState n} {m : Value} (h : trans_refl (mesi_rule n) x y) :
    canon y m = canon x m := by
  unfold canon
  congr 1
  funext k
  rw [ext_trans h k]

/-! ### Verso lo stato canonico -/

/-- Versione generale di `predrain_aux1`: la riga `k` è `M` oppure `E`. -/
theorem predrain_aux1_aux1 {x y : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E)
    (hyk : mtokC (y.caches k) = 0)
    (hoth : ∀ k', k' ≠ k → y.caches k' = x.caches k') : ∀ k', mtok y k' = 0 := by
  intro k'
  by_cases hkk : k' = k
  · rw [hkk]; exact hyk
  · have hI := hc.excl k k' hk hkk
    have h0 := (hc.rowI k' hI).1
    unfold mtok at h0 ⊢
    rw [hoth k' hkk]
    exact h0

/-- Se la cache `k` (riga `M`) è rimasta senza token `M` e le altre cache non sono cambiate,
nessun token `M` è in giro: le altre righe erano `I` (`excl`). -/
theorem predrain_aux1 {x y : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M) (hyk : mtokC (y.caches k) = 0)
    (hoth : ∀ k', k' ≠ k → y.caches k' = x.caches k') : ∀ k', mtok y k' = 0 := by
  exact predrain_aux1_aux1 hc (Or.inl hk) hyk hoth

/-- Caso A: la cache `k` è in `M`; rilascia e il parent prende il rilascio. -/
theorem predrain_aux2 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M) (hM : (x.caches k).state = Bstate.M)
    (hg : (x.caches k).queue_pc.countP isGrantX = 0)
    (hr : (x.caches k).queue_cp.countP isReleaseX = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have hs := hc.synced
  -- Passo 1: la cache `k` rilascia spontaneamente.
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, mesi_rule n x x1
        ∧ synced x1
        ∧ (x1.caches k).state = Bstate.I
        ∧ (x1.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp ++ [CPEvent.rsIμ (x.caches k).value]
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    have hstep := mesi_step_internal.cache x _ k _
      (cache_mesi_step_internal.rq_data_not_available (x.caches k) hM)
    refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: il parent prende il rilascio.
  obtain ⟨x2, step2, h2state, h2pc, h2cp, h2oth⟩ :
      ∃ x2, mesi_rule n x1 x2
        ∧ (x2.caches k).state = Bstate.I
        ∧ (x2.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    have hg6 : (x1.parent.queue_cip k)[(x.caches k).queue_cp.length]?
        = some (CPEvent.rsIμ (x.caches k).value) := by
      rw [(h1s k).1, h1cp]; exact List.getElem?_concat_length
    have hstep := mesi_step_internal.parent_upd_queue x1 _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x1.parent (x.caches k).value k _ hg6)
    refine ⟨_, mesi_rule_of_step hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h1state
    · simp only [update_Fin_gss]; rw [(h1s k).2, h1pc]
    · simp only [update_Fin_gss]; rw [(h1s k).1, h1cp]; exact eraseIdx_concat _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  refine ⟨x2, trans_refl.step step1 (trans_refl.step step2 trans_refl.refl), ?_⟩
  refine predrain_aux1 hc hk ?_ h2oth
  unfold mtokC
  rw [h2state, h2pc, h2cp, hg, hr]
  simp

/-- Versione generale del caso B: riga `M` o `E`, grant `rsM v` o `rsE v` in volo verso `k`
(cache in `I`); la cache lo prende (passando a `M` o a `E`), rilascia e il parent prende il
rilascio. -/
theorem predrain_aux3_aux1 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E)
    (hnME : ¬((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E))
    {v : Value}
    (hv : PCEvent.rsM v ∈ (x.caches k).queue_pc ∨ PCEvent.rsE v ∈ (x.caches k).queue_pc)
    (hr : (x.caches k).queue_cp.countP isReleaseX = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have hs := hc.synced
  have ⟨h1, h0S⟩ := hc.rowM k hk
  have hnS := (stok_zero_facts h0S).1
  have hI : (x.caches k).state = Bstate.I := by
    cases hst : (x.caches k).state with
    | M => exact absurd (Or.inl hst) hnME
    | E => exact absurd (Or.inr hst) hnME
    | S => exact absurd hst hnS
    | I => rfl
  have hg1 : (x.caches k).queue_pc.countP isGrantX = 1 := by
    have h1' := h1
    unfold mtok mtokC at h1'
    rw [if_neg hnME, hr] at h1'
    omega
  -- Passo 1: la cache `k` prende il grant (`rsM` o `rsE`), passando a `M` o a `E`.
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1val, h1oth⟩ :
      ∃ x1, mesi_rule n x x1
        ∧ synced x1
        ∧ ((x1.caches k).state = Bstate.M ∨ (x1.caches k).state = Bstate.E)
        ∧ (x1.caches k).queue_pc.countP isGrantX = 0
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp
        ∧ (x1.caches k).value = v
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    rcases hv with hv | hv
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
      have hgE : ((x.caches k).queue_pc.eraseIdx j).countP isGrantX = 0 := by
        have := countP_eraseIdx_pos (p := isGrantX) hj rfl
        omega
      have hstep := mesi_step_internal.cache x _ k _
        (cache_mesi_step_internal.upgrade_from_I_rs (x.caches k) v j hj hI)
      refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_, ?_⟩
      · exact Or.inl (by simp only [update_Fin_gss])
      · simp only [update_Fin_gss]; exact hgE
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
      have hgE : ((x.caches k).queue_pc.eraseIdx j).countP isGrantX = 0 := by
        have := countP_eraseIdx_pos (p := isGrantX) hj rfl
        omega
      have hstep := mesi_step_internal.cache x _ k _
        (cache_mesi_step_internal.upgrade_from_I_rsE (x.caches k) v j hj hI)
      refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_, ?_⟩
      · exact Or.inr (by simp only [update_Fin_gss])
      · simp only [update_Fin_gss]; exact hgE
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: la cache `k` rilascia spontaneamente (da `M` o da `E`).
  obtain ⟨x2, step2, h2s, h2state, h2pc, h2cp, h2oth⟩ :
      ∃ x2, mesi_rule n x1 x2
        ∧ synced x2
        ∧ (x2.caches k).state = Bstate.I
        ∧ (x2.caches k).queue_pc = (x1.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp ++ [CPEvent.rsIμ v]
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    rcases h1state with h1state | h1state
    · have hstep := mesi_step_internal.cache x1 _ k _
        (cache_mesi_step_internal.rq_data_not_available (x1.caches k) h1state)
      refine ⟨_, mesi_rule_of_step hstep, synced_step h1s hstep, ?_, ?_, ?_, ?_⟩
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]; rw [h1cp, h1val]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
    · have hstep := mesi_step_internal.cache x1 _ k _
        (cache_mesi_step_internal.rq_data_not_availableE (x1.caches k) h1state)
      refine ⟨_, mesi_rule_of_step hstep, synced_step h1s hstep, ?_, ?_, ?_, ?_⟩
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]; rw [h1cp, h1val]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  -- Passo 3: il parent prende il rilascio.
  obtain ⟨x3, step3, h3state, h3pc, h3cp, h3oth⟩ :
      ∃ x3, mesi_rule n x2 x3
        ∧ (x3.caches k).state = Bstate.I
        ∧ (x3.caches k).queue_pc = (x1.caches k).queue_pc
        ∧ (x3.caches k).queue_cp = (x.caches k).queue_cp
        ∧ (∀ k', k' ≠ k → x3.caches k' = x.caches k') := by
    have hg6 : (x2.parent.queue_cip k)[(x.caches k).queue_cp.length]?
        = some (CPEvent.rsIμ v) := by
      rw [(h2s k).1, h2cp]; exact List.getElem?_concat_length
    have hstep := mesi_step_internal.parent_upd_queue x2 _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x2.parent v k _ hg6)
    refine ⟨_, mesi_rule_of_step hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h2state
    · simp only [update_Fin_gss]; rw [(h2s k).2, h2pc]
    · simp only [update_Fin_gss]; rw [(h2s k).1, h2cp]; exact eraseIdx_concat _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h2oth k' hk
  refine ⟨x3, trans_refl.step step1 (trans_refl.step step2
    (trans_refl.step step3 trans_refl.refl)), ?_⟩
  refine predrain_aux1_aux1 hc hk ?_ h3oth
  unfold mtokC
  rw [h3state, h3pc, h1pc, h3cp, hr]
  simp

/-- Caso B: un grant `rsM v` in volo verso `k` (cache in `I`); la cache lo prende, rilascia e il
parent prende il rilascio. -/
theorem predrain_aux3 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M) (hnM : (x.caches k).state ≠ Bstate.M)
    {v : Value} (hv : PCEvent.rsM v ∈ (x.caches k).queue_pc)
    (hr : (x.caches k).queue_cp.countP isReleaseX = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have ⟨h1, _⟩ := hc.rowM k (Or.inl hk)
  -- la cache non è in `E`: con un grant in volo il token `M` sarebbe doppio
  have hnE : (x.caches k).state ≠ Bstate.E := by
    intro hE
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
    have := countP_eraseIdx_pos (p := isGrantX) hj rfl
    unfold mtok mtokC at h1
    rw [if_pos (Or.inr hE), hr] at h1
    omega
  exact predrain_aux3_aux1 hc (Or.inl hk) (fun h => h.elim hnM hnE) (Or.inl hv) hr

/-- Versione generale del caso C: riga `M` o `E`, un rilascio `rsIμ v` in volo da `k`; il parent
lo prende. -/
theorem predrain_aux4_aux1 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E)
    (hnME : ¬((x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E))
    (hg : (x.caches k).queue_pc.countP isGrantX = 0)
    {v : Value} (hv : CPEvent.rsIμ v ∈ (x.caches k).queue_cp) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have hs := hc.synced
  have ⟨h1, _⟩ := hc.rowM k hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have hr1 : (x.caches k).queue_cp.countP isReleaseX = 1 := by
    have h1' := h1
    unfold mtok mtokC at h1'
    rw [if_neg hnME, hg] at h1'
    omega
  have hrE : ((x.caches k).queue_cp.eraseIdx j).countP isReleaseX = 0 := by
    have := countP_eraseIdx_pos (p := isReleaseX) hj rfl
    omega
  have hj' : (x.parent.queue_cip k)[j]? = some (CPEvent.rsIμ v) := by
    rw [(hs k).1]; exact hj
  -- Un solo passo: il parent prende il rilascio.
  obtain ⟨x1, step1, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, mesi_rule n x x1
        ∧ (x1.caches k).state = (x.caches k).state
        ∧ (x1.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp.eraseIdx j
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    have hstep := mesi_step_internal.parent_upd_queue x _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x.parent v k j hj')
    refine ⟨_, mesi_rule_of_step hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; rw [(hs k).2]
    · simp only [update_Fin_gss]; rw [(hs k).1]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  refine ⟨x1, trans_refl.step step1 trans_refl.refl, ?_⟩
  refine predrain_aux1_aux1 hc hk ?_ h1oth
  unfold mtokC
  rw [h1state, if_neg hnME, h1pc, h1cp, hg, hrE]

/-- Caso C: un rilascio `rsIμ v` in volo da `k`; il parent lo prende. -/
theorem predrain_aux4 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M) (hnM : (x.caches k).state ≠ Bstate.M)
    (hg : (x.caches k).queue_pc.countP isGrantX = 0)
    {v : Value} (hv : CPEvent.rsIμ v ∈ (x.caches k).queue_cp) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have ⟨h1, _⟩ := hc.rowM k (Or.inl hk)
  -- la cache non è in `E`: con un rilascio in volo il token `M` sarebbe doppio
  have hnE : (x.caches k).state ≠ Bstate.E := by
    intro hE
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
    have := countP_eraseIdx_pos (p := isReleaseX) hj rfl
    unfold mtok mtokC at h1
    rw [if_pos (Or.inr hE), hg] at h1
    omega
  exact predrain_aux4_aux1 hc (Or.inl hk) (fun h => h.elim hnM hnE) hg hv

/-- Versione generale del caso A (`predrain_aux2`): riga `M` o `E`, cache `k` in `M` o in `E`;
rilascia (`rq_data_not_available` / `rq_data_not_availableE`) e il parent prende il rilascio. -/
theorem predrain_aux5 {x : MESIState n} {k : Fin n} (hc : cohInv x)
    (hk : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E)
    (hME : (x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.E)
    (hg : (x.caches k).queue_pc.countP isGrantX = 0)
    (hr : (x.caches k).queue_cp.countP isReleaseX = 0) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  have hs := hc.synced
  -- Passo 1: la cache `k` rilascia spontaneamente (da `M` o da `E`).
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, mesi_rule n x x1
        ∧ synced x1
        ∧ (x1.caches k).state = Bstate.I
        ∧ (x1.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp ++ [CPEvent.rsIμ (x.caches k).value]
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    rcases hME with hM | hE
    · have hstep := mesi_step_internal.cache x _ k _
        (cache_mesi_step_internal.rq_data_not_available (x.caches k) hM)
      refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
    · have hstep := mesi_step_internal.cache x _ k _
        (cache_mesi_step_internal.rq_data_not_availableE (x.caches k) hE)
      refine ⟨_, mesi_rule_of_step hstep, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · simp only [update_Fin_gss]
      · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: il parent prende il rilascio.
  obtain ⟨x2, step2, h2state, h2pc, h2cp, h2oth⟩ :
      ∃ x2, mesi_rule n x1 x2
        ∧ (x2.caches k).state = Bstate.I
        ∧ (x2.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    have hg6 : (x1.parent.queue_cip k)[(x.caches k).queue_cp.length]?
        = some (CPEvent.rsIμ (x.caches k).value) := by
      rw [(h1s k).1, h1cp]; exact List.getElem?_concat_length
    have hstep := mesi_step_internal.parent_upd_queue x1 _ _ k
      (parent_mesi_step.downgrade_from_M_rq1 x1.parent (x.caches k).value k _ hg6)
    refine ⟨_, mesi_rule_of_step hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h1state
    · simp only [update_Fin_gss]; rw [(h1s k).2, h1pc]
    · simp only [update_Fin_gss]; rw [(h1s k).1, h1cp]; exact eraseIdx_concat _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  refine ⟨x2, trans_refl.step step1 (trans_refl.step step2 trans_refl.refl), ?_⟩
  refine predrain_aux1_aux1 hc hk ?_ h2oth
  unfold mtokC
  rw [h2state, h2pc, h2cp, hg, hr]
  simp

/-- Si completa il ciclo dell'eventuale token `M` in giro: alla fine nessun token `M`. -/
theorem predrain {x : MESIState n} {m : Value} (hc : cohInv x) (_hl : LV x m) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ ∀ k, mtok y k = 0 := by
  by_cases hex : ∃ k, x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E
  · obtain ⟨k, hk⟩ := hex
    have ⟨h1, _⟩ := hc.rowM k hk
    rcases mtok_one_cases h1 with ⟨hME, hg, hr⟩ | ⟨hnME, ⟨v, hv⟩, hr⟩ | ⟨hnME, hg, ⟨v, hv⟩⟩
    · exact predrain_aux5 hc hk hME hg hr
    · exact predrain_aux3_aux1 hc hk hnME hv hr
    · exact predrain_aux4_aux1 hc hk hnME hg hv
  · simp only [not_exists, not_or] at hex
    refine ⟨x, trans_refl.refl, fun k => ?_⟩
    cases hrow : x.parent.shared_state k with
    | M => exact absurd hrow (hex k).1
    | E => exact absurd hrow (hex k).2
    | I => exact (hc.rowI k hrow).1
    | S => exact (hc.rowS k hrow).2

/-- Senza token `M` in giro, `cohInv` e `LV m` danno `flushInv` rispetto a uno spec con memoria `m`. -/
theorem flushInv_of_lv {x : MESIState n} {m : Value} (hc : cohInv x) (hl : LV x m)
    (h0 : ∀ k, mtok x k = 0) : flushInv x ⟨m, fun _ => default⟩ := by
  refine ⟨hc.synced, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowM: nessuna riga può essere `M` o `E` senza token `M`
    intro k hrow
    have h1 := (hc.rowM k hrow).1
    rw [h0 k] at h1
    omega
  · -- rowS
    intro k hrow
    exact tokenS_of_stok_pos (by rw [(hc.rowS k hrow).1]; exact Nat.one_pos)
  · -- value
    exact hl.parent h0
  · -- cacheVal
    intro k hne
    cases hst : (x.caches k).state with
    | M => exact absurd (Or.inl hst) (mtok_zero_facts (h0 k)).1
    | E => exact absurd (Or.inr hst) (mtok_zero_facts (h0 k)).1
    | I => exact absurd hst hne
    | S => exact hl.cacheS k hst
  · -- grantVal
    intro k v hmem
    rcases hmem with h | h | h
    · exact absurd h ((mtok_zero_facts (h0 k)).2.1 v).1
    · exact hl.grantS k v h
    · exact absurd h ((mtok_zero_facts (h0 k)).2.1 v).2
  · -- releaseVal
    intro k v h
    exact absurd h ((mtok_zero_facts (h0 k)).2.2 v)

/-- Da uno stato flushed la cache `k` porta il suo valore a `s.memory`: `rqM`, grant, presa,
rilascio, presa del rilascio; `extqueue` e le altre cache non cambiano. -/
theorem fix_step {x : MESIState n} {s : SeqState n} {k : Fin n} (hf : flush0 x s)
    (hk : (x.caches k).value ≠ s.memory) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ flush0 y s ∧ (y.caches k).value = s.memory
      ∧ (y.caches k).extqueue = (x.caches k).extqueue
      ∧ ∀ k', k' ≠ k → y.caches k' = x.caches k' := by
  obtain ⟨hc, hp, hv⟩ := hf
  obtain ⟨hkI, hcp, hpc⟩ := hc k
  refine ⟨_, trans_refl.step
    (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.upgrade_from_I_rq _ hkI)))
    (trans_refl.step
      (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
        (parent_mesi_step.upgrade_to_M_data_avilable_rq1 _ k 0 ?h1 ?h2)))
      (trans_refl.step
        (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
          (cache_mesi_step_internal.upgrade_from_I_rs _ x.parent.value 0 ?h3 ?h4)))
        (trans_refl.step
          (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
            (cache_mesi_step_internal.rq_data_not_available _ ?h5)))
          (trans_refl.step
            (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
              (parent_mesi_step.downgrade_from_M_rq1 _ x.parent.value k 0 ?h6)))
            trans_refl.refl)))), ?_, ?_, ?_, ?_⟩
  case h1 => simp [update_Fin_gss, hcp]
  case h2 => intro j; simpa using (hp j).1
  case h3 => simp [update_Fin_gss, hpc]
  case h4 => simp [update_Fin_gss, hkI]
  case h5 => simp [update_Fin_gss]
  case h6 => simp [update_Fin_gss, hcp, hpc]
  · constructor
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hkI, hcp, hpc]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hc k']
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hcp, hpc]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hp k']
    · simpa using hv
  · simp [update_Fin_gss, hv]
  · simp [update_Fin_gss]
  · intro k' hkk
    simp [update_Fin_gso2 _ _ _ _ hkk]

theorem fix_all {x : MESIState n} {s : SeqState n} (hf : flush0 x s) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ flush0 y s ∧ (∀ k, (y.caches k).value = s.memory)
      ∧ ∀ k, (y.caches k).extqueue = (x.caches k).extqueue := by
  suffices H : ∀ N, ∀ x : MESIState n, flush0 x s → μ4 x s.memory ≤ N →
      ∃ y, trans_refl (mesi_rule n) x y ∧ flush0 y s ∧ (∀ k, (y.caches k).value = s.memory)
        ∧ ∀ k, (y.caches k).extqueue = (x.caches k).extqueue from
    H _ x hf le_rfl
  intro N
  induction N with
  | zero =>
    intro x hf hN
    have h0 : Finset.univ.sum (fun k => if (x.caches k).value = s.memory then 0 else 1) = 0 :=
      Nat.le_zero.mp hN
    refine ⟨x, trans_refl.refl, hf, ?_, fun _ => rfl⟩
    intro k
    have hk : (if (x.caches k).value = s.memory then 0 else 1) = 0 :=
      sum_eq_zero_iff_pointwise.mp h0 k
    by_contra hne
    simp [hne] at hk
  | succ N ih =>
    intro x hf hN
    by_cases h0 : μ4 x s.memory = 0
    · have h0' : Finset.univ.sum (fun k => if (x.caches k).value = s.memory then 0 else 1) = 0 := h0
      refine ⟨x, trans_refl.refl, hf, ?_, fun _ => rfl⟩
      intro k
      have hk : (if (x.caches k).value = s.memory then 0 else 1) = 0 :=
        sum_eq_zero_iff_pointwise.mp h0' k
      by_contra hne
      simp [hne] at hk
    · have hpos : 0 < μ4 x s.memory := Nat.pos_of_ne_zero h0
      unfold μ4 at hpos
      obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
      have hk2 : 0 < (if (x.caches k).value = s.memory then 0 else 1) := hk
      have hne : (x.caches k).value ≠ s.memory := by
        intro heq
        simp [heq] at hk2
      obtain ⟨y1, hxy1, hf1, hval1, hext1, hoth1⟩ := fix_step hf hne
      have hlt : μ4 y1 s.memory < μ4 x s.memory := by
        unfold μ4
        refine sum_lt_of_pointwise ?_ k ?_
        · intro k'
          show (if (y1.caches k').value = s.memory then 0 else 1)
            ≤ (if (x.caches k').value = s.memory then 0 else 1)
          by_cases hk' : k' = k
          · subst hk'
            simp [hval1]
          · rw [hoth1 k' hk']
        · show (if (y1.caches k).value = s.memory then 0 else 1)
            < (if (x.caches k).value = s.memory then 0 else 1)
          simp [hval1, hne]
      obtain ⟨y, hy1y, hfy, hval, hext⟩ := ih y1 hf1 (by omega)
      refine ⟨y, phase2_aux1 hxy1 hy1y, hfy, hval, ?_⟩
      intro k'
      rw [hext k']
      by_cases hk' : k' = k
      · subst hk'
        exact hext1
      · rw [hoth1 k' hk']

/-- Uno stato flushed (`flush0`) con tutti i valori a `s.memory` è canonico. -/
theorem canon_of_flush {x : MESIState n} {s : SeqState n} (hf : flush0 x s)
    (hv : ∀ k, (x.caches k).value = s.memory) : x = canon x s.memory := by
  obtain ⟨hcI, hp, hpv⟩ := hf
  have hcaches : x.caches
      = fun k => ⟨Bstate.I, s.memory, [], [], (x.caches k).extqueue⟩ := by
    funext k
    obtain ⟨h1, h2, h3⟩ := hcI k
    have h4 := hv k
    cases hck : x.caches k with
    | mk st v cp pc ext =>
      simp only [hck] at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
  have hparent : x.parent = ⟨s.memory, fun _ => Bstate.I, fun _ => [], fun _ => []⟩ := by
    cases hpp : x.parent with
    | mk pv rows cip pci =>
      simp only [hpp] at hpv hp
      have e1 : rows = fun _ => Bstate.I := funext fun k => (hp k).1
      have e2 : cip = fun _ => [] := funext fun k => (hp k).2.1
      have e3 : pci = fun _ => [] := funext fun k => (hp k).2.2
      subst hpv e1 e2 e3
      rfl
  have h : (⟨x.caches, x.parent⟩ : MESIState n) = canon x s.memory := by
    unfold canon
    rw [hparent]
    congr 1
  exact h

/-- Da ogni stato con `cohInv` e valore logico `m` si raggiunge `canon x m` con passi interni:
`predrain`, `flushInv_of_lv`, le tre fasi, `fix_all`, `canon_of_flush`, `canon_trans`. -/
theorem reach_canon {x : MESIState n} {m : Value} (hc : cohInv x) (hl : LV x m) :
    trans_refl (mesi_rule n) x (canon x m) := by
  obtain ⟨y, hxy, h0⟩ := predrain hc hl
  obtain ⟨hcy, hly⟩ := coh_lv_trans hc hl hxy
  have hI := flushInv_of_lv hcy hly h0
  obtain ⟨y1, h1, hI1, hq1⟩ := phase1 hI
  obtain ⟨y2, h2, hI2, hq1', hq2⟩ := phase2 hI1 hq1
  obtain ⟨y3, h3, hI3, a, b, c⟩ := phase3 hI2 hq1' hq2
  have hf3 : flush0 y3 ⟨m, fun _ => default⟩ := flush_of_quiet hI3 a b c
  obtain ⟨y5, h5, hf5, hval, _⟩ := fix_all hf3
  have heq : y5 = canon y5 m := canon_of_flush hf5 hval
  have hpath : trans_refl (mesi_rule n) x y5 :=
    phase2_aux1 hxy (phase2_aux1 h1 (phase2_aux1 h2 (phase2_aux1 h3 h5)))
  have hcanon : canon y5 m = canon x m := canon_trans hpath
  rw [← hcanon, ← heq]
  exact hpath

/-- **Confluenza dei passi interni sugli stati raggiungibili**: l'ipotesi (4) di
`ReachingStar.trace_inclusion` per MSI. -/
theorem mesi_confluent :
    ReachingStar.has_diamond_property_on
      (fun i' => ReachingStar.reachable (mesi_rule n) mesi_step_external i' (default : MESIState n))
      (trans_refl (mesi_rule n)) := by
  unfold ReachingStar.has_diamond_property_on
  intro a b c hR hac hab
  obtain ⟨hc, m, hl⟩ := reach_inv (show Reach a from hR)
  refine ⟨canon a m, ?_, ?_⟩
  · have hcl := coh_lv_trans hc hl hac
    have := reach_canon hcl.1 hcl.2
    rw [canon_trans hac] at this
    exact this
  · have hcl := coh_lv_trans hc hl hab
    have := reach_canon hcl.1 hcl.2
    rw [canon_trans hab] at this
    exact this

/-! ### Verso `trace_inclusion`: le relazioni con lo spec e la commutazione a meno di passi interni -/

/-- Uno stato flushed (`flush0`) soddisfa `cohInv`: nessun token, righe a `I`. -/
theorem coh_of_flush0 {x : MESIState n} {s : SeqState n} (hf : flush0 x s) : cohInv x := by
  obtain ⟨hc, hp, hv⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨by rw [(hp k).2.1, (hc k).2.1], by rw [(hp k).2.2, (hc k).2.2]⟩
  · intro k h
    rw [(hp k).1] at h
    rcases h with h | h <;> cases h
  · intro k h
    rw [(hp k).1] at h
    cases h
  · intro k _
    unfold mtok mtokC stok stokC
    rw [(hc k).1, (hc k).2.1, (hc k).2.2]
    simp
  · intro k k' h
    rw [(hp k).1] at h
    rcases h with h | h <;> cases h

/-- Uno stato flushed (`flush0`) ha valore logico `s.memory`. -/
theorem lv_of_flush0 {x : MESIState n} {s : SeqState n} (hf : flush0 x s) : LV x s.memory := by
  obtain ⟨hc, hp, hv⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h
    rw [(hc k).1] at h
    rcases h with h | h <;> cases h
  · intro k h
    rw [(hc k).1] at h
    cases h
  · intro k v h
    rw [(hc k).2.2] at h
    simp at h
  · intro k v h
    rw [(hc k).2.2] at h
    simp at h
  · intro k v h
    rw [(hc k).2.1] at h
    simp at h
  · intro _
    exact hv

/-- Lo stato canonico è flushed rispetto a uno spec con memoria `m` e le stesse `extqueue`. -/
theorem flush_canon {x : MESIState n} {m : Value} {s : SeqState n} (hm : s.memory = m)
    (hext : ∀ k, (x.caches k).extqueue = s.extqueue k) : flush (canon x m) s := by
  unfold flush
  refine ⟨?_, fun k => hext k⟩
  constructor
  · intro k
    exact ⟨rfl, rfl, rfl⟩
  · intro k
    exact ⟨rfl, rfl, rfl⟩
  · exact hm.symm

/-- Il valore logico dopo un passo esterno: `st_rs` lo cambia nel valore scritto dalla cache, gli
altri eventi (richieste, `ld_rs`) lo lasciano. -/
theorem lv_step_ext_val {x y : MESIState n} {m : Value} {e : Event} {k : Fin n} (hc : cohInv x)
    (hl : LV x m) (h : mesi_step_external x (.cache e k) y) :
    (e ≠ Event.st_rs → LV y m) ∧ (e = Event.st_rs → LV y (y.caches k).value) := by
  cases h
  rename_i c' hc'
  · cases hc' with
    | ld_rq =>
      exact ⟨fun _ => lv_step_ext_aux2 hl rfl rfl rfl rfl, fun heq => by cases heq⟩
    | st_rq v =>
      exact ⟨fun _ => lv_step_ext_aux2 hl rfl rfl rfl rfl, fun heq => by cases heq⟩
    | ld_rq_data_available1 rst hrq hS =>
      exact ⟨fun _ => lv_step_ext_aux2 hl rfl rfl rfl rfl, fun heq => by cases heq⟩
    | ld_rq_data_available rst hrq hM =>
      exact ⟨fun _ => lv_step_ext_aux2 hl rfl rfl rfl rfl, fun heq => by cases heq⟩
    | ld_rq_data_availableE rst hrq hE =>
      exact ⟨fun _ => lv_step_ext_aux2 hl rfl rfl rfl rfl, fun heq => by cases heq⟩
    | st_rq_M_state v rst hrq hM =>
      refine ⟨fun hne => absurd rfl hne, fun _ => ?_⟩
      simp only [update_Fin_gss]
      -- la cache `k` è in `M`: la sua riga è `M` (o `E`), ha un solo token esclusivo, nessun
      -- token `S`, e tutte le altre cache non hanno token
      have hpos : mtok x k ≠ 0 := by
        unfold mtok mtokC; rw [if_pos (Or.inl hM)]; omega
      have hrow : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.E := by
        have hr : x.parent.shared_state k = Bstate.M ∨ x.parent.shared_state k = Bstate.I
            ∨ x.parent.shared_state k = Bstate.S ∨ x.parent.shared_state k = Bstate.E := by
          cases x.parent.shared_state k <;> simp
        rcases hr with hr | hr | hr | hr
        · exact Or.inl hr
        · exact absurd (hc.rowI k hr).1 hpos
        · exact absurd (hc.rowS k hr).2 hpos
        · exact Or.inr hr
      obtain ⟨hm1, hs0⟩ := hc.rowM k hrow
      have hother : ∀ k', k' ≠ k → mtok x k' = 0 ∧ stok x k' = 0 :=
        fun k' hne => hc.rowI k' (hc.excl k k' hrow hne)
      have hcnt : (x.caches k).queue_pc.countP isGrantX = 0 ∧
          (x.caches k).queue_cp.countP isReleaseX = 0 := by
        unfold mtok mtokC at hm1; rw [if_pos (Or.inl hM)] at hm1; omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k' hM'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]
        · exfalso
          simp only [update_Fin_gso2 _ _ _ _ hk] at hM'
          exact (mtok_zero_facts (hother k' hk).1).1 hM'
      · intro k' hS'
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hS'
          rw [hM] at hS'
          cases hS'
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hS'
          exact (stok_zero_facts (hother k' hk).2).1 hS'
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          rcases hmem with hmem | hmem
          · exact List.countP_eq_zero.1 hcnt.1 _ hmem rfl
          · exact List.countP_eq_zero.1 hcnt.1 _ hmem rfl
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          rcases hmem with hmem | hmem
          · exact ((mtok_zero_facts (hother k' hk).1).2.1 w).1 hmem
          · exact ((mtok_zero_facts (hother k' hk).1).2.1 w).2 hmem
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          exact (stok_zero_facts hs0).2.1 w hmem
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          exact (stok_zero_facts (hother k' hk).2).2.1 w hmem
      · intro k' w hmem
        exfalso
        by_cases hk : k' = k
        · subst hk
          simp only [update_Fin_gss] at hmem
          exact List.countP_eq_zero.1 hcnt.2 _ hmem rfl
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
          exact (mtok_zero_facts (hother k' hk).1).2.2 w hmem
      · intro hall
        exfalso
        have := hall k
        unfold mtok mtokC at this
        simp [update_Fin_gss, hM] at this

/-- Lo stesso evento indicizzato aggiorna allo stesso modo le `extqueue` di implementazione e spec. -/
theorem ext_step_ext {i' i'' : MESIState n} {s s' : SeqState n} {e : Event} {k : Fin n}
    (hext : ∀ k, (i'.caches k).extqueue = s.extqueue k) (h : mesi_step_external i' (.cache e k) i'')
    (hs : seq_step s (.cache e k) s') : ∀ k', (i''.caches k').extqueue = s'.extqueue k' := by
  intro k'
  cases h with
  | cache _ c' _ hc' =>
    by_cases hk : k' = k
    · rw [hk]
      cases hc' with
      | ld_rq =>
        cases hs with
        | ld_rq => simp only [update_Fin_gss, hext k]
      | st_rq v =>
        cases hs with
        | st_rq => simp only [update_Fin_gss, hext k]
      | ld_rq_data_available1 rst hrq hS =>
        cases hs with
        | ld_rs _ _ rst' hrq' hm' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
      | ld_rq_data_available rst hrq hM =>
        cases hs with
        | ld_rs _ _ rst' hrq' hm' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
      | ld_rq_data_availableE rst hrq hE =>
        cases hs with
        | ld_rs _ _ rst' hrq' hm' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
      | st_rq_M_state v rst hrq hM =>
        cases hs with
        | st_rs v' _ rst' hrq' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
    · have hs' : s'.extqueue k' = s.extqueue k' := by
        cases hs <;> simp only [update_Fin_gso2 _ _ _ _ hk]
      rw [hs']
      simp only [update_Fin_gso2 _ _ _ _ hk]
      exact hext k'

/-- La memoria dello spec dopo un passo: cambia solo con `st_rs`, nel valore in testa alla coda. -/
theorem spec_memory {s s' : SeqState n} {e : Event} {k : Fin n} (hs : seq_step s (.cache e k) s') :
    (e ≠ Event.st_rs → s'.memory = s.memory)
    ∧ (e = Event.st_rs → ∃ v rst, (s.extqueue k).rq = Event.st_rq v :: rst ∧ s'.memory = v) := by
  cases hs with
  | ld_rq => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | st_rq v => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | ld_rs v _ rst hrq hm => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | st_rs v _ rst hrq => exact ⟨fun hne => absurd rfl hne, fun _ => ⟨v, rst, hrq, rfl⟩⟩

/-- Da uno stato flushed (`flush0`) la cache `k` acquisisce `M` (`rqM`, grant, presa): valore
`s.memory`, `extqueue` invariate. -/
theorem acquire_M {x : MESIState n} {s : SeqState n} (k : Fin n) (hf : flush0 x s) :
    ∃ y, trans_refl (mesi_rule n) x y ∧ (y.caches k).state = Bstate.M
      ∧ (y.caches k).value = s.memory ∧ ∀ k', (y.caches k').extqueue = (x.caches k').extqueue := by
  obtain ⟨hc, hp, hv⟩ := hf
  obtain ⟨hkI, hcp, hpc⟩ := hc k
  refine ⟨_, trans_refl.step
    (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
      (cache_mesi_step_internal.upgrade_from_I_rq _ hkI)))
    (trans_refl.step
      (mesi_rule_of_step (mesi_step_internal.parent_upd_queue _ _ _ k
        (parent_mesi_step.upgrade_to_M_data_avilable_rq1 _ k 0 ?h1 ?h2)))
      (trans_refl.step
        (mesi_rule_of_step (mesi_step_internal.cache _ _ k _
          (cache_mesi_step_internal.upgrade_from_I_rs _ x.parent.value 0 ?h3 ?h4)))
        trans_refl.refl)), ?_, ?_, ?_⟩
  case h1 => simp [update_Fin_gss, hcp]
  case h2 => intro j; simpa using (hp j).1
  case h3 => simp [update_Fin_gss, hpc]
  case h4 => simp [update_Fin_gss, hkI]
  · simp [update_Fin_gss]
  · simp [update_Fin_gss, hv]
  · intro k'
    by_cases hkk : k' = k
    · subst hkk; simp [update_Fin_gss]
    · simp [update_Fin_gso2 _ _ _ _ hkk]

/-- `relation_flush` di ARS per la `flush` completa: `mesi_relation_flush0` più l'invarianza delle
`extqueue` lungo i passi interni. -/
theorem mesi_relation_flush (i i' : MESIState n) (s : SeqState n) :
    relation_flush flush i i' s (mesi_rule n) := by
  unfold relation_flush
  intro hf htr
  obtain ⟨hf0, hext⟩ := hf
  obtain ⟨i'', h1, h2⟩ := mesi_relation_flush0 i i' s hf0 htr
  refine ⟨i'', h1, h2, fun k => ?_⟩
  rw [ext_trans h1 k, ext_trans htr k]
  exact hext k

/-- `relation_init` di ARS per la `flush` completa: lo stato iniziale è flushed rispetto a
`seq_init n`, code esterne comprese (vuote da entrambe le parti). -/
theorem mesi_relation_init : relation_init flush (default : MESIState n) (seq_init n) := by
  unfold relation_init flush
  exact ⟨mesi_relation_init0 default
    ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ => rfl⟩

/-- `relation_method_int` di ARS: in uno stato `i'` raggiunto con passi interni da uno flushed,
ogni evento esterno dell'implementazione è possibile anche nello spec. Le richieste sempre; le
risposte perché la coda della cache è quella dello spec (`flush`, `ext_trans`) e il valore risposto
è il valore logico, cioè `s.memory` (`flushInv` lungo i passi interni: `cacheVal`). -/
theorem mesi_relation_method_int (i i' i'' : MESIState n) (s : SeqState n) (e : MSIExternalEvent n) :
    ReachingStar.relation_method_int flush (mesi_rule n) mesi_step_external seq_step i i' i'' s e := by
  unfold ReachingStar.relation_method_int
  intro hf htr h
  obtain ⟨hf0, hext⟩ := hf
  have hI : flushInv i' s := inv_trans (inv_of_flush hf0) htr
  have hext' : ∀ k, (i'.caches k).extqueue = s.extqueue k :=
    fun k => (ext_trans htr k).trans (hext k)
  cases e with
  | cache ev k =>
    cases h with
    | cache ev' c' k hc' =>
      cases hc' with
      | ld_rq => exact ⟨_, seq_step.ld_rq s k⟩
      | st_rq v => exact ⟨_, seq_step.st_rq s v k⟩
      | ld_rq_data_available1 rst hrq hS =>
        exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext' k]; exact hrq)
          (hI.cacheVal k (by rw [hS]; intro h; cases h)).symm⟩
      | ld_rq_data_available rst hrq hM =>
        exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext' k]; exact hrq)
          (hI.cacheVal k (by rw [hM]; intro h; cases h)).symm⟩
      | ld_rq_data_availableE rst hrq hE =>
        exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext' k]; exact hrq)
          (hI.cacheVal k (by rw [hE]; intro h; cases h)).symm⟩
      | st_rq_M_state v rst hrq hM =>
        exact ⟨_, seq_step.st_rs s v k rst (by rw [← hext' k]; exact hrq)⟩

/-- `relation_flush_method_int` di ARS: dopo lo stesso evento in `i'` e in `s`, l'implementazione
torna con passi interni a uno stato flushed rispetto a `s'`: lo stato canonico di `i''` con valore
logico `s'.memory` (`reach_canon`, `flush_canon`, `lv_step_ext_val`, `ext_step_ext`, `spec_memory`). -/
theorem mesi_relation_flush_method_int (i i' i'' : MESIState n) (s s' : SeqState n)
    (e : MSIExternalEvent n) :
    ReachingStar.relation_flush_method_int flush (mesi_rule n) mesi_step_external seq_step
      i i' i'' s s' e := by
  unfold ReachingStar.relation_flush_method_int
  intro hf htr h hs
  obtain ⟨hf0, hext⟩ := hf
  have hc := coh_of_flush0 hf0
  have hl := lv_of_flush0 hf0
  obtain ⟨hc', hl'⟩ := coh_lv_trans hc hl htr
  have hext' : ∀ k, (i'.caches k).extqueue = s.extqueue k :=
    fun k => (ext_trans htr k).trans (hext k)
  cases e with
  | cache ev k =>
    have hc'' := coh_step_ext hc' h
    have hext'' := ext_step_ext hext' h hs
    have hlv := lv_step_ext_val hc' hl' h
    have hsm := spec_memory hs
    have hl'' : LV i'' s'.memory := by
      by_cases hev : ev = Event.st_rs
      · obtain ⟨v, rst, hrq, hmem⟩ := hsm.2 hev
        have hLv := hlv.2 hev
        have hval : (i''.caches k).value = v := by
          subst hev
          cases h
          rename_i c' hcs
          cases hcs with
          | st_rq_M_state v' rst' hrq' hM =>
            simp only [update_Fin_gss]
            rw [hext' k] at hrq'
            rw [hrq'] at hrq
            exact Event.st_rq.inj (List.cons.inj hrq).1
        rw [hmem, ← hval]
        exact hLv
      · have := hlv.1 hev
        rw [hsm.1 hev]
        exact this
    exact ⟨canon i'' s'.memory, reach_canon hc'' hl'', flush_canon rfl hext''⟩

/-- Lo stato canonico dipende solo dalle `extqueue`. -/
theorem mesi_commutes_upto_aux1 {x y : MESIState n} {m : Value}
    (h : ∀ k, (x.caches k).extqueue = (y.caches k).extqueue) : canon x m = canon y m := by
  unfold canon
  congr 1
  funext k
  rw [h k]

/-- Ricongiungimento: due stati con `cohInv`, lo stesso valore logico e le stesse `extqueue`
si ricongiungono nel (comune) stato canonico. -/
theorem mesi_commutes_upto_aux2 {c d : MESIState n} {m : Value} (hcc : cohInv c) (hlc : LV c m)
    (hcd : cohInv d) (hld : LV d m)
    (hext : ∀ k, (c.caches k).extqueue = (d.caches k).extqueue) :
    ∃ j, trans_refl (mesi_rule n) c j ∧ trans_refl (mesi_rule n) d j := by
  refine ⟨canon c m, reach_canon hcc hlc, ?_⟩
  rw [mesi_commutes_upto_aux1 hext]
  exact reach_canon hcd hld

/-- Da uno stato con `cohInv` e valore logico `m` si raggiunge con passi interni uno stato in cui
la cache `k` è in `M` con valore `m`; le `extqueue` non cambiano (`predrain`, `flushInv_of_lv`,
le tre fasi, `acquire_M`). -/
theorem mesi_commutes_upto_aux3 {b : MESIState n} {m : Value} (k : Fin n) (hcb : cohInv b)
    (hlb : LV b m) :
    ∃ f, trans_refl (mesi_rule n) b f ∧ (f.caches k).state = Bstate.M ∧ (f.caches k).value = m
      ∧ ∀ k', (f.caches k').extqueue = (b.caches k').extqueue := by
  obtain ⟨y, hby, h0⟩ := predrain hcb hlb
  obtain ⟨hcy, hly⟩ := coh_lv_trans hcb hlb hby
  have hI := flushInv_of_lv hcy hly h0
  obtain ⟨y1, h1, hI1, hq1⟩ := phase1 hI
  obtain ⟨y2, h2, hI2, hq1', hq2⟩ := phase2 hI1 hq1
  obtain ⟨y3, h3, hI3, hq1'', hq2', hq3⟩ := phase3 hI2 hq1' hq2
  have hf3 : flush0 y3 ⟨m, fun _ => default⟩ := flush_of_quiet hI3 hq1'' hq2' hq3
  obtain ⟨f, hyf, hfM, hfv, _⟩ := acquire_M k hf3
  have hpath : trans_refl (mesi_rule n) b f :=
    phase2_aux1 hby (phase2_aux1 h1 (phase2_aux1 h2 (phase2_aux1 h3 hyf)))
  exact ⟨f, hpath, hfM, hfv, ext_trans hpath⟩

/-- La commutazione a meno di passi interni sugli stati raggiungibili (l'ipotesi (5) di
`ReachingStar.trace_inclusion`). Richieste: `b' = b`, `d = b` più la richiesta, `j` lo stato
canonico. Risposte: da `b` si torna a flushed e si riacquisisce `M` per la cache (`acquire_M`); la
richiesta è ancora in testa perché i passi interni non toccano le `extqueue`; la risposta ha lo
stesso valore che in `c` (valore logico); `j` è lo stato canonico di `c`, uguale a quello di `d`. -/
theorem mesi_commutes_upto :
    ReachingStar.commutes_method_rule_upto_on
      (fun i' => ReachingStar.reachable (mesi_rule n) mesi_step_external i' (default : MESIState n))
      mesi_step_external (mesi_rule n) := by
  unfold ReachingStar.commutes_method_rule_upto_on
  intro a b c e hR hab hac
  obtain ⟨hca, m, hla⟩ := reach_inv (show Reach a from hR)
  obtain ⟨hcb, hlb⟩ := coh_lv_trans hca hla hab
  have hextab := ext_trans hab
  have hac' := hac
  cases e with
  | cache ev k =>
  cases hac with
  | cache a c' =>
  rename_i hc'
  cases hc' with
  | ld_rq =>
    -- richiesta: `b' = b`, `d` = `b` più la richiesta, `j` lo stato canonico
    have hd := mesi_step_external.cache b _ _ k (cache_mesi_step.ld_rq (b.caches k))
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac')
      ((lv_step_ext_val hca hla hac').1 (by decide)) (coh_step_ext hcb hd)
      ((lv_step_ext_val hcb hlb hd).1 (by decide))
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextab]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextab k').symm)
    exact ⟨b, _, j, trans_refl.refl, hd, hcj, hdj⟩
  | st_rq v =>
    have hd := mesi_step_external.cache b _ _ k (cache_mesi_step.st_rq (b.caches k) v)
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac')
      ((lv_step_ext_val hca hla hac').1 (by intro h; cases h)) (coh_step_ext hcb hd)
      ((lv_step_ext_val hcb hlb hd).1 (by intro h; cases h))
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextab]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextab k').symm)
    exact ⟨b, _, j, trans_refl.refl, hd, hcj, hdj⟩
  | ld_rq_data_available1 rst hrq hS =>
    -- risposta a una load (da `S`): da `b` si riacquisisce `M` e si serve la stessa richiesta
    have hva : (a.caches k).value = m := hla.cacheS k hS
    obtain ⟨f, hbf, hfM, hfv, hfext⟩ := mesi_commutes_upto_aux3 k hcb hlb
    obtain ⟨hcf, hlf⟩ := coh_lv_trans hcb hlb hbf
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfv' : (f.caches k).value = (a.caches k).value := hfv.trans hva.symm
    have hfrq : (f.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hextaf k]; exact hrq
    have hd := mesi_step_external.cache f _ _ k
      (cache_mesi_step.ld_rq_data_available (f.caches k) rst hfrq hfM)
    rw [hfv'] at hd
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac')
      ((lv_step_ext_val hca hla hac').1 (by intro h; cases h)) (coh_step_ext hcf hd)
      ((lv_step_ext_val hcf hlf hd).1 (by intro h; cases h))
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩
  | ld_rq_data_available rst hrq hM =>
    -- risposta a una load (da `M`)
    have hva : (a.caches k).value = m := hla.cacheM k (Or.inl hM)
    obtain ⟨f, hbf, hfM, hfv, hfext⟩ := mesi_commutes_upto_aux3 k hcb hlb
    obtain ⟨hcf, hlf⟩ := coh_lv_trans hcb hlb hbf
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfv' : (f.caches k).value = (a.caches k).value := hfv.trans hva.symm
    have hfrq : (f.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hextaf k]; exact hrq
    have hd := mesi_step_external.cache f _ _ k
      (cache_mesi_step.ld_rq_data_available (f.caches k) rst hfrq hfM)
    rw [hfv'] at hd
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac')
      ((lv_step_ext_val hca hla hac').1 (by intro h; cases h)) (coh_step_ext hcf hd)
      ((lv_step_ext_val hcf hlf hd).1 (by intro h; cases h))
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩
  | ld_rq_data_availableE rst hrq hE =>
    -- risposta a una load (da `E`): come da `M`, la risposta da `f` è servita in `M`
    have hva : (a.caches k).value = m := hla.cacheM k (Or.inr hE)
    obtain ⟨f, hbf, hfM, hfv, hfext⟩ := mesi_commutes_upto_aux3 k hcb hlb
    obtain ⟨hcf, hlf⟩ := coh_lv_trans hcb hlb hbf
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfv' : (f.caches k).value = (a.caches k).value := hfv.trans hva.symm
    have hfrq : (f.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hextaf k]; exact hrq
    have hd := mesi_step_external.cache f _ _ k
      (cache_mesi_step.ld_rq_data_available (f.caches k) rst hfrq hfM)
    rw [hfv'] at hd
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac')
      ((lv_step_ext_val hca hla hac').1 (by intro h; cases h)) (coh_step_ext hcf hd)
      ((lv_step_ext_val hcf hlf hd).1 (by intro h; cases h))
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩
  | st_rq_M_state v rst hrq hM =>
    -- risposta a una store: da `b` si riacquisisce `M` e si serve la stessa richiesta; il nuovo
    -- valore logico è `v` da entrambe le parti
    obtain ⟨f, hbf, hfM, _, hfext⟩ := mesi_commutes_upto_aux3 k hcb hlb
    obtain ⟨hcf, hlf⟩ := coh_lv_trans hcb hlb hbf
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfrq : (f.caches k).extqueue.rq = Event.st_rq v :: rst := by rw [hextaf k]; exact hrq
    have hd := mesi_step_external.cache f _ _ k
      (cache_mesi_step.st_rq_M_state (f.caches k) v rst hfrq hfM)
    have hlc := (lv_step_ext_val hca hla hac').2 rfl
    simp only [update_Fin_gss] at hlc
    have hld := (lv_step_ext_val hcf hlf hd).2 rfl
    simp only [update_Fin_gss] at hld
    obtain ⟨j, hcj, hdj⟩ := mesi_commutes_upto_aux2 (coh_step_ext hca hac') hlc
      (coh_step_ext hcf hd) hld
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩

end ConfluenceOnReachable

/-- **L'inclusione delle tracce di MSI nello spec sequenziale**, via `ReachingStar.trace_inclusion`
(commutazione a meno di passi interni). Le sei ipotesi: (1) `mesi_relation_flush`, (2)
`mesi_relation_flush_method_int`, (3) `mesi_relation_method_int`, (4) `mesi_confluent`, (5)
`mesi_commutes_upto`, (6) `mesi_relation_init`. Le conversioni tra `star_extend`/`star` di `star.lean`
e quelli di ARS sono `have` inline. -/
theorem trace_inclusion (l : List (MSIExternalEvent n)) :
  imp_behaviour n l -> spec_behaviour n l := by
  intro himp
  -- comportamenti dell'implementazione: da `star_extend` di `star.lean` (passi interni etichettati)
  -- a `star_extend` di ARS (tratti `trans_refl (mesi_rule n)`)
  have conv_imp : ∀ (a b : MESIState n) (l : List (MSIExternalEvent n)),
      star_extend mesi_step_external mesi_step_internal a l b →
      ReachingStar.star_extend (mesi_rule n) mesi_step_external a l b := by
    intro a b l h
    induction h with
    | refl => exact ReachingStar.star_extend.refl a
    | step_int l₁ s₁ s₂ ie _ hstep ih =>
      exact ReachingStar.star_extend.step_int a l₁ s₁ s₂ ih
        (trans_refl.step (mesi_rule_of_step hstep) trans_refl.refl)
    | step_ext l₁ s₁ s₂ e _ hstep ih => exact ReachingStar.star_extend.step_ext a l₁ s₁ s₂ e ih hstep
  -- comportamenti dello spec: da `star` di ARS a `star` di `star.lean`
  have conv_spec : ∀ (a b : SeqState n) (l : List (MSIExternalEvent n)),
      ReachingStar.star seq_step a l b → star seq_step a l b := by
    intro a b l h
    induction h with
    | refl => exact star.refl a
    | step s₂ s₃ l₁ e₁ _ hstep ih => exact star.step a s₂ s₃ l₁ e₁ ih hstep
  have himp' : ReachingStar.imp_behaviour (mesi_rule n) mesi_step_external l (default : MESIState n) := by
    unfold imp_behaviour behaviour_extend at himp
    obtain ⟨s', hs'⟩ := himp
    exact ⟨s', conv_imp _ _ _ hs'⟩
  have hspec := ReachingStar.trace_inclusion flush (mesi_rule n) mesi_step_external seq_step l
    (default : MESIState n) (seq_init n) mesi_relation_flush mesi_relation_flush_method_int
    mesi_relation_method_int mesi_confluent mesi_commutes_upto mesi_relation_init himp'
  obtain ⟨s', hs'⟩ := hspec
  unfold spec_behaviour behaviour
  exact ⟨s', conv_spec _ _ _ hs'⟩

end MESI
