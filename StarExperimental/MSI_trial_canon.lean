import StarExperimental.MSI_trial_flush
import StarExperimental.MSI_trial_views15
import StarExperimental.MSI_trial_dec

/-!
# `MSI_trial`: lo stato canonico

Per `commutes_method_rule_upto_on` serve un lemma di **progresso**: dopo passi interni qualsiasi, la
cache che poteva servire una load/store riprende la linea e la serve, e i due risultati si
ricongiungono. Il modello non termina, quindi il ricongiungimento non si costruisce passo per passo:
si passa per uno **stato canonico** `canon x m`, raggiungibile internamente da ogni stato
raggiungibile (`reach_canon`, lo *svuotamento*, in `MSI_trial_drain.lean`) e invariante lungo i passi
interni (`canon_step`).

`canon x m`: tutte le cache in `I`, nessun messaggio, righe a `I`, parent a `m` (il valore logico,
`s.memory` di uno spec `s` con `flush x s`), `extqueue` di `x`; il valore di una cache è `m` se la
cache è *attiva* in `x` (tiene la linea, ha una richiesta o un grant in volo, o ha una richiesta del
programma in testa: nello svuotamento acquisirà la linea e prenderà `m`), altrimenti il suo valore
in `x`. Un rilascio in volo non rende attiva la cache: chi ha rilasciato ha già il valore `m`.

Fatti sugli stati raggiungibili usati: le viste cattive (13 + i pattern 14–15), le clausole sul
valore di `flush` (vera per ogni stato raggiungibile, `exists_flush_of_reach`) e `demandOK`, quattro
fatti sulle richieste rispetto alla coda del programma, che le viste non vedono.
-/

open THEORY Relation MSIView
open ReachingStar (Rule trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Flush per ogni stato raggiungibile -/

/-- Ogni stato raggiungibile è in relazione `flush` con qualche stato dello spec. -/
theorem exists_flush_of_reach {x : MSIState n} (h : Reach x) : ∃ s, flush x s := by
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact ⟨seq_init n, trial_relation_init⟩
  | step_int _ _ _ _ htr ih =>
      obtain ⟨s, hs⟩ := ih
      exact ⟨s, flush_trans hs htr⟩
  | step_ext _ _ _ _ _ hext ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨s', hs'⟩ := flush_method hs hext
      exact ⟨s', flush_step_ext hs hext hs'⟩

/-! ## Richieste e richieste del programma

Le viste non vedono la `extqueue`. Quattro fatti sugli stati raggiungibili che la riguardano:
una richiesta o un grant in volo hanno ancora la richiesta del programma in testa; chi tiene la
linea non ha richieste né grant in volo; richiesta e grant non sono mai in volo insieme; al più una
richiesta per cache. Sono conservati da ogni passo (le richieste partono solo con una richiesta del
programma in testa, da `I`, una per volta; servire richiede `S`/`M`). -/

/-- Numero di richieste (`rqM`, `rqS`) nella coda cache → parent. -/
def nReq (c : CacheState) : Nat :=
  c.queue_cp.countP (fun e => match e with | CPEvent.rqM => true | CPEvent.rqS => true | _ => false)

def demandOK (x : MSIState n) : Prop :=
  ∀ k, (pending (x.caches k) ∨ grantInFlight (x.caches k) → wantsM (x.caches k) ∨ wantsS (x.caches k)) ∧
       ((x.caches k).state ≠ Bstate.I → ¬ pending (x.caches k) ∧ ¬ grantInFlight (x.caches k)) ∧
       ¬ (pending (x.caches k) ∧ grantInFlight (x.caches k)) ∧
       nReq (x.caches k) ≤ 1

/-! ### Lemmi ausiliari (liste e code di una cache) -/

/-- Membership survives erasing a different element. -/
theorem canonA_mem_eraseIdx_iff {α : Type} {l : List α} {p : Nat} {a b : α}
    (hj : l[p]? = some b) (hab : a ≠ b) : a ∈ l.eraseIdx p ↔ a ∈ l := by
  constructor
  · exact List.mem_of_mem_eraseIdx
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    refine List.mem_eraseIdx_iff_getElem?.mpr ⟨i, fun hip => ?_, hi⟩
    subst hip
    rw [hj] at hi
    exact hab (Option.some.inj hi).symm

theorem canonA_grant_iff_of {c c' : CacheState}
    (h : ∀ v, (PCEvent.rsM v ∈ c'.queue_pc ↔ PCEvent.rsM v ∈ c.queue_pc) ∧
              (PCEvent.rsS v ∈ c'.queue_pc ↔ PCEvent.rsS v ∈ c.queue_pc)) :
    grantInFlight c' ↔ grantInFlight c := by
  unfold grantInFlight
  constructor
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact Or.inl ⟨v, (h v).1.mp hv⟩
    · exact Or.inr ⟨v, (h v).2.mp hv⟩
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact Or.inl ⟨v, (h v).1.mpr hv⟩
    · exact Or.inr ⟨v, (h v).2.mpr hv⟩

theorem canonA_pending_iff_of {c c' : CacheState}
    (h : (CPEvent.rqM ∈ c'.queue_cp ↔ CPEvent.rqM ∈ c.queue_cp) ∧
         (CPEvent.rqS ∈ c'.queue_cp ↔ CPEvent.rqS ∈ c.queue_cp)) : pending c' ↔ pending c := by
  unfold pending; rw [h.1, h.2]

/-- The per-cache body of `demandOK`. -/
def canonA_dOK (c : CacheState) : Prop :=
  (pending c ∨ grantInFlight c → wantsM c ∨ wantsS c) ∧
  (c.state ≠ Bstate.I → ¬ pending c ∧ ¬ grantInFlight c) ∧
  ¬ (pending c ∧ grantInFlight c) ∧ nReq c ≤ 1

theorem canonA_nReq_zero {c : CacheState} (hp : ¬ pending c) : nReq c = 0 := by
  unfold nReq
  rw [List.countP_eq_zero]
  intro a ha
  rcases a with v | _ | _ | _
  · simp
  · simp
  · exact absurd (Or.inr ha) hp
  · exact absurd (Or.inl ha) hp

theorem canonA_nReq_le_eraseIdx {c c' : CacheState} {p : Nat}
    (hc : c'.queue_cp = c.queue_cp.eraseIdx p) : nReq c' ≤ nReq c := by
  unfold nReq; rw [hc]; exact List.Sublist.countP_le (List.eraseIdx_sublist _ _)

theorem canonA_nReq_eraseIdx {c c' : CacheState} {p : Nat} {a : CPEvent}
    (hc : c'.queue_cp = c.queue_cp.eraseIdx p) (hj : c.queue_cp[p]? = some a)
    (ha : a ≠ CPEvent.rqM) (hb : a ≠ CPEvent.rqS) : nReq c' = nReq c := by
  unfold nReq; rw [hc, ← countP_eraseIdx _ _ _ _ hj]
  rcases a with v | _ | _ | _
  · simp
  · simp
  · exact absurd rfl hb
  · exact absurd rfl ha

theorem canonA_nReq_append {c c' : CacheState} {a : CPEvent}
    (hc : c'.queue_cp = c.queue_cp ++ [a]) (ha : a ≠ CPEvent.rqM) (hb : a ≠ CPEvent.rqS) :
    nReq c' = nReq c := by
  unfold nReq; rw [hc, List.countP_append]
  rcases a with v | _ | _ | _
  · simp
  · simp
  · exact absurd rfl hb
  · exact absurd rfl ha

/-- Two requests at different positions give `nReq ≥ 2`. -/
theorem canonA_nReq_two {c : CacheState} {p q : Nat} {a b : CPEvent}
    (hj : c.queue_cp[p]? = some a) (hq : c.queue_cp[q]? = some b) (hne : q ≠ p)
    (ha : a = CPEvent.rqM ∨ a = CPEvent.rqS) (hb : b = CPEvent.rqM ∨ b = CPEvent.rqS) :
    2 ≤ nReq c := by
  unfold nReq
  refine two_le_countP_of_ne _ _ hq hj hne ?_ ?_
  · rcases hb with h | h <;> subst h <;> rfl
  · rcases ha with h | h <;> subst h <;> rfl

/-- After the parent consumed the (only) request, nothing is pending. -/
theorem canonA_not_pending_eraseIdx {c c' : CacheState} {p : Nat} {a : CPEvent}
    (hj : c.queue_cp[p]? = some a) (ha : a = CPEvent.rqM ∨ a = CPEvent.rqS) (hn : nReq c ≤ 1)
    (hc : c'.queue_cp = c.queue_cp.eraseIdx p) : ¬ pending c' := by
  intro hp
  unfold pending at hp; rw [hc] at hp
  rcases hp with hm | hm
  · obtain ⟨q, hq, hqm⟩ := List.mem_eraseIdx_iff_getElem?.mp hm
    have := canonA_nReq_two hj hqm hq ha (Or.inl rfl)
    omega
  · obtain ⟨q, hq, hqm⟩ := List.mem_eraseIdx_iff_getElem?.mp hm
    have := canonA_nReq_two hj hqm hq ha (Or.inr rfl)
    omega

theorem canonA_grant_of_eraseIdx {c c' : CacheState} {p : Nat}
    (hc : c'.queue_pc = c.queue_pc.eraseIdx p) (h : grantInFlight c') : grantInFlight c := by
  unfold grantInFlight at *; rw [hc] at h
  rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨v, List.mem_of_mem_eraseIdx hv⟩
  · exact Or.inr ⟨v, List.mem_of_mem_eraseIdx hv⟩

/-- `canonA_dOK` transfers along a step that does not change pending / grant / head / `nReq`
and does not make the cache a holder. -/
theorem canonA_dOK_of_iff {c c' : CacheState} (hd : canonA_dOK c)
    (hp : pending c' ↔ pending c) (hg : grantInFlight c' ↔ grantInFlight c)
    (hw : c'.extqueue = c.extqueue) (hn : nReq c' = nReq c)
    (hs : c'.state ≠ Bstate.I → c.state ≠ Bstate.I) : canonA_dOK c' := by
  obtain ⟨d1, d2, d3, d4⟩ := hd
  refine ⟨fun h => ?_, fun h => ?_, fun h => d3 ⟨hp.mp h.1, hg.mp h.2⟩, by rw [hn]; exact d4⟩
  · have := d1 (h.imp hp.mp hg.mp)
    unfold wantsM wantsS at this ⊢; rw [hw]; exact this
  · have := d2 (hs h)
    exact ⟨fun h' => this.1 (hp.mp h'), fun h' => this.2 (hg.mp h')⟩

theorem canonA_dOK_default : demandOK (default : MSIState n) := by
  intro k
  have hc : (default : MSIState n).caches k = ⟨Bstate.I, 0, [], [], ⟨[], []⟩⟩ := rfl
  show canonA_dOK _
  rw [hc]
  refine ⟨fun h => ?_, fun h => absurd rfl h, fun h => ?_, by decide⟩
  · rcases h with (h | h) | (⟨v, h⟩ | ⟨v, h⟩) <;> exact absurd h List.not_mem_nil
  · rcases h.1 with h | h <;> exact absurd h List.not_mem_nil

theorem canonA_dOK_step_int {x y : MSIState n} {e : IEvent n} (hr : Reach x) (hd : demandOK x)
    (h : step_int x e y) : demandOK y := by
  have hsync := synced_of_reach hr
  intro j
  show canonA_dOK _
  cases h with
  | cache cache' k e hc =>
    by_cases hk : k = j
    · subst hk
      simp only [update_Fin_gss]
      obtain ⟨d1, d2, d3, d4⟩ := hd k
      obtain ⟨h1, h2⟩ := hsync k
      cases hc with
      | rq_data_not_available hM =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ (canonA_pending_iff_of ⟨by simp, by simp⟩) Iff.rfl rfl
          (canonA_nReq_append rfl (by simp) (by simp)) (fun h => absurd rfl h)
      | rq_data_not_available1 hS =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ (canonA_pending_iff_of ⟨by simp, by simp⟩) Iff.rfl rfl
          (canonA_nReq_append rfl (by simp) (by simp)) (fun h => absurd rfl h)
      | upgrade_from_I_rq hI hp hg hw =>
        refine ⟨fun _ => Or.inl hw, fun h => absurd hI h, fun h => hg h.2, ?_⟩
        show (_ ++ [CPEvent.rqM]).countP _ ≤ 1
        rw [List.countP_append]
        have hz := canonA_nReq_zero hp
        unfold nReq at hz
        rw [hz]; decide
      | upgrade_from_I_rq1 hI hp hg hw =>
        refine ⟨fun _ => Or.inr hw, fun h => absurd hI h, fun h => hg h.2, ?_⟩
        show (_ ++ [CPEvent.rqS]).countP _ ≤ 1
        rw [List.countP_append]
        have hz := canonA_nReq_zero hp
        unfold nReq at hz
        rw [hz]; decide
      | upgrade_from_I_rs v p hj hI =>
        have hg : grantInFlight (x.caches k) := Or.inl ⟨v, List.mem_of_getElem? hj⟩
        have hnp : ¬ pending (x.caches k) := fun hp => d3 ⟨hp, hg⟩
        have hj' : (x.parent.queue_pci k)[p]? = some (PCEvent.rsM v) := by rw [h2]; exact hj
        have hng : ¬ ((∃ w, PCEvent.rsM w ∈ (x.caches k).queue_pc.eraseIdx p) ∨
                      (∃ w, PCEvent.rsS w ∈ (x.caches k).queue_pc.eraseIdx p)) := by
          rintro (⟨w, hw⟩ | ⟨w, hw⟩)
          · obtain ⟨q, hq, hqw⟩ := List.mem_eraseIdx_iff_getElem?.mp hw
            have h2le := two_le_countP_of_ne isGrantM _ hqw hj hq rfl rfl
            exact not_reach_of_two_mu (i := k) (by unfold muMsgs; rw [h2]; omega) hr
          · have hsig : sigMsgs x.parent k ≠ 0 := by
              have : 0 < ((x.caches k).queue_pc).countP isGrantS :=
                List.countP_pos_iff.mpr ⟨_, List.mem_of_mem_eraseIdx hw, rfl⟩
              unfold sigMsgs; rw [h2]; omega
            exact not_reach_of_mu_sig (muMsgs_ne_zero_of_rsM hj') hsig hr
        exact ⟨fun h => d1 (h.imp (fun hp => hp) (fun hg' => canonA_grant_of_eraseIdx rfl hg')),
          fun _ => ⟨hnp, hng⟩, fun h => hnp h.1, d4⟩
      | upgrade_from_I_rsS v p hj hI =>
        have hg : grantInFlight (x.caches k) := Or.inr ⟨v, List.mem_of_getElem? hj⟩
        have hnp : ¬ pending (x.caches k) := fun hp => d3 ⟨hp, hg⟩
        have hj' : (x.parent.queue_pci k)[p]? = some (PCEvent.rsS v) := by rw [h2]; exact hj
        have hng : ¬ ((∃ w, PCEvent.rsM w ∈ (x.caches k).queue_pc.eraseIdx p) ∨
                      (∃ w, PCEvent.rsS w ∈ (x.caches k).queue_pc.eraseIdx p)) := by
          rintro (⟨w, hw⟩ | ⟨w, hw⟩)
          · have hmu : muMsgs x.parent k ≠ 0 := by
              have : 0 < ((x.caches k).queue_pc).countP isGrantM :=
                List.countP_pos_iff.mpr ⟨_, List.mem_of_mem_eraseIdx hw, rfl⟩
              unfold muMsgs; rw [h2]; omega
            exact not_reach_of_mu_sig hmu (sigMsgs_ne_zero_of_rsS hj') hr
          · obtain ⟨q, hq, hqw⟩ := List.mem_eraseIdx_iff_getElem?.mp hw
            have h2le := two_le_countP_of_ne isGrantS _ hqw hj hq rfl rfl
            exact not_reach_of_two_sig (i := k) (by unfold sigMsgs; rw [h2]; omega) hr
        exact ⟨fun h => d1 (h.imp (fun hp => hp) (fun hg' => canonA_grant_of_eraseIdx rfl hg')),
          fun _ => ⟨hnp, hng⟩, fun h => hnp h.1, d4⟩
      | downgrade_from_M_rs p hj hM =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ (canonA_pending_iff_of ⟨by simp, by simp⟩)
          (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          rfl (canonA_nReq_append rfl (by simp) (by simp)) (fun h => absurd rfl h)
      | downgrade_from_M_rs1 p hj hS =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ (canonA_pending_iff_of ⟨by simp, by simp⟩)
          (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          rfl (canonA_nReq_append rfl (by simp) (by simp)) (fun h => absurd rfl h)
      | drop_rqIμ p hj hI =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          rfl rfl (fun h => h)
      | drop_rqIσ p hj hI =>
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          rfl rfl (fun h => h)
    · simp only [update_Fin_gso _ _ _ _ hk]; exact hd j
  | parent_upd_queue parent' e k hp =>
    by_cases hk : k = j
    · subst hk
      simp only [update_Fin_gss]
      obtain ⟨d1, d2, d3, d4⟩ := hd k
      obtain ⟨h1, h2⟩ := hsync k
      cases hp with
      | downgrade_from_M_rq1 v i p hj =>
        rw [h1] at hj
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩
          (canonA_pending_iff_of
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          Iff.rfl rfl (canonA_nReq_eraseIdx rfl hj (by simp) (by simp)) (fun h => h)
      | downgrade_from_M_rq2 i p hj =>
        rw [h1] at hj
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩
          (canonA_pending_iff_of
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩)
          Iff.rfl rfl (canonA_nReq_eraseIdx rfl hj (by simp) (by simp)) (fun h => h)
      | upgrade_to_M_data_avilable_rq1 i p hj _ =>
        rw [h1] at hj
        simp only [update_Fin_gss, h1, h2]
        have hpd : pending (x.caches k) := Or.inl (List.mem_of_getElem? hj)
        exact ⟨fun _ => d1 (Or.inl hpd), fun h => absurd hpd (d2 h).1,
          fun h => canonA_not_pending_eraseIdx hj (Or.inl rfl) d4 rfl h.1,
          le_trans (canonA_nReq_le_eraseIdx rfl) d4⟩
      | upgrade_to_M_data_avilable_rq2 i p hj _ _ =>
        rw [h1] at hj
        simp only [update_Fin_gss, h1, h2]
        have hpd : pending (x.caches k) := Or.inr (List.mem_of_getElem? hj)
        exact ⟨fun _ => d1 (Or.inl hpd), fun h => absurd hpd (d2 h).1,
          fun h => canonA_not_pending_eraseIdx hj (Or.inr rfl) d4 rfl h.1,
          le_trans (canonA_nReq_le_eraseIdx rfl) d4⟩
      | upgrade_to_M_invalid_all i i' p hj _ =>
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl rfl (fun h => h)
      | upgrade_to_M_invalid_all1 i i' p hj _ =>
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl rfl (fun h => h)
      | upgrade_to_M_invalid_all2 i i' p hj _ _ =>
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl rfl (fun h => h)
      | upgrade_to_M_invalid_all3 i i' p hj _ =>
        simp only [update_Fin_gss, h1, h2]
        exact canonA_dOK_of_iff ⟨d1, d2, d3, d4⟩ Iff.rfl
          (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl rfl (fun h => h)
    · simp only [update_Fin_gso _ _ _ _ hk]; exact hd j

theorem canonA_dOK_step_ext {x y : MSIState n} {e : MSIExternalEvent n} (hd : demandOK x)
    (h : msi_step_external x e y) : demandOK y := by
  intro j
  show canonA_dOK _
  cases h with
  | cache ev cache' k hc =>
    by_cases hk : k = j
    · subst hk
      simp only [update_Fin_gss]
      obtain ⟨d1, d2, d3, d4⟩ := hd k
      cases hc with
      | ld_rq =>
        refine ⟨fun h => ?_, d2, d3, d4⟩
        rcases d1 h with ⟨v, rst, hw⟩ | ⟨rst, hw⟩
        · exact Or.inl ⟨v, rst ++ [Event.ld_rq],
            by show (x.caches k).extqueue.rq ++ _ = _; rw [hw]; rfl⟩
        · exact Or.inr ⟨rst ++ [Event.ld_rq],
            by show (x.caches k).extqueue.rq ++ _ = _; rw [hw]; rfl⟩
      | st_rq v =>
        refine ⟨fun h => ?_, d2, d3, d4⟩
        rcases d1 h with ⟨w, rst, hw⟩ | ⟨rst, hw⟩
        · exact Or.inl ⟨w, rst ++ [Event.st_rq v],
            by show (x.caches k).extqueue.rq ++ _ = _; rw [hw]; rfl⟩
        · exact Or.inr ⟨rst ++ [Event.st_rq v],
            by show (x.caches k).extqueue.rq ++ _ = _; rw [hw]; rfl⟩
      | ld_rq_data_available1 rst hrq hS =>
        have hng := d2 (by rw [hS]; intro h; cases h)
        exact ⟨fun h => absurd h (not_or.mpr hng), fun _ => hng, fun h => hng.1 h.1, d4⟩
      | ld_rq_data_available rst hrq hM =>
        have hng := d2 (by rw [hM]; intro h; cases h)
        exact ⟨fun h => absurd h (not_or.mpr hng), fun _ => hng, fun h => hng.1 h.1, d4⟩
      | st_rq_M_state v rst hrq hM =>
        have hng := d2 (by rw [hM]; intro h; cases h)
        exact ⟨fun h => absurd h (not_or.mpr hng), fun _ => hng, fun h => hng.1 h.1, d4⟩
    · simp only [update_Fin_gso _ _ _ _ hk]; exact hd j

theorem demandOK_of_reach {x : MSIState n} (h : Reach x) : demandOK x := by
  have key : ∀ {a b : MSIState n}, trans_refl (rule n) a b → Reach a → demandOK a → demandOK b := by
    intro a b htr
    induction htr with
    | refl => exact fun _ hd => hd
    | step hab _ ih =>
        intro hr hd
        obtain ⟨e, he⟩ := hab
        exact ih (reach_step hr ⟨e, he⟩) (canonA_dOK_step_int hr hd he)
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact canonA_dOK_default
  | step_int l s' s'' h1 htr ih => exact key htr ⟨l, h1⟩ ih
  | step_ext _ _ _ _ _ hext ih => exact canonA_dOK_step_ext ih hext

/-! ## Lo stato canonico -/

/-- La cache `j` è attiva in `x`: nello svuotamento acquisirà la linea e prenderà il valore `m`. -/
def active (x : MSIState n) (j : Fin n) : Prop :=
  (x.caches j).state ≠ Bstate.I ∨ pending (x.caches j) ∨ grantInFlight (x.caches j) ∨
  wantsM (x.caches j) ∨ wantsS (x.caches j)

open Classical in
/-- Lo stato canonico di `x` con valore logico `m`. -/
noncomputable def canon (x : MSIState n) (m : Value) : MSIState n :=
  ⟨fun j => ⟨Bstate.I, if active x j then m else (x.caches j).value, [], [], (x.caches j).extqueue⟩,
   ⟨m, fun _ => Bstate.I, fun _ => [], fun _ => []⟩⟩

open Classical in
/-- `canon` dipende da `x` solo attraverso i valori che assegna alle cache e le `extqueue`. -/
theorem canon_ext {x y : MSIState n} {m : Value}
    (hval : ∀ j, (if active x j then m else (x.caches j).value)
                 = (if active y j then m else (y.caches j).value))
    (hext : ∀ j, (x.caches j).extqueue = (y.caches j).extqueue) : canon x m = canon y m := by
  unfold canon
  congr 1
  funext j
  rw [hval j, hext j]

/-- `Reach` è chiuso per cammini interni. -/
theorem reach_trans {x y : MSIState n} (hr : Reach x) (h : trans_refl (rule n) x y) : Reach y := by
  induction h with
  | refl => exact hr
  | step hab _ ih => exact ih (reach_step hr hab)

/-! ### Lemmi ausiliari per `canon_step` -/

/-- The cache-level body of `active`. -/
def canonA_activeC (c : CacheState) : Prop :=
  c.state ≠ Bstate.I ∨ pending c ∨ grantInFlight c ∨ wantsM c ∨ wantsS c

theorem canonA_activeC_iff {c c' : CacheState} (hs : c'.state = c.state)
    (hp : pending c' ↔ pending c) (hg : grantInFlight c' ↔ grantInFlight c)
    (hw : c'.extqueue = c.extqueue) : canonA_activeC c' ↔ canonA_activeC c := by
  unfold canonA_activeC wantsM wantsS; rw [hs, hp, hg, hw]

open Classical in
/-- The per-cache goal of `canon_ext`, packaged so that rewriting does not touch an `if`. -/
def canonA_G (c' c : CacheState) (m : Value) : Prop :=
  (if canonA_activeC c' then m else c'.value) = (if canonA_activeC c then m else c.value)

open Classical in
theorem canonA_G_of_active {c' c : CacheState} {m : Value} (hP : canonA_activeC c')
    (hQ : canonA_activeC c) : canonA_G c' c m := by
  unfold canonA_G; rw [if_pos hP, if_pos hQ]

open Classical in
theorem canonA_G_of_iff {c' c : CacheState} {m : Value} (h : canonA_activeC c' ↔ canonA_activeC c)
    (hab : c'.value = c.value) : canonA_G c' c m := by
  unfold canonA_G
  by_cases hq : canonA_activeC c
  · rw [if_pos (h.mpr hq), if_pos hq]
  · rw [if_neg (fun hp => hq (h.mp hp)), if_neg hq, hab]

open Classical in
theorem canonA_G_of_m {c' c : CacheState} {m : Value} (ha : c'.value = m) (hb : c.value = m) :
    canonA_G c' c m := by
  unfold canonA_G; rw [ha, hb, ite_self, ite_self]

theorem canonA_G_refl {c : CacheState} {m : Value} : canonA_G c c m := rfl

/-- `canon` non cambia lungo i passi interni (stesso `m`). Usa `flush`: la cache che prende un grant
prende `m`, la cache che rilascia aveva `m`. -/
theorem canon_step {x y : MSIState n} {s : SeqState n} {e : IEvent n}
    (hr : Reach x) (hf : flush x s) (h : step_int x e y) : canon y s.memory = canon x s.memory := by
  have hsync := synced_of_reach hr
  have hval : ∀ k, (x.caches k).state ≠ Bstate.I → (x.caches k).value = s.memory := hf.2.2.1
  apply canon_ext
  · intro j
    show canonA_G (y.caches j) (x.caches j) s.memory
    cases h with
    | cache cache' k e hc =>
      by_cases hk : k = j
      · subst hk
        simp only [update_Fin_gss]
        have hvk : (x.caches k).state = Bstate.M ∨ (x.caches k).state = Bstate.S →
            (x.caches k).value = s.memory :=
          fun h => hval k (by rcases h with h | h <;> rw [h] <;> intro h' <;> cases h')
        cases hc with
        | rq_data_not_available hM => exact canonA_G_of_m (hvk (Or.inl hM)) (hvk (Or.inl hM))
        | rq_data_not_available1 hS => exact canonA_G_of_m (hvk (Or.inr hS)) (hvk (Or.inr hS))
        | upgrade_from_I_rq _ _ _ hw =>
          exact canonA_G_of_active (Or.inr (Or.inr (Or.inr (Or.inl hw)))) (Or.inr (Or.inr (Or.inr (Or.inl hw))))
        | upgrade_from_I_rq1 _ _ _ hw =>
          exact canonA_G_of_active (Or.inr (Or.inr (Or.inr (Or.inr hw)))) (Or.inr (Or.inr (Or.inr (Or.inr hw))))
        | upgrade_from_I_rs v p hj _ =>
          exact canonA_G_of_active (Or.inl (by simp))
            (Or.inr (Or.inr (Or.inl (Or.inl ⟨v, List.mem_of_getElem? hj⟩))))
        | upgrade_from_I_rsS v p hj _ =>
          exact canonA_G_of_active (Or.inl (by simp))
            (Or.inr (Or.inr (Or.inl (Or.inr ⟨v, List.mem_of_getElem? hj⟩))))
        | downgrade_from_M_rs p hj hM => exact canonA_G_of_m (hvk (Or.inl hM)) (hvk (Or.inl hM))
        | downgrade_from_M_rs1 p hj hS => exact canonA_G_of_m (hvk (Or.inr hS)) (hvk (Or.inr hS))
        | drop_rqIμ p hj _ =>
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩) rfl) rfl
        | drop_rqIσ p hj _ =>
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl (canonA_grant_iff_of fun v =>
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩) rfl) rfl
      · simp only [update_Fin_gso _ _ _ _ hk]; exact canonA_G_refl
    | parent_upd_queue parent' e k hp =>
      by_cases hk : k = j
      · subst hk
        obtain ⟨h1, h2⟩ := hsync k
        simp only [update_Fin_gss]
        cases hp with
        | downgrade_from_M_rq1 v i p hj =>
          rw [h1] at hj
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl (canonA_pending_iff_of
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩) Iff.rfl rfl) rfl
        | downgrade_from_M_rq2 i p hj =>
          rw [h1] at hj
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl (canonA_pending_iff_of
            ⟨canonA_mem_eraseIdx_iff hj (by simp), canonA_mem_eraseIdx_iff hj (by simp)⟩) Iff.rfl rfl) rfl
        | upgrade_to_M_data_avilable_rq1 i p hj _ =>
          rw [h1] at hj
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_active (Or.inr (Or.inr (Or.inl (Or.inl ⟨x.parent.value, by simp⟩))))
            (Or.inr (Or.inl (Or.inl (List.mem_of_getElem? hj))))
        | upgrade_to_M_data_avilable_rq2 i p hj _ _ =>
          rw [h1] at hj
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_active (Or.inr (Or.inr (Or.inl (Or.inr ⟨x.parent.value, by simp⟩))))
            (Or.inr (Or.inl (Or.inr (List.mem_of_getElem? hj))))
        | upgrade_to_M_invalid_all i i' p hj _ =>
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl
            (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl) rfl
        | upgrade_to_M_invalid_all1 i i' p hj _ =>
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl
            (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl) rfl
        | upgrade_to_M_invalid_all2 i i' p hj _ _ =>
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl
            (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl) rfl
        | upgrade_to_M_invalid_all3 i i' p hj _ =>
          simp only [update_Fin_gss, h1, h2]
          exact canonA_G_of_iff (canonA_activeC_iff rfl Iff.rfl
            (canonA_grant_iff_of fun v => ⟨by simp, by simp⟩) rfl) rfl
      · simp only [update_Fin_gso _ _ _ _ hk]; exact canonA_G_refl
  · intro j; exact extqueue_step_int h j

theorem canon_trans {x y : MSIState n} {s : SeqState n}
    (hr : Reach x) (hf : flush x s) (h : trans_refl (rule n) x y) :
    canon y s.memory = canon x s.memory := by
  induction h with
  | refl => rfl
  | step hab _ ih =>
      obtain ⟨e, he⟩ := hab
      rw [ih (reach_step hr ⟨e, he⟩) (flush_step_int hf he), canon_step hr hf he]

/-- Il canonico di un canonico è lui stesso. -/
theorem canon_canon {x : MSIState n} {m : Value} : canon (canon x m) m = canon x m := by
  classical
  apply canon_ext
  · intro j
    have hv : ((canon x m).caches j).value = if active x j then m else (x.caches j).value := rfl
    have hact : active (canon x m) j → active x j := by
      intro h
      rcases h with h | h | h | h | h
      · exact absurd rfl h
      · rcases h with h | h <;> exact absurd h (List.not_mem_nil)
      · rcases h with ⟨v, h⟩ | ⟨v, h⟩ <;> exact absurd h (List.not_mem_nil)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    by_cases h : active x j
    · rw [if_pos h]
      by_cases h' : active (canon x m) j
      · rw [if_pos h']
      · rw [if_neg h', hv, if_pos h]
    · rw [if_neg h, if_neg (fun h' => h (hact h')), hv, if_neg h]
  · intro j; rfl

/-! ## Le tappe dello svuotamento (`MSI_trial_drain1/2.lean`) -/

/-- Nessuna cache tiene la linea, nessun token (`rsM`, `rsS`, `rsIμ`, `rsIσ`) in volo, righe a `I`. -/
def Quiet1 (x : MSIState n) : Prop :=
  (∀ k, (x.caches k).state = Bstate.I) ∧
  (∀ k v, PCEvent.rsM v ∉ (x.caches k).queue_pc) ∧ (∀ k v, PCEvent.rsS v ∉ (x.caches k).queue_pc) ∧
  (∀ k v, CPEvent.rsIμ v ∉ (x.caches k).queue_cp) ∧ (∀ k, CPEvent.rsIσ ∉ (x.caches k).queue_cp) ∧
  (∀ k, x.parent.shared_state k = Bstate.I)

/-- `Quiet1` e nessun invalidate in volo. -/
def Quiet2 (x : MSIState n) : Prop :=
  Quiet1 x ∧ (∀ k, PCEvent.rqIμ ∉ (x.caches k).queue_pc) ∧ (∀ k, PCEvent.rqIσ ∉ (x.caches k).queue_pc)

/-- `Quiet2` e nessuna richiesta in volo: le code sono tutte vuote. -/
def Quiet3 (x : MSIState n) : Prop :=
  Quiet2 x ∧ (∀ k, ¬ pending (x.caches k))

/-- Quel che lo svuotamento conserva di `x`: le `extqueue`; le cache inattive restano inattive e con
il loro valore; ogni valore è quello di `x` o `m`. -/
def Keeps (x y : MSIState n) (m : Value) : Prop :=
  (∀ j, (y.caches j).extqueue = (x.caches j).extqueue) ∧
  (∀ j, ¬ active x j → ¬ active y j) ∧
  (∀ j, ¬ active x j → (y.caches j).value = (x.caches j).value) ∧
  (∀ j, (y.caches j).value = (x.caches j).value ∨ (y.caches j).value = m)

theorem Keeps.refl (x : MSIState n) (m : Value) : Keeps x x m :=
  ⟨fun _ => rfl, fun _ h => h, fun _ _ => rfl, fun _ => Or.inl rfl⟩

theorem Keeps.trans {x y z : MSIState n} {m : Value} (h₁ : Keeps x y m) (h₂ : Keeps y z m) :
    Keeps x z m := by
  obtain ⟨e₁, a₁, v₁, w₁⟩ := h₁
  obtain ⟨e₂, a₂, v₂, w₂⟩ := h₂
  refine ⟨fun j => (e₂ j).trans (e₁ j), fun j h => a₂ j (a₁ j h),
    fun j h => (v₂ j (a₁ j h)).trans (v₁ j h), fun j => ?_⟩
  rcases w₂ j with h | h
  · rw [h]; exact w₁ j
  · exact Or.inr h

end MSITrial
