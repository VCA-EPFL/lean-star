import StarExperimental.MSI_trial_def
import StarExperimental.MSI

/-!
# `MSI_trial`: corrispondenza con i passi di `MSI_def`

Le regole di `MSI_trial` sono quelle di `MSI_def` con due guardie in più sulle richieste e due regole
di scarto in più. Quindi:

* ogni passo interno di `MSI_trial` che non è uno scarto è un passo di `MSI_def` (`step_int_old`);
* ogni passo di `MSI_def` che non è una richiesta è un passo di `MSI_trial` (`step_int_of_old`);
  una richiesta lo è se la cache non ha richieste in sospeso né grant in volo (`step_int_of_old_req`).

Con questi lemmi i diamanti locali di `MSI.lean` che non usano l'uscita `¬ MSI.reachable` si
trasportano a `MSI_trial` senza rifarne le dimostrazioni: i cammini di ricongiungimento di `MSI.lean`
contengono richieste solo come ripetizione del passo di richiesta del picco, e per quelle la guardia
si conserva (`req_guard_preserved`).
-/

open THEORY Relation MSIView

namespace MSITrial

variable {n : Nat}

/-! ## Da `MSI_trial` a `MSI_def` -/

/-- L'evento di `MSI_def` corrispondente; gli scarti non hanno corrispondente (`intro`). -/
def CEvent.toOld : CEvent → CacheInternalEvent
  | .rq_data_not_available => .rq_data_not_available
  | .upgrade_from_I_rq => .upgrade_from_I_rq
  | .upgrade_from_I_rs v => .upgrade_from_I_rs v
  | .downgrade_from_M_rs => .downgrade_from_M_rs
  | .ld_rq_data_not_availableS => .ld_rq_data_not_availableS
  | .upgrade_from_I_rqS => .upgrade_from_I_rqS
  | .upgrade_from_I_rsS v => .upgrade_from_I_rsS v
  | .downgrade_from_S_rsS => .downgrade_from_S_rsS
  | .drop_rqIμ => .intro
  | .drop_rqIσ => .intro

def CEvent.isDrop : CEvent → Prop
  | .drop_rqIμ => True
  | .drop_rqIσ => True
  | _ => False

def toOld : IEvent n → MSIInternalEvent n
  | .cache e i => .cache e.toOld i
  | .parent e i => .parent (.upd_queue e i)

def IEvent.isDrop : IEvent n → Prop
  | .cache e _ => e.isDrop
  | .parent _ _ => False

theorem cache_step_old {c c' : CacheState} {e : CEvent} (h : cache_step c e c') (hd : ¬ e.isDrop) :
    cache_msi_step_internal c e.toOld c' := by
  cases h with
  | rq_data_not_available hM => exact .rq_data_not_available _ hM
  | rq_data_not_available1 hS => exact .rq_data_not_available1 _ hS
  | upgrade_from_I_rq hI _ _ _ => exact .upgrade_from_I_rq _ hI
  | upgrade_from_I_rq1 hI _ _ _ => exact .upgrade_from_I_rq1 _ hI
  | upgrade_from_I_rs v j hj hI => exact .upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact .upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM => exact .downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS => exact .downgrade_from_M_rs1 _ j hj hS
  | drop_rqIμ => exact absurd trivial hd
  | drop_rqIσ => exact absurd trivial hd

/-- Ogni passo interno di `MSI_trial` che non è uno scarto è un passo interno di `MSI_def`. -/
theorem step_int_old {s s' : MSIState n} {e : IEvent n} (h : step_int s e s') (hd : ¬ e.isDrop) :
    msi_step_internal s (toOld e) s' := by
  cases h with
  | cache _ i e hc => exact .cache _ _ i _ (cache_step_old hc hd)
  | parent_upd_queue _ e i hp => exact .parent_upd_queue _ _ e i hp

/-! ## Da `MSI_def` a `MSI_trial` -/

/-- L'evento di `MSI_trial` corrispondente a un evento di cache di `MSI_def` (gli eventi che non
etichettano nessuna regola interna, `ld_rs`, `st_rs`, `intro`, vanno su un valore qualsiasi). -/
def CEvent.ofOld : CacheInternalEvent → CEvent
  | .rq_data_not_available => .rq_data_not_available
  | .upgrade_from_I_rq => .upgrade_from_I_rq
  | .upgrade_from_I_rs v => .upgrade_from_I_rs v
  | .downgrade_from_M_rs => .downgrade_from_M_rs
  | .ld_rq_data_not_availableS => .ld_rq_data_not_availableS
  | .upgrade_from_I_rqS => .upgrade_from_I_rqS
  | .upgrade_from_I_rsS v => .upgrade_from_I_rsS v
  | .downgrade_from_S_rsS => .downgrade_from_S_rsS
  | .ld_rs _ => .drop_rqIμ
  | .st_rs _ => .drop_rqIμ
  | .intro => .drop_rqIμ

/-- Un passo di cache di `MSI_def` che non è una richiesta è un passo di `MSI_trial`. -/
theorem cache_step_of_old {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c')
    (hr : e ≠ .upgrade_from_I_rq ∧ e ≠ .upgrade_from_I_rqS) :
    cache_step c (CEvent.ofOld e) c' := by
  cases h with
  | rq_data_not_available hM => exact .rq_data_not_available _ hM
  | rq_data_not_available1 hS => exact .rq_data_not_available1 _ hS
  | upgrade_from_I_rq => exact absurd rfl hr.1
  | upgrade_from_I_rq1 => exact absurd rfl hr.2
  | upgrade_from_I_rs v j hj hI => exact .upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact .upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM => exact .downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS => exact .downgrade_from_M_rs1 _ j hj hS

/-- Una richiesta di `MSI_def` è un passo di `MSI_trial` se vale la guardia nuova. -/
theorem cache_step_of_old_req {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal c e c')
    (hp : ¬ pending c) (hg : ¬ grantInFlight c)
    (hw : (e = .upgrade_from_I_rq → wantsM c) ∧ (e = .upgrade_from_I_rqS → wantsS c)) :
    cache_step c (CEvent.ofOld e) c' := by
  cases h with
  | rq_data_not_available hM => exact .rq_data_not_available _ hM
  | rq_data_not_available1 hS => exact .rq_data_not_available1 _ hS
  | upgrade_from_I_rq hI => exact .upgrade_from_I_rq _ hI hp hg (hw.1 rfl)
  | upgrade_from_I_rq1 hI => exact .upgrade_from_I_rq1 _ hI hp hg (hw.2 rfl)
  | upgrade_from_I_rs v j hj hI => exact .upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact .upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM => exact .downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS => exact .downgrade_from_M_rs1 _ j hj hS

/-- Un passo di cache di `MSI_def` che non è una richiesta è un passo interno di `MSI_trial`. -/
theorem step_int_of_old_cache {s s' : MSIState n} {e : CacheInternalEvent} {i : Fin n}
    (h : msi_step_internal s (.cache e i) s')
    (hr : e ≠ .upgrade_from_I_rq ∧ e ≠ .upgrade_from_I_rqS) :
    step_int s (.cache (CEvent.ofOld e) i) s' := by
  cases h with
  | cache _ _ _ hc => exact .cache _ _ i _ (cache_step_of_old hc hr)

/-- Un passo del parent di `MSI_def` è un passo interno di `MSI_trial`. -/
theorem step_int_of_old_parent {s s' : MSIState n} {e : ParentUpdQueueInternalEvent n} {i : Fin n}
    (h : msi_step_internal s (.parent (.upd_queue e i)) s') :
    step_int s (.parent e i) s' := by
  cases h with
  | parent_upd_queue _ _ _ hp => exact .parent_upd_queue _ _ e i hp

/-- Una richiesta di `MSI_def` dalla cache `i` è un passo di `MSI_trial` se la cache `i` non ha
richieste in sospeso né grant in volo. -/
theorem step_int_of_old_req {s s' : MSIState n} {e : CacheInternalEvent} {i : Fin n}
    (h : msi_step_internal s (.cache e i) s')
    (hp : ¬ pending (s.caches i)) (hg : ¬ grantInFlight (s.caches i))
    (hw : (e = .upgrade_from_I_rq → wantsM (s.caches i)) ∧ (e = .upgrade_from_I_rqS → wantsS (s.caches i))) :
    step_int s (.cache (CEvent.ofOld e) i) s' := by
  cases h with
  | cache _ _ _ hc => exact .cache _ _ i _ (cache_step_of_old_req hc hp hg hw)

/-- I passi interni non toccano la `extqueue`: quel che il programma vuole non cambia. -/
theorem extqueue_step_int {s t : MSIState n} {e : IEvent n} (h : step_int s e t) (i : Fin n) :
    (t.caches i).extqueue = (s.caches i).extqueue := by
  cases h with
  | cache _ j e hc =>
      by_cases hji : j = i
      · subst hji
        simp only [update_Fin_gss]
        cases hc <;> rfl
      · simp [update_Fin_gso _ _ _ _ hji]
  | parent_upd_queue _ e j hp =>
      by_cases hji : j = i
      · subst hji; simp [update_Fin_gss]
      · simp [update_Fin_gso _ _ _ _ hji]

theorem wantsM_step_int {s t : MSIState n} {e : IEvent n} (h : step_int s e t) {i : Fin n}
    (hw : wantsM (s.caches i)) : wantsM (t.caches i) := by
  unfold wantsM at *; rw [extqueue_step_int h i]; exact hw

theorem wantsS_step_int {s t : MSIState n} {e : IEvent n} (h : step_int s e t) {i : Fin n}
    (hw : wantsS (s.caches i)) : wantsS (t.caches i) := by
  unfold wantsS at *; rw [extqueue_step_int h i]; exact hw

/-! ## La guardia delle richieste si conserva

Se la cache `i` può chiedere in `s` (niente in sospeso, niente in volo) e un altro passo porta `s`
in `t`, allora può chiedere anche in `t`, a meno che il passo sia un grant verso `i`: ma un grant
verso `i` consuma una richiesta di `i`, che non c'è (le code sono allineate). -/

theorem pending_of_mem_eraseIdx {c : CacheState} {l : List CPEvent} {j : Nat}
    (h : ¬ pending c) (hl : c.queue_cp = l) :
    ¬ pending { c with queue_cp := l.eraseIdx j } := by
  intro hp
  apply h
  subst hl
  rcases hp with hp | hp
  · exact Or.inl (List.mem_of_mem_eraseIdx hp)
  · exact Or.inr (List.mem_of_mem_eraseIdx hp)

/-- Un passo di un'altra cache o del parent su un altro indice non tocca le code della cache `i`. -/
theorem queues_other {s t : MSIState n} {e : IEvent n} {i : Fin n} (h : step_int s e t)
    (hi : ∀ e' j, e = .cache e' j → j ≠ i) (hj : ∀ e' j, e = .parent e' j → j ≠ i) :
    (t.caches i).queue_cp = (s.caches i).queue_cp ∧ (t.caches i).queue_pc = (s.caches i).queue_pc := by
  cases h with
  | cache _ j e hc =>
      have := hi e j rfl
      simp [update_Fin_gso _ _ _ _ this]
  | parent_upd_queue _ e j hp =>
      have := hj e j rfl
      simp [update_Fin_gso _ _ _ _ this]

/-- La guardia delle richieste della cache `i` si conserva lungo un passo che non è un grant verso
`i` e non è un passo della cache `i` stessa; se è un grant verso `i`, le code allineate danno una
contraddizione con `¬ pending`. -/
theorem req_guard_preserved {s t : MSIState n} {e : IEvent n} {i : Fin n}
    (hsync : synced s) (h : step_int s e t)
    (hp : ¬ pending (s.caches i)) (hg : ¬ grantInFlight (s.caches i))
    (hi : ∀ e' , e ≠ .cache e' i) :
    ¬ pending (t.caches i) ∧ ¬ grantInFlight (t.caches i) := by
  cases h with
  | cache _ j e hc =>
      have hji : j ≠ i := fun hji => hi e (by rw [hji])
      simp only [update_Fin_gso _ _ _ _ hji]
      exact ⟨hp, hg⟩
  | parent_upd_queue p' e j hp' =>
      by_cases hji : j = i
      · subst hji
        obtain ⟨h1, h2⟩ := hsync j
        cases hp' with
        | downgrade_from_M_rq1 v _ k hk =>
            simp only [update_Fin_gss]
            refine ⟨?_, ?_⟩
            · intro hpend
              apply hp
              rcases hpend with hm | hm
              · exact Or.inl (h1 ▸ List.mem_of_mem_eraseIdx hm)
              · exact Or.inr (h1 ▸ List.mem_of_mem_eraseIdx hm)
            · intro hgi; apply hg; simpa [grantInFlight, h2] using hgi
        | downgrade_from_M_rq2 _ k hk =>
            simp only [update_Fin_gss]
            refine ⟨?_, ?_⟩
            · intro hpend
              apply hp
              rcases hpend with hm | hm
              · exact Or.inl (h1 ▸ List.mem_of_mem_eraseIdx hm)
              · exact Or.inr (h1 ▸ List.mem_of_mem_eraseIdx hm)
            · intro hgi; apply hg; simpa [grantInFlight, h2] using hgi
        | upgrade_to_M_data_avilable_rq1 _ k hk _ =>
            exact absurd (Or.inl (h1 ▸ List.mem_of_getElem? hk)) hp
        | upgrade_to_M_data_avilable_rq2 _ k hk _ _ =>
            exact absurd (Or.inr (h1 ▸ List.mem_of_getElem? hk)) hp
        | upgrade_to_M_invalid_all _ _ k hk _ =>
            simp only [update_Fin_gss]
            refine ⟨by simpa [pending, h1] using hp, ?_⟩
            intro hgi; apply hg
            simp only [grantInFlight, h2, List.mem_append, List.mem_singleton] at hgi ⊢
            rcases hgi with ⟨v, hv | hv⟩ | ⟨v, hv | hv⟩
            · exact Or.inl ⟨v, hv⟩
            · cases hv
            · exact Or.inr ⟨v, hv⟩
            · cases hv
        | upgrade_to_M_invalid_all1 _ _ k hk _ =>
            simp only [update_Fin_gss]
            refine ⟨by simpa [pending, h1] using hp, ?_⟩
            intro hgi; apply hg
            simp only [grantInFlight, h2, List.mem_append, List.mem_singleton] at hgi ⊢
            rcases hgi with ⟨v, hv | hv⟩ | ⟨v, hv | hv⟩
            · exact Or.inl ⟨v, hv⟩
            · cases hv
            · exact Or.inr ⟨v, hv⟩
            · cases hv
        | upgrade_to_M_invalid_all2 _ _ k hk _ _ =>
            simp only [update_Fin_gss]
            refine ⟨by simpa [pending, h1] using hp, ?_⟩
            intro hgi; apply hg
            simp only [grantInFlight, h2, List.mem_append, List.mem_singleton] at hgi ⊢
            rcases hgi with ⟨v, hv | hv⟩ | ⟨v, hv | hv⟩
            · exact Or.inl ⟨v, hv⟩
            · cases hv
            · exact Or.inr ⟨v, hv⟩
            · cases hv
        | upgrade_to_M_invalid_all3 _ _ k hk _ =>
            simp only [update_Fin_gss]
            refine ⟨by simpa [pending, h1] using hp, ?_⟩
            intro hgi; apply hg
            simp only [grantInFlight, h2, List.mem_append, List.mem_singleton] at hgi ⊢
            rcases hgi with ⟨v, hv | hv⟩ | ⟨v, hv | hv⟩
            · exact Or.inl ⟨v, hv⟩
            · cases hv
            · exact Or.inr ⟨v, hv⟩
            · cases hv
      · simp only [update_Fin_gso _ _ _ _ hji]
        exact ⟨hp, hg⟩


/-! ## Inversione delle richieste e degli scarti -/

/-- Le guardie di una richiesta di `M`. -/
theorem reqM_guards {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .upgrade_from_I_rq i) s') :
    (s.caches i).state = Bstate.I ∧ ¬ pending (s.caches i) ∧ ¬ grantInFlight (s.caches i) ∧
      wantsM (s.caches i) := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | upgrade_from_I_rq hI hp hg hw => exact ⟨hI, hp, hg, hw⟩

/-- Le guardie di una richiesta di `S`. -/
theorem reqS_guards {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .upgrade_from_I_rqS i) s') :
    (s.caches i).state = Bstate.I ∧ ¬ pending (s.caches i) ∧ ¬ grantInFlight (s.caches i) ∧
      wantsS (s.caches i) := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | upgrade_from_I_rq1 hI hp hg hw => exact ⟨hI, hp, hg, hw⟩

/-- Uno scarto di `rqIμ`: la cache è in `I` e il messaggio è in `queue_pc`. -/
theorem dropM_guards {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .drop_rqIμ i) s') :
    ∃ j : Nat, (s.caches i).state = Bstate.I ∧ ((s.caches i).queue_pc)[j]? = some PCEvent.rqIμ := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | drop_rqIμ j hj hI => exact ⟨j, hI, hj⟩

/-- Uno scarto di `rqIσ`. -/
theorem dropS_guards {s s' : MSIState n} {i : Fin n} (h : step_int s (.cache .drop_rqIσ i) s') :
    ∃ j : Nat, (s.caches i).state = Bstate.I ∧ ((s.caches i).queue_pc)[j]? = some PCEvent.rqIσ := by
  cases h with
  | cache _ _ _ hc =>
      cases hc with
      | drop_rqIσ j hj hI => exact ⟨j, hI, hj⟩

end MSITrial
