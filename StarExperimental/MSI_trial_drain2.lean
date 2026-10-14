import StarExperimental.MSI_trial_canon

/-!
# `MSI_trial`: svuotamento, tappe 3–4 e arrivo al canonico

Da `Quiet2` a `Quiet3` servendo ogni richiesta in volo (grant, presa, rilascio, consumo), poi ogni
cache con una richiesta del programma in testa acquisisce la linea e prende `m` (tappa 4). In fondo lo
stato è esattamente `canon x m` (`canon_of_drained`).
-/

open THEORY Relation MSIView
open ReachingStar (Rule trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Lemmi ausiliari: liste, `update_Fin`, un passo come `rule` -/

/-- Cancellare l'ultimo elemento di `l ++ [a]` ridà `l`. -/
theorem drain2_eraseIdx_concat {α : Type} (l : List α) (a : α) :
    (l ++ [a]).eraseIdx l.length = l := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.length_cons, List.eraseIdx_cons_succ, ih]

/-- Rimettere in `k` il valore che `f` ha già in `k` non cambia `f`. -/
theorem drain2_update_self {α : Type} {k : Fin n} {f : Fin n → α} {a : α} (h : f k = a) :
    update_Fin k a f = f := by
  subst h; exact update_Fin_self k f

/-- Un passo di cache come `rule`, con lo stato di arrivo dato esplicitamente. -/
theorem drain2_rule_cache {x y : MSIState n} (k : Fin n) {e : CEvent} {c' : CacheState}
    (h : cache_step (x.caches k) e c')
    (hy : y = { x with caches := update_Fin k c' x.caches,
                       parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                       parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci }) :
    rule n x y := by
  subst hy; exact ⟨.cache e k, step_int.cache x c' k e h⟩

/-- Un passo del parent come `rule`, con lo stato di arrivo dato esplicitamente. -/
theorem drain2_rule_parent {x y : MSIState n} (k : Fin n) {e : ParentUpdQueueInternalEvent n}
    {p' : ParentState n} (h : parent_msi_step x.parent (.upd_queue e k) p')
    (hy : y = { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                                queue_pc := p'.queue_pci k } x.caches,
                       parent := p' }) :
    rule n x y := by
  subst hy; exact ⟨.parent e k, step_int.parent_upd_queue x p' e k h⟩

/-- `active` dipende solo dalla cache. -/
theorem drain2_active_congr {x y : MSIState n} {i : Fin n} (h : y.caches i = x.caches i) :
    active y i ↔ active x i := by
  unfold active; rw [h]

/-- `Keeps` per un cammino che tocca solo la cache attiva `k`, lasciandole la `extqueue` e dandole il
valore `m`. -/
theorem drain2_keeps_of_local {x y : MSIState n} {k : Fin n} {m : Value}
    (hk : active x k) (hne : ∀ i, i ≠ k → y.caches i = x.caches i)
    (hext : (y.caches k).extqueue = (x.caches k).extqueue) (hv : (y.caches k).value = m) :
    Keeps x y m := by
  refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_, fun i => ?_⟩
  · by_cases h : i = k
    · subst h; exact hext
    · rw [hne i h]
  · by_cases h : i = k
    · subst h; exact absurd hk hi
    · rw [drain2_active_congr (hne i h)]; exact hi
  · by_cases h : i = k
    · subst h; exact absurd hk hi
    · rw [hne i h]
  · by_cases h : i = k
    · subst h; exact Or.inr hv
    · exact Or.inl (by rw [hne i h])

/-- `Quiet2` per uno stato che differisce da `x` solo nella cache `k`, che resta in `I`, non ha
nuovi messaggi in `queue_pc` e in `queue_cp` ha al più nuove richieste. -/
theorem drain2_quiet2_of {x y : MSIState n} {k : Fin n} (hq : Quiet2 x)
    (hc : ∀ i, i ≠ k → y.caches i = x.caches i)
    (hk : (y.caches k).state = Bstate.I)
    (hcp : ∀ e, e ∈ (y.caches k).queue_cp →
      e ∈ (x.caches k).queue_cp ∨ e = CPEvent.rqM ∨ e = CPEvent.rqS)
    (hpc : ∀ e, e ∈ (y.caches k).queue_pc → e ∈ (x.caches k).queue_pc)
    (hrows : ∀ i, y.parent.shared_state i = x.parent.shared_state i) : Quiet2 y := by
  obtain ⟨⟨q1, q2, q3, q4, q5, q6⟩, q7, q8⟩ := hq
  refine ⟨⟨fun i => ?_, fun i v hv => ?_, fun i v hv => ?_, fun i v hv => ?_, fun i hv => ?_,
    fun i => ?_⟩, fun i hv => ?_, fun i hv => ?_⟩
  · by_cases hi : i = k
    · subst hi; exact hk
    · rw [hc i hi]; exact q1 i
  · by_cases hi : i = k
    · subst hi; exact q2 i v (hpc _ hv)
    · rw [hc i hi] at hv; exact q2 i v hv
  · by_cases hi : i = k
    · subst hi; exact q3 i v (hpc _ hv)
    · rw [hc i hi] at hv; exact q3 i v hv
  · by_cases hi : i = k
    · subst hi
      rcases hcp _ hv with h | h | h
      · exact q4 i v h
      · cases h
      · cases h
    · rw [hc i hi] at hv; exact q4 i v hv
  · by_cases hi : i = k
    · subst hi
      rcases hcp _ hv with h | h | h
      · exact q5 i h
      · cases h
      · cases h
    · rw [hc i hi] at hv; exact q5 i hv
  · rw [hrows i]; exact q6 i
  · by_cases hi : i = k
    · subst hi; exact q7 i (hpc _ hv)
    · rw [hc i hi] at hv; exact q7 i hv
  · by_cases hi : i = k
    · subst hi; exact q8 i (hpc _ hv)
    · rw [hc i hi] at hv; exact q8 i hv

/-! ## Servire una richiesta: grant, presa, rilascio, consumo -/

/-- Lo stato dopo aver servito la richiesta in posizione `j` di `queue_cp k`: la cache `k` torna a
`I` con valore `m`, la richiesta è sparita, il resto delle sue code è quello di prima; il parent ha
valore `m`, le righe di prima (tutte `I`) e la copia di `queue_cp k` aggiornata. -/
def drain2_served (x : MSIState n) (k : Fin n) (j : Nat) (m : Value) : MSIState n :=
  ⟨update_Fin k ⟨Bstate.I, m, (x.caches k).queue_cp.eraseIdx j, (x.caches k).queue_pc,
      (x.caches k).extqueue⟩ x.caches,
   ⟨m, x.parent.shared_state, update_Fin k ((x.caches k).queue_cp.eraseIdx j) x.parent.queue_cip,
    x.parent.queue_pci⟩⟩

theorem drain2_served_caches_ne {x : MSIState n} {k i : Fin n} {j : Nat} {m : Value} (h : i ≠ k) :
    (drain2_served x k j m).caches i = x.caches i := by
  simp [drain2_served, update_Fin_gso2 _ _ _ _ h]

theorem drain2_served_caches_k {x : MSIState n} {k : Fin n} {j : Nat} {m : Value} :
    (drain2_served x k j m).caches k =
      ⟨Bstate.I, m, (x.caches k).queue_cp.eraseIdx j, (x.caches k).queue_pc,
       (x.caches k).extqueue⟩ := by
  simp [drain2_served]

/-- La richiesta `rqM` in posizione `j` viene servita in quattro passi: grant di `M`
(`upgrade_to_M_data_avilable_rq1`, righe tutte `I`), presa (`upgrade_from_I_rs`, ultima posizione di
`queue_pc k`), rilascio spontaneo (`rq_data_not_available`), consumo (`downgrade_from_M_rq1`, ultima
posizione di `queue_cip k`). Il valore passato è `parent.value`. -/
theorem drain2_serve_M {x : MSIState n} {k : Fin n} {j : Nat}
    (hI : (x.caches k).state = Bstate.I)
    (hcip : x.parent.queue_cip k = (x.caches k).queue_cp)
    (hpci : x.parent.queue_pci k = (x.caches k).queue_pc)
    (hrows : ∀ i, x.parent.shared_state i = Bstate.I)
    (hj : ((x.caches k).queue_cp)[j]? = some CPEvent.rqM) :
    trans_refl (rule n) x (drain2_served x k j x.parent.value) := by
  obtain ⟨cs, pv, rows, cip, pci⟩ := x
  change (cs k).state = Bstate.I at hI
  change cip k = (cs k).queue_cp at hcip
  change pci k = (cs k).queue_pc at hpci
  change ∀ i, rows i = Bstate.I at hrows
  change ((cs k).queue_cp)[j]? = some CPEvent.rqM at hj
  show trans_refl (rule n) ⟨cs, ⟨pv, rows, cip, pci⟩⟩
    ⟨update_Fin k ⟨Bstate.I, pv, (cs k).queue_cp.eraseIdx j, (cs k).queue_pc, (cs k).extqueue⟩ cs,
     ⟨pv, rows, update_Fin k ((cs k).queue_cp.eraseIdx j) cip, pci⟩⟩
  rcases hck : cs k with ⟨st, v0, cp, pc, ex⟩
  rw [hck] at hI hcip hpci hj
  have hst : st = Bstate.I := hI
  subst hst
  have hcip' : cip k = cp := hcip
  have hpci' : pci k = pc := hpci
  have hj' : cp[j]? = some CPEvent.rqM := hj
  -- 1. grant di `M`
  have s1 : rule n ⟨cs, ⟨pv, rows, cip, pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, v0, cp.eraseIdx j, pc ++ [PCEvent.rsM pv], ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j) cip,
        update_Fin k (pc ++ [PCEvent.rsM pv]) pci⟩⟩ :=
    drain2_rule_parent k
      (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ k j
        (by show (cip k)[j]? = some CPEvent.rqM; rw [hcip']; exact hj') (by exact hrows))
      (by simp [hck, hcip', hpci'])
  -- 2. presa del grant (ultima posizione di `queue_pc k`)
  have s2 : rule n
      ⟨update_Fin k ⟨Bstate.I, v0, cp.eraseIdx j, pc ++ [PCEvent.rsM pv], ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j) cip,
        update_Fin k (pc ++ [PCEvent.rsM pv]) pci⟩⟩
      ⟨update_Fin k ⟨Bstate.M, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩ :=
    drain2_rule_cache k
      (cache_step.upgrade_from_I_rs _ pv pc.length (by simp) (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_eraseIdx_concat, drain2_update_self hpci'])
  -- 3. rilascio spontaneo
  have s3 : rule n
      ⟨update_Fin k ⟨Bstate.M, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j ++ [CPEvent.rsIμ pv], pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j ++ [CPEvent.rsIμ pv]) cip,
        pci⟩⟩ :=
    drain2_rule_cache k (cache_step.rq_data_not_available _ (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_update_self hpci'])
  -- 4. consumo del rilascio (ultima posizione di `queue_cip k`)
  have s4 : rule n
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j ++ [CPEvent.rsIμ pv], pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.M rows, update_Fin k (cp.eraseIdx j ++ [CPEvent.rsIμ pv]) cip,
        pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩ :=
    drain2_rule_parent k
      (parent_msi_step.downgrade_from_M_rq1 _ pv k (cp.eraseIdx j).length
        (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_eraseIdx_concat, hpci',
                drain2_update_self (hrows k)])
  exact trans_refl.step s1 (trans_refl.step s2 (trans_refl.step s3
    (trans_refl.step s4 trans_refl.refl)))

/-- La richiesta `rqS` in posizione `j` viene servita in quattro passi: grant di `S`
(`upgrade_to_M_data_avilable_rq2`: riga `k` a `I`, nessuna riga `M`), presa (`upgrade_from_I_rsS`),
rilascio spontaneo (`rq_data_not_available1`), consumo (`downgrade_from_M_rq2`). -/
theorem drain2_serve_S {x : MSIState n} {k : Fin n} {j : Nat}
    (hI : (x.caches k).state = Bstate.I)
    (hcip : x.parent.queue_cip k = (x.caches k).queue_cp)
    (hpci : x.parent.queue_pci k = (x.caches k).queue_pc)
    (hrows : ∀ i, x.parent.shared_state i = Bstate.I)
    (hj : ((x.caches k).queue_cp)[j]? = some CPEvent.rqS) :
    trans_refl (rule n) x (drain2_served x k j x.parent.value) := by
  obtain ⟨cs, pv, rows, cip, pci⟩ := x
  change (cs k).state = Bstate.I at hI
  change cip k = (cs k).queue_cp at hcip
  change pci k = (cs k).queue_pc at hpci
  change ∀ i, rows i = Bstate.I at hrows
  change ((cs k).queue_cp)[j]? = some CPEvent.rqS at hj
  show trans_refl (rule n) ⟨cs, ⟨pv, rows, cip, pci⟩⟩
    ⟨update_Fin k ⟨Bstate.I, pv, (cs k).queue_cp.eraseIdx j, (cs k).queue_pc, (cs k).extqueue⟩ cs,
     ⟨pv, rows, update_Fin k ((cs k).queue_cp.eraseIdx j) cip, pci⟩⟩
  rcases hck : cs k with ⟨st, v0, cp, pc, ex⟩
  rw [hck] at hI hcip hpci hj
  have hst : st = Bstate.I := hI
  subst hst
  have hcip' : cip k = cp := hcip
  have hpci' : pci k = pc := hpci
  have hj' : cp[j]? = some CPEvent.rqS := hj
  -- 1. grant di `S`
  have s1 : rule n ⟨cs, ⟨pv, rows, cip, pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, v0, cp.eraseIdx j, pc ++ [PCEvent.rsS pv], ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j) cip,
        update_Fin k (pc ++ [PCEvent.rsS pv]) pci⟩⟩ :=
    drain2_rule_parent k
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ k j
        (by show (cip k)[j]? = some CPEvent.rqS; rw [hcip']; exact hj') (by exact hrows k)
        (by intro i; show ¬ rows i = Bstate.M; rw [hrows i]; intro h; cases h))
      (by simp [hck, hcip', hpci'])
  -- 2. presa del grant
  have s2 : rule n
      ⟨update_Fin k ⟨Bstate.I, v0, cp.eraseIdx j, pc ++ [PCEvent.rsS pv], ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j) cip,
        update_Fin k (pc ++ [PCEvent.rsS pv]) pci⟩⟩
      ⟨update_Fin k ⟨Bstate.S, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩ :=
    drain2_rule_cache k
      (cache_step.upgrade_from_I_rsS _ pv pc.length (by simp) (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_eraseIdx_concat, drain2_update_self hpci'])
  -- 3. rilascio spontaneo
  have s3 : rule n
      ⟨update_Fin k ⟨Bstate.S, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j ++ [CPEvent.rsIσ], pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j ++ [CPEvent.rsIσ]) cip, pci⟩⟩ :=
    drain2_rule_cache k (cache_step.rq_data_not_available1 _ (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_update_self hpci'])
  -- 4. consumo del rilascio
  have s4 : rule n
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j ++ [CPEvent.rsIσ], pc, ex⟩ cs,
       ⟨pv, update_Fin k Bstate.S rows, update_Fin k (cp.eraseIdx j ++ [CPEvent.rsIσ]) cip, pci⟩⟩
      ⟨update_Fin k ⟨Bstate.I, pv, cp.eraseIdx j, pc, ex⟩ cs,
       ⟨pv, rows, update_Fin k (cp.eraseIdx j) cip, pci⟩⟩ :=
    drain2_rule_parent k
      (parent_msi_step.downgrade_from_M_rq2 _ k (cp.eraseIdx j).length
        (by simp))
      (by simp [update_Fin_update_Fin_same, drain2_eraseIdx_concat, hpci',
                drain2_update_self (hrows k)])
  exact trans_refl.step s1 (trans_refl.step s2 (trans_refl.step s3
    (trans_refl.step s4 trans_refl.refl)))

/-- **Servire una richiesta.** Da `Quiet2` con `Reach` e `flush`, una richiesta (`rqM` o `rqS`) in
posizione `j` di `queue_cp k` viene servita in quattro passi; il valore preso è `parent.value`, che è
`s.memory` (clausola 7 di `flush`: nessuna riga è `M`). -/
theorem drain2_serve {x : MSIState n} {s : SeqState n} {k : Fin n} {j : Nat}
    (hr : Reach x) (hf : flush x s) (hq : Quiet2 x)
    (hj : ((x.caches k).queue_cp)[j]? = some CPEvent.rqM ∨
          ((x.caches k).queue_cp)[j]? = some CPEvent.rqS) :
    trans_refl (rule n) x (drain2_served x k j s.memory) := by
  have hsync := synced_of_reach hr
  have hpv : x.parent.value = s.memory :=
    hf.2.2.2.2.2.2 fun i => by rw [hq.1.2.2.2.2.2 i]; intro h; cases h
  rw [← hpv]
  rcases hj with hj | hj
  · exact drain2_serve_M (hq.1.1 k) (hsync k).1 (hsync k).2 hq.1.2.2.2.2.2 hj
  · exact drain2_serve_S (hq.1.1 k) (hsync k).1 (hsync k).2 hq.1.2.2.2.2.2 hj

theorem drain2_served_quiet2 {x : MSIState n} {k : Fin n} {j : Nat} {m : Value} (hq : Quiet2 x) :
    Quiet2 (drain2_served x k j m) :=
  drain2_quiet2_of (k := k) hq (fun i hi => drain2_served_caches_ne hi)
    (by rw [drain2_served_caches_k])
    (fun e he => by
      rw [drain2_served_caches_k] at he
      exact Or.inl (List.mem_of_mem_eraseIdx he))
    (fun e he => by rw [drain2_served_caches_k] at he; exact he)
    (fun i => rfl)

theorem drain2_served_keeps {x : MSIState n} {k : Fin n} {j : Nat} {m : Value} (hk : active x k) :
    Keeps x (drain2_served x k j m) m :=
  drain2_keeps_of_local hk (fun i hi => drain2_served_caches_ne hi)
    (by rw [drain2_served_caches_k]) (by rw [drain2_served_caches_k])

/-- Servire la richiesta in posizione `j` fa calare `nReq` di uno. -/
theorem drain2_served_nReq {x : MSIState n} {k : Fin n} {j : Nat} {m : Value}
    (hj : ((x.caches k).queue_cp)[j]? = some CPEvent.rqM ∨
          ((x.caches k).queue_cp)[j]? = some CPEvent.rqS) :
    nReq ((drain2_served x k j m).caches k) + 1 = nReq (x.caches k) := by
  rw [drain2_served_caches_k]
  unfold nReq
  rcases hj with hj | hj
  · exact countP_eraseIdx _ _ _ _ hj
  · exact countP_eraseIdx _ _ _ _ hj

/-! ## Somme su `List.finRange` -/

theorem drain2_sum_le {f g : Fin n → Nat} (hle : ∀ i, g i ≤ f i) (l : List (Fin n)) :
    (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle a) ih

theorem drain2_sum_lt {f g : Fin n → Nat} (hle : ∀ i, g i ≤ f i) (l : List (Fin n)) (k : Fin n)
    (hk : k ∈ l) (hlt : g k < f k) : (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => cases hk
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hk with h | h
    · subst h
      have := drain2_sum_le hle l
      omega
    · have := ih h
      have := hle a
      omega

/-- Numero totale di richieste in volo. -/
def drain2_nreqs (x : MSIState n) : Nat :=
  ((List.finRange n).map fun k => nReq (x.caches k)).sum

/-! ## Tappa 3 -/

/-- **Tappa 3**: ogni richiesta in volo viene servita (grant, presa, rilascio, consumo): la cache
prende `m` e torna a `I`. -/
theorem drain_requests {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    (hq : Quiet2 x) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Keeps x y s.memory := by
  suffices h : ∀ N (x : MSIState n), drain2_nreqs x = N → Reach x → flush x s → Quiet2 x →
      ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Keeps x y s.memory from h _ x rfl hr hf hq
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih x hN hr hf hq
  by_cases hp : ∃ k, pending (x.caches k)
  · obtain ⟨k, hk⟩ := hp
    have hj : ∃ j : Nat, ((x.caches k).queue_cp)[j]? = some CPEvent.rqM ∨
        ((x.caches k).queue_cp)[j]? = some CPEvent.rqS := by
      rcases hk with h | h
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
        exact ⟨j, Or.inl hj⟩
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
        exact ⟨j, Or.inr hj⟩
    obtain ⟨j, hj⟩ := hj
    have hstep := drain2_serve hr hf hq hj
    have hr' := reach_trans hr hstep
    have hf' := flush_trans hf hstep
    have hq' : Quiet2 (drain2_served x k j s.memory) := drain2_served_quiet2 hq
    have hlt : drain2_nreqs (drain2_served x k j s.memory) < N := by
      rw [← hN]
      unfold drain2_nreqs
      refine drain2_sum_lt (fun i => ?_) _ k (List.mem_finRange k) ?_
      · by_cases hi : i = k
        · subst hi
          have := drain2_served_nReq (m := s.memory) hj
          omega
        · rw [drain2_served_caches_ne hi]
      · have := drain2_served_nReq (m := s.memory) hj
        omega
    obtain ⟨y, hy1, hy2, hy3⟩ := ih _ hlt _ rfl hr' hf' hq'
    exact ⟨y, ReachingStar.trans_refl_trans hstep hy1, hy2,
      Keeps.trans (drain2_served_keeps (Or.inr (Or.inl hk))) hy3⟩
  · push Not at hp
    exact ⟨x, trans_refl.refl, ⟨hq, hp⟩, Keeps.refl x _⟩

/-! ## Tappa 4 -/

/-- Dopo una richiesta `e ∈ {rqM, rqS}` della cache `k` (da `Quiet3`), servirla porta in uno stato
`Quiet3` in cui `k` ha valore `m` e tutto il resto è come in `x`. -/
theorem drain2_after_request {x x1 : MSIState n} {s : SeqState n} {k : Fin n} {e : CPEvent}
    (hr : Reach x) (hf : flush x s) (hq : Quiet3 x) (he : e = CPEvent.rqM ∨ e = CPEvent.rqS)
    (h1 : rule n x x1)
    (hc1 : ∀ i, i ≠ k → x1.caches i = x.caches i)
    (hk1 : x1.caches k = { x.caches k with queue_cp := (x.caches k).queue_cp ++ [e] })
    (hp1 : ∀ i, x1.parent.shared_state i = x.parent.shared_state i) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Reach y ∧ flush y s ∧
      (∀ i, i ≠ k → y.caches i = x.caches i) ∧
      y.caches k = { x.caches k with value := s.memory } := by
  obtain ⟨hq2, hnp⟩ := hq
  have hI : (x.caches k).state = Bstate.I := hq2.1.1 k
  have hr1 : Reach x1 := reach_step hr h1
  have hf1 : flush x1 s := by
    obtain ⟨ev, hev⟩ := h1
    exact flush_step_int hf hev
  have hq1 : Quiet2 x1 :=
    drain2_quiet2_of (k := k) hq2 hc1 (by rw [hk1]; exact hI)
      (fun e' he' => by
        rw [hk1] at he'
        rcases List.mem_append.mp he' with h | h
        · exact Or.inl h
        · obtain rfl := List.mem_singleton.mp h
          exact Or.inr he)
      (fun e' he' => by rw [hk1] at he'; exact he') hp1
  have hj1 : ((x1.caches k).queue_cp)[(x.caches k).queue_cp.length]? = some CPEvent.rqM ∨
      ((x1.caches k).queue_cp)[(x.caches k).queue_cp.length]? = some CPEvent.rqS := by
    rw [hk1]
    rcases he with rfl | rfl
    · exact Or.inl List.getElem?_concat_length
    · exact Or.inr List.getElem?_concat_length
  have hstep := drain2_serve hr1 hf1 hq1 hj1
  have hyk : (drain2_served x1 k (x.caches k).queue_cp.length s.memory).caches k
      = { x.caches k with value := s.memory } := by
    rw [drain2_served_caches_k, hk1]
    simp [drain2_eraseIdx_concat, hI]
  have hyne : ∀ i, i ≠ k →
      (drain2_served x1 k (x.caches k).queue_cp.length s.memory).caches i = x.caches i :=
    fun i hi => (drain2_served_caches_ne hi).trans (hc1 i hi)
  refine ⟨_, ReachingStar.trans_refl_trans (trans_refl.step h1 trans_refl.refl) hstep,
    ⟨drain2_served_quiet2 hq1, fun i => ?_⟩, reach_trans hr1 hstep, flush_trans hf1 hstep,
    hyne, hyk⟩
  by_cases hi : i = k
  · subst hi; rw [hyk]; exact hnp i
  · rw [hyne i hi]; exact hnp i

/-- Una cache con una richiesta del programma in testa, da `Quiet3`, chiede la linea
(`upgrade_from_I_rq`/`rq1`) e viene servita: prende `m`, il resto non cambia, `Quiet3` è
ripristinato. -/
theorem drain2_demand_step {x : MSIState n} {s : SeqState n} {k : Fin n}
    (hr : Reach x) (hf : flush x s) (hq : Quiet3 x)
    (hw : wantsM (x.caches k) ∨ wantsS (x.caches k)) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Reach y ∧ flush y s ∧
      (∀ i, i ≠ k → y.caches i = x.caches i) ∧
      y.caches k = { x.caches k with value := s.memory } := by
  have hI : (x.caches k).state = Bstate.I := hq.1.1.1 k
  have hnp : ¬ pending (x.caches k) := hq.2 k
  have hng : ¬ grantInFlight (x.caches k) := by
    rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact hq.1.1.2.1 k v hv
    · exact hq.1.1.2.2.1 k v hv
  rcases hw with hw | hw
  · exact drain2_after_request hr hf hq (Or.inl rfl)
      ⟨_, step_int.cache x _ k _ (cache_step.upgrade_from_I_rq _ hI hnp hng hw)⟩
      (fun i hi => by simp [update_Fin_gso2 _ _ _ _ hi]) (by simp) (by intro i; exact rfl)
  · exact drain2_after_request hr hf hq (Or.inr rfl)
      ⟨_, step_int.cache x _ k _ (cache_step.upgrade_from_I_rq1 _ hI hnp hng hw)⟩
      (fun i hi => by simp [update_Fin_gso2 _ _ _ _ hi]) (by simp) (by intro i; exact rfl)

open Classical in
/-- Numero di cache con una richiesta del programma in testa e valore diverso da `m`. -/
noncomputable def drain2_dem (x : MSIState n) (m : Value) : Nat :=
  ((List.finRange n).map fun k =>
    if (wantsM (x.caches k) ∨ wantsS (x.caches k)) ∧ (x.caches k).value ≠ m then 1 else 0).sum

/-- **Tappa 4**: ogni cache con una richiesta del programma in testa e valore diverso da `m`
acquisisce la linea (richiesta, grant, presa, rilascio, consumo) e prende `m`. -/
theorem drain_demands {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    (hq : Quiet3 x) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Keeps x y s.memory ∧
      (∀ k, wantsM (x.caches k) ∨ wantsS (x.caches k) → (y.caches k).value = s.memory) := by
  suffices h : ∀ N (x : MSIState n), drain2_dem x s.memory = N → Reach x → flush x s → Quiet3 x →
      ∃ y, trans_refl (rule n) x y ∧ Quiet3 y ∧ Keeps x y s.memory ∧
        (∀ k, wantsM (x.caches k) ∨ wantsS (x.caches k) → (y.caches k).value = s.memory) from
    h _ x rfl hr hf hq
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih x hN hr hf hq
  by_cases hex : ∃ k, (wantsM (x.caches k) ∨ wantsS (x.caches k)) ∧ (x.caches k).value ≠ s.memory
  · obtain ⟨k, hw, hv⟩ := hex
    obtain ⟨y₁, hy1, hq1, hr1, hf1, hne, hk⟩ := drain2_demand_step hr hf hq hw
    have hlt : drain2_dem y₁ s.memory < N := by
      rw [← hN]
      unfold drain2_dem
      refine drain2_sum_lt (fun i => ?_) _ k (List.mem_finRange k) ?_
      · by_cases hi : i = k
        · subst hi; rw [hk]; simp
        · rw [hne i hi]
      · rw [hk]; simp [hw, hv]
    obtain ⟨y, hy2, hq2, hk2, hd2⟩ := ih _ hlt y₁ rfl hr1 hf1 hq1
    refine ⟨y, ReachingStar.trans_refl_trans hy1 hy2, hq2,
      Keeps.trans (drain2_keeps_of_local (Or.inr (Or.inr (Or.inr hw))) hne (by rw [hk])
        (by rw [hk])) hk2, fun i hwi => hd2 i ?_⟩
    have hext : (y₁.caches i).extqueue = (x.caches i).extqueue := by
      by_cases hi : i = k
      · subst hi; rw [hk]
      · rw [hne i hi]
    unfold wantsM wantsS at hwi ⊢
    rw [hext]; exact hwi
  · push Not at hex
    exact ⟨x, trans_refl.refl, hq, Keeps.refl x _, fun k hw => hex k hw⟩

/-! ## Arrivo al canonico -/

/-- Lo stato in fondo allo svuotamento è il canonico. -/
theorem canon_of_drained {x y : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    (hry : Reach y) (hfy : flush y s) (hq : Quiet3 y) (hk : Keeps x y s.memory)
    (hd : ∀ k, wantsM (x.caches k) ∨ wantsS (x.caches k) → (y.caches k).value = s.memory)
    (hdem : demandOK x) : y = canon x s.memory := by
  obtain ⟨⟨⟨q1, q2, q3, q4, q5, q6⟩, q7, q8⟩, q9⟩ := hq
  have hsync := synced_of_reach hry
  -- code vuote: ogni evento è escluso da `Quiet3`
  have hcp : ∀ k, (y.caches k).queue_cp = [] := fun k =>
    List.eq_nil_iff_forall_not_mem.mpr fun e he => by
      cases e with
      | rsIμ v => exact q4 k v he
      | rsIσ => exact q5 k he
      | rqS => exact q9 k (Or.inr he)
      | rqM => exact q9 k (Or.inl he)
  have hpc : ∀ k, (y.caches k).queue_pc = [] := fun k =>
    List.eq_nil_iff_forall_not_mem.mpr fun e he => by
      cases e with
      | rqIμ => exact q7 k he
      | rqIσ => exact q8 k he
      | rsM v => exact q2 k v he
      | rsS v => exact q3 k v he
  -- il valore di una cache attiva è `m`
  have hvalA : ∀ k, active x k → (y.caches k).value = s.memory := by
    intro k ha
    rcases ha with h | h | h | h | h
    · have hx : (x.caches k).value = s.memory := hf.2.2.1 k h
      rcases hk.2.2.2 k with h' | h'
      · rw [h', hx]
      · exact h'
    · exact hd k ((hdem k).1 (Or.inl h))
    · exact hd k ((hdem k).1 (Or.inr h))
    · exact hd k (Or.inl h)
    · exact hd k (Or.inr h)
  unfold canon
  refine MSIState.ext_all (fun k => ?_) ?_ (fun k => q6 k) (fun k => ?_) (fun k => ?_)
  · dsimp only
    rcases hyk : y.caches k with ⟨st, v, cp, pc, ex⟩
    have e1 : st = Bstate.I := by have := q1 k; rw [hyk] at this; exact this
    have e3 : cp = [] := by have := hcp k; rw [hyk] at this; exact this
    have e4 : pc = [] := by have := hpc k; rw [hyk] at this; exact this
    have e5 : ex = (x.caches k).extqueue := by have := hk.1 k; rw [hyk] at this; exact this
    subst e1 e3 e4 e5
    by_cases ha : active x k
    · rw [if_pos ha]
      have := hvalA k ha
      rw [hyk] at this
      have e2 : v = s.memory := this
      subst e2; rfl
    · rw [if_neg ha]
      have := hk.2.2.1 k ha
      rw [hyk] at this
      have e2 : v = (x.caches k).value := this
      subst e2; rfl
  · exact hfy.2.2.2.2.2.2 fun k => by rw [q6 k]; intro h; cases h
  · show y.parent.queue_cip k = []
    rw [(hsync k).1]; exact hcp k
  · show y.parent.queue_pci k = []
    rw [(hsync k).2]; exact hpc k

end MSITrial
