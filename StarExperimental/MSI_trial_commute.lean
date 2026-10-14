import StarExperimental.MSI_trial_drain1
import StarExperimental.MSI_trial_drain2

/-!
# `MSI_trial`: la commutazione metodo–regola

`reach_canon` mette insieme le quattro tappe; `acquire_S`/`acquire_M` prendono la linea da uno stato
canonico; `step_int_enqueue` fa commutare i passi interni con l'accodamento di una richiesta del
programma; `msi_trial_commutes_upto` è `commutes_method_rule_upto_on` di ARS: per le load/store si
passa per il canonico (`j := canon c m`), per gli accodamenti si ripercorre il cammino.
-/

open THEORY Relation MSIView
open ReachingStar (Rule trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Lemmi ausiliari: trasporto lungo uguaglianze -/

theorem comm_step_int_eq {a b b' : MSIState n} {e : IEvent n} (h : step_int a e b) (heq : b = b') :
    step_int a e b' := heq ▸ h

theorem comm_refl_of_eq {a b : MSIState n} (h : a = b) : trans_refl (rule n) a b := h ▸ trans_refl.refl

/-! ## La forma di ogni passo di cache (interno o esterno) e di ogni passo del parent -/

/-- `x` con la cache `k` sostituita da `c` e le copie del parent riallineate: la forma del risultato
di `step_int.cache` e di `msi_step_external.cache`. -/
def comm_extSt (x : MSIState n) (k : Fin n) (c : CacheState) : MSIState n :=
  { x with caches := update_Fin k c x.caches,
           parent.queue_cip := update_Fin k c.queue_cp x.parent.queue_cip,
           parent.queue_pci := update_Fin k c.queue_pc x.parent.queue_pci }

/-- La forma del risultato di `step_int.parent_upd_queue`. -/
def comm_parSt (x : MSIState n) (p : ParentState n) (i : Fin n) : MSIState n :=
  { x with caches := update_Fin i { x.caches i with queue_cp := p.queue_cip i,
                                                    queue_pc := p.queue_pci i } x.caches,
           parent := p }

/-- La cache dopo l'accodamento di una richiesta del programma. -/
def comm_enqC (c : CacheState) (ev : Event) : CacheState :=
  { c with extqueue.rq := c.extqueue.rq ++ [ev] }

/-- La cache dopo aver servito una load. -/
def comm_ldC (c : CacheState) (v : Value) (rst : List Event) : CacheState :=
  { c with extqueue.rs := c.extqueue.rs ++ [Event.ld_rs v], extqueue.rq := rst }

/-- La cache dopo aver servito una store. -/
def comm_stC (c : CacheState) (v : Value) (rst : List Event) : CacheState :=
  { c with value := v, extqueue.rs := c.extqueue.rs ++ [Event.st_rs], extqueue.rq := rst }

@[simp] theorem comm_extSt_caches_self {x : MSIState n} {k : Fin n} {c : CacheState} :
    (comm_extSt x k c).caches k = c := by simp [comm_extSt]

theorem comm_extSt_caches_other {x : MSIState n} {k j : Fin n} {c : CacheState} (h : j ≠ k) :
    (comm_extSt x k c).caches j = x.caches j := by simp [comm_extSt, update_Fin_gso2 _ _ _ _ h]

theorem comm_extSt_extSt {x : MSIState n} {k : Fin n} {c c' : CacheState} :
    comm_extSt (comm_extSt x k c) k c' = comm_extSt x k c' := by
  refine MSIState.ext_all (fun j => ?_) rfl (fun j => rfl) (fun j => ?_) (fun j => ?_) <;>
  · by_cases hjk : j = k
    · subst hjk; simp [comm_extSt]
    · simp [comm_extSt, update_Fin_gso2 _ _ _ _ hjk]

theorem comm_extSt_comm {x : MSIState n} {i k : Fin n} {c c' : CacheState} (h : i ≠ k) :
    comm_extSt (comm_extSt x k c) i c' = comm_extSt (comm_extSt x i c') k c := by
  refine MSIState.ext_all (fun j => ?_) rfl (fun j => rfl) (fun j => ?_) (fun j => ?_) <;>
  · by_cases hji : j = i
    · subst hji; simp [comm_extSt, update_Fin_gso2 _ _ _ _ h]
    · by_cases hjk : j = k
      · subst hjk; simp [comm_extSt, update_Fin_gso2 _ _ _ _ hji]
      · simp [comm_extSt, update_Fin_gso2 _ _ _ _ hji, update_Fin_gso2 _ _ _ _ hjk]

/-- Se la cache sostituita ha le stesse code, il parent non cambia (code allineate). -/
theorem comm_extSt_parent {x : MSIState n} {k : Fin n} {c : CacheState} (hs : synced x)
    (h1 : c.queue_cp = (x.caches k).queue_cp) (h2 : c.queue_pc = (x.caches k).queue_pc) :
    (comm_extSt x k c).parent = x.parent := by
  have e1 : update_Fin k c.queue_cp x.parent.queue_cip = x.parent.queue_cip := by
    funext j; by_cases hjk : j = k
    · subst hjk; rw [update_Fin_gss, h1, (hs _).1]
    · rw [update_Fin_gso2 _ _ _ _ hjk]
  have e2 : update_Fin k c.queue_pc x.parent.queue_pci = x.parent.queue_pci := by
    funext j; by_cases hjk : j = k
    · subst hjk; rw [update_Fin_gss, h2, (hs _).2]
    · rw [update_Fin_gso2 _ _ _ _ hjk]
  show ({ x.parent with queue_cip := update_Fin k c.queue_cp x.parent.queue_cip,
                        queue_pci := update_Fin k c.queue_pc x.parent.queue_pci } : ParentState n)
       = x.parent
  rw [e1, e2]

/-! ## Svuotamento -/

/-- **Svuotamento**: ogni stato raggiungibile arriva al suo canonico con passi interni. -/
theorem reach_canon {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s) :
    trans_refl (rule n) x (canon x s.memory) := by
  obtain ⟨y1, h1, q1, k1⟩ := drain_tokens hr hf
  have hr1 := reach_trans hr h1
  have hf1 := flush_trans hf h1
  obtain ⟨y2, h2, q2, k2⟩ := drain_invalidates hr1 hf1 q1
  have hr2 := reach_trans hr1 h2
  have hf2 := flush_trans hf1 h2
  obtain ⟨y3, h3, q3, k3⟩ := drain_requests hr2 hf2 q2
  have hr3 := reach_trans hr2 h3
  have hf3 := flush_trans hf2 h3
  obtain ⟨y4, h4, q4, k4, hd4⟩ := drain_demands hr3 hf3 q3
  have hr4 := reach_trans hr3 h4
  have hf4 := flush_trans hf3 h4
  have hpath : trans_refl (rule n) x y4 :=
    ReachingStar.trans_refl_trans h1 (ReachingStar.trans_refl_trans h2
      (ReachingStar.trans_refl_trans h3 h4))
  have hk13 : Keeps x y3 s.memory := Keeps.trans k1 (Keeps.trans k2 k3)
  have hk : Keeps x y4 s.memory := Keeps.trans hk13 k4
  have hd : ∀ k, wantsM (x.caches k) ∨ wantsS (x.caches k) → (y4.caches k).value = s.memory := by
    intro k hw
    apply hd4 k
    have he := hk13.1 k
    rcases hw with ⟨v, rst, h⟩ | ⟨rst, h⟩
    · exact Or.inl ⟨v, rst, by rw [he]; exact h⟩
    · exact Or.inr ⟨rst, by rw [he]; exact h⟩
  have := canon_of_drained hr hf hr4 hf4 q4 hk hd (demandOK_of_reach hr)
  rw [← this]; exact hpath

/-! ## Dal canonico alla linea -/

/-- Da uno stato canonico, una cache con una load in testa prende `S` (richiesta, grant, presa): le
altre cache non cambiano, e dallo stato ottenuto si torna al canonico (rilascio, consumo). -/
theorem acquire_S {x : MSIState n} {m : Value} {k : Fin n} (hr : Reach (canon x m))
    (hw : wantsS (x.caches k)) :
    ∃ y, trans_refl (rule n) (canon x m) y ∧ (y.caches k).state = Bstate.S ∧
      (y.caches k).value = m ∧ (y.caches k).extqueue = (x.caches k).extqueue ∧
      (∀ j, j ≠ k → y.caches j = (canon x m).caches j) ∧
      trans_refl (rule n) y (canon x m) := by
  have hact : active x k := Or.inr (Or.inr (Or.inr (Or.inr hw)))
  refine ⟨_, trans_refl.step ⟨_, step_int.cache _ _ k _
      (cache_step.upgrade_from_I_rq1 ((canon x m).caches k) ?g1 ?g2 ?g3 ?g4)⟩
    (trans_refl.step ⟨_, step_int.parent_upd_queue _ _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ k 0 ?g5 ?g6 ?g7)⟩
    (trans_refl.step ⟨_, step_int.cache _ _ k _
      (cache_step.upgrade_from_I_rsS _ m 0 ?g8 ?g9)⟩ trans_refl.refl)), ?p1, ?p2, ?p3, ?p4, ?back⟩
  case g1 => rfl
  case g2 => simp [pending, canon]
  case g3 => simp [grantInFlight, canon]
  case g4 => obtain ⟨rst, h⟩ := hw; exact ⟨rst, h⟩
  case g5 => simp [canon]
  case g6 => simp [canon]
  case g7 => simp [canon]
  case g8 => simp [canon]
  case g9 => simp [canon]
  case p1 => simp
  case p2 => simp
  case p3 => simp [canon]
  case p4 => intro j hj; simp [update_Fin_gso2 _ _ _ _ hj]
  case back =>
    refine trans_refl.step ⟨_, step_int.cache _ _ k _ (cache_step.rq_data_not_available1 _ ?b1)⟩
      (trans_refl.step ⟨_, step_int.parent_upd_queue _ _ _ k
        (parent_msi_step.downgrade_from_M_rq2 _ k 0 ?b2)⟩ ?b3)
    case b1 => simp
    case b2 => simp [canon]
    case b3 =>
      refine comm_refl_of_eq (MSIState.ext_all (fun j => ?_) ?_ (fun j => ?_) (fun j => ?_) (fun j => ?_))
      · by_cases hj : j = k
        · subst hj; simp [canon, hact]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · rfl
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]

/-- Da uno stato canonico, una cache con una store in testa prende `M`. -/
theorem acquire_M {x : MSIState n} {m : Value} {k : Fin n} (hr : Reach (canon x m))
    (hw : wantsM (x.caches k)) :
    ∃ y, trans_refl (rule n) (canon x m) y ∧ (y.caches k).state = Bstate.M ∧
      (y.caches k).value = m ∧ (y.caches k).extqueue = (x.caches k).extqueue ∧
      (∀ j, j ≠ k → y.caches j = (canon x m).caches j) ∧
      trans_refl (rule n) y (canon x m) := by
  have hact : active x k := Or.inr (Or.inr (Or.inr (Or.inl hw)))
  refine ⟨_, trans_refl.step ⟨_, step_int.cache _ _ k _
      (cache_step.upgrade_from_I_rq ((canon x m).caches k) ?g1 ?g2 ?g3 ?g4)⟩
    (trans_refl.step ⟨_, step_int.parent_upd_queue _ _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ k 0 ?g5 ?g6)⟩
    (trans_refl.step ⟨_, step_int.cache _ _ k _
      (cache_step.upgrade_from_I_rs _ m 0 ?g8 ?g9)⟩ trans_refl.refl)), ?p1, ?p2, ?p3, ?p4, ?back⟩
  case g1 => rfl
  case g2 => simp [pending, canon]
  case g3 => simp [grantInFlight, canon]
  case g4 => obtain ⟨v, rst, h⟩ := hw; exact ⟨v, rst, h⟩
  case g5 => simp [canon]
  case g6 => simp [canon]
  case g8 => simp [canon]
  case g9 => simp [canon]
  case p1 => simp
  case p2 => simp
  case p3 => simp [canon]
  case p4 => intro j hj; simp [update_Fin_gso2 _ _ _ _ hj]
  case back =>
    refine trans_refl.step ⟨_, step_int.cache _ _ k _ (cache_step.rq_data_not_available _ ?b1)⟩
      (trans_refl.step ⟨_, step_int.parent_upd_queue _ _ _ k
        (parent_msi_step.downgrade_from_M_rq1 _ m k 0 ?b2)⟩ ?b3)
    case b1 => simp
    case b2 => simp [canon]
    case b3 =>
      refine comm_refl_of_eq (MSIState.ext_all (fun j => ?_) ?_ (fun j => ?_) (fun j => ?_) (fun j => ?_))
      · by_cases hj : j = k
        · subst hj; simp [canon, hact]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · rfl
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]
      · by_cases hj : j = k
        · subst hj; simp [canon]
        · simp [canon, update_Fin_gso2 _ _ _ _ hj]

/-! ## La commutazione metodo–regola a meno di passi interni -/

/-- Un passo di cache non legge la `extqueue` se non per la testa, che un accodamento non cambia. -/
theorem comm_cache_step_enq {c c' : CacheState} {ce : CEvent} {ev : Event} (h : cache_step c ce c') :
    cache_step (comm_enqC c ev) ce (comm_enqC c' ev) := by
  cases h with
  | rq_data_not_available hM => exact cache_step.rq_data_not_available _ hM
  | rq_data_not_available1 hS => exact cache_step.rq_data_not_available1 _ hS
  | upgrade_from_I_rq hI hp hg hw =>
      obtain ⟨v, rst, hv⟩ := hw
      exact cache_step.upgrade_from_I_rq _ hI hp hg
        ⟨v, rst ++ [ev], by show c.extqueue.rq ++ [ev] = _; rw [hv]; rfl⟩
  | upgrade_from_I_rq1 hI hp hg hw =>
      obtain ⟨rst, hv⟩ := hw
      exact cache_step.upgrade_from_I_rq1 _ hI hp hg
        ⟨rst ++ [ev], by show c.extqueue.rq ++ [ev] = _; rw [hv]; rfl⟩
  | upgrade_from_I_rs v j hj hI => exact cache_step.upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact cache_step.upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM => exact cache_step.downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS => exact cache_step.downgrade_from_M_rs1 _ j hj hS
  | drop_rqIμ j hj hI => exact cache_step.drop_rqIμ _ j hj hI
  | drop_rqIσ j hj hI => exact cache_step.drop_rqIσ _ j hj hI

/-- Un passo interno commuta con l'accodamento, in forma esplicita. -/
theorem comm_enq_step {x y : MSIState n} {e : IEvent n} {k : Fin n} {ev : Event}
    (hs : synced x) (h : step_int x e y) :
    step_int (comm_extSt x k (comm_enqC (x.caches k) ev)) e
      (comm_extSt y k (comm_enqC (y.caches k) ev)) := by
  cases h with
  | cache cache' i ce hc =>
    by_cases hik : i = k
    · subst hik
      have hc' : cache_step ((comm_extSt x i (comm_enqC (x.caches i) ev)).caches i) ce
          (comm_enqC cache' ev) := by
        rw [comm_extSt_caches_self]; exact comm_cache_step_enq hc
      refine comm_step_int_eq (step_int.cache _ _ i _ hc') ?_
      show comm_extSt (comm_extSt x i (comm_enqC (x.caches i) ev)) i (comm_enqC cache' ev)
        = comm_extSt (comm_extSt x i cache') i (comm_enqC ((comm_extSt x i cache').caches i) ev)
      rw [comm_extSt_extSt, comm_extSt_extSt, comm_extSt_caches_self]
    · have hc' : cache_step ((comm_extSt x k (comm_enqC (x.caches k) ev)).caches i) ce cache' := by
        rw [comm_extSt_caches_other hik]; exact hc
      refine comm_step_int_eq (step_int.cache _ _ i _ hc') ?_
      show comm_extSt (comm_extSt x k (comm_enqC (x.caches k) ev)) i cache'
        = comm_extSt (comm_extSt x i cache') k (comm_enqC ((comm_extSt x i cache').caches k) ev)
      rw [comm_extSt_caches_other (Ne.symm hik), comm_extSt_comm hik]
  | parent_upd_queue parent' pe i hp =>
    have hpar : (comm_extSt x k (comm_enqC (x.caches k) ev)).parent = x.parent :=
      comm_extSt_parent hs rfl rfl
    have hp' : parent_msi_step (comm_extSt x k (comm_enqC (x.caches k) ev)).parent
        (.upd_queue pe i) parent' := by
      rw [hpar]; exact hp
    refine comm_step_int_eq (step_int.parent_upd_queue _ _ pe i hp') ?_
    show comm_parSt (comm_extSt x k (comm_enqC (x.caches k) ev)) parent' i
      = comm_extSt (comm_parSt x parent' i) k (comm_enqC ((comm_parSt x parent' i).caches k) ev)
    have hloc := parent_step_local hp
    refine MSIState.ext_all (fun j => ?_) rfl (fun j => rfl) (fun j => ?_) (fun j => ?_)
    · by_cases hjk : j = k
      · subst hjk
        by_cases hji : j = i
        · subst hji; simp [comm_parSt, comm_extSt, comm_enqC]
        · simp [comm_parSt, comm_extSt, comm_enqC, update_Fin_gso2 _ _ _ _ hji]
      · by_cases hji : j = i
        · subst hji; simp [comm_parSt, comm_extSt, comm_enqC, update_Fin_gso2 _ _ _ _ hjk]
        · simp [comm_parSt, comm_extSt, update_Fin_gso2 _ _ _ _ hji, update_Fin_gso2 _ _ _ _ hjk]
    · by_cases hjk : j = k
      · subst hjk
        by_cases hji : j = i
        · subst hji; simp [comm_parSt, comm_extSt, comm_enqC]
        · simp [comm_parSt, comm_extSt, comm_enqC, update_Fin_gso2 _ _ _ _ hji]
          rw [(hloc j hji).1, (hs j).1]
      · simp [comm_parSt, comm_extSt, update_Fin_gso2 _ _ _ _ hjk]
    · by_cases hjk : j = k
      · subst hjk
        by_cases hji : j = i
        · subst hji; simp [comm_parSt, comm_extSt, comm_enqC]
        · simp [comm_parSt, comm_extSt, comm_enqC, update_Fin_gso2 _ _ _ _ hji]
          rw [(hloc j hji).2.1, (hs j).2]
      · simp [comm_parSt, comm_extSt, update_Fin_gso2 _ _ _ _ hjk]

/-- Un cammino interno commuta con l'accodamento. -/
theorem comm_enq_path {x y : MSIState n} {k : Fin n} {ev : Event} (hs : synced x)
    (h : trans_refl (rule n) x y) :
    trans_refl (rule n) (comm_extSt x k (comm_enqC (x.caches k) ev))
      (comm_extSt y k (comm_enqC (y.caches k) ev)) := by
  induction h with
  | refl => exact trans_refl.refl
  | step hab _ ih =>
      obtain ⟨e, he⟩ := hab
      exact trans_refl.step ⟨e, comm_enq_step hs he⟩ (ih (synced_step_int hs he))

/-- Un passo interno commuta con l'accodamento di una richiesta del programma (`ld_rq`/`st_rq`): i
passi interni non leggono la `extqueue` se non per la testa, che l'accodamento non cambia quando la
coda non è vuota, e quando è vuota nessuna richiesta della cache è possibile. -/
theorem step_int_enqueue {x y x' : MSIState n} {e : IEvent n} {k : Fin n} {ev : Event}
    (hev : ev = Event.ld_rq ∨ ∃ v, ev = Event.st_rq v)
    (hs : synced x) (h : step_int x e y) (hx : msi_step_external x (.cache ev k) x') :
    ∃ y', step_int x' e y' ∧ msi_step_external y (.cache ev k) y' := by
  cases hx with
  | cache _ cache' _ hc =>
    cases hc with
    | ld_rq =>
        exact ⟨_, comm_enq_step hs h, msi_step_external.cache y Event.ld_rq _ k (cache_msi_step.ld_rq _)⟩
    | st_rq v =>
        exact ⟨_, comm_enq_step hs h,
          msi_step_external.cache y (Event.st_rq v) _ k (cache_msi_step.st_rq _ v)⟩
    | ld_rq_data_available1 _ _ _ => rcases hev with h | ⟨v, h⟩ <;> cases h
    | ld_rq_data_available _ _ _ => rcases hev with h | ⟨v, h⟩ <;> cases h
    | st_rq_M_state _ _ _ _ => rcases hev with h | ⟨v, h⟩ <;> cases h

/-! ### Il caso delle load e delle store: si passa per il canonico -/

theorem comm_active_iff {x y : MSIState n} {j : Fin n} (h : x.caches j = y.caches j) :
    active x j ↔ active y j := by
  unfold active; rw [h]

theorem comm_active_canon {x : MSIState n} {m : Value} {j : Fin n} :
    active (canon x m) j ↔ wantsM (x.caches j) ∨ wantsS (x.caches j) := by
  simp [active, canon, pending, grantInFlight, wantsM, wantsS]

theorem comm_active_of_wants {x : MSIState n} {j : Fin n}
    (h : wantsM (x.caches j) ∨ wantsS (x.caches j)) : active x j := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

open Classical in
theorem comm_canon_value {x : MSIState n} {m : Value} {j : Fin n} :
    ((canon x m).caches j).value = if active x j then m else (x.caches j).value := rfl

theorem comm_canon_extqueue {x : MSIState n} {m : Value} {j : Fin n} :
    ((canon x m).caches j).extqueue = (x.caches j).extqueue := rfl

theorem comm_seq_ld_memory {s s' : SeqState n} {v : Value} {i : Fin n}
    (h : seq_step s (.cache (Event.ld_rs v) i) s') : s'.memory = s.memory := by
  cases h; rfl

theorem comm_seq_st_memory {s s' : SeqState n} {v : Value} {i : Fin n} {rst : List Event}
    (h : seq_step s (.cache Event.st_rs i) s') (hrq : (s.extqueue i).rq = Event.st_rq v :: rst) :
    s'.memory = v := by
  cases h with
  | st_rs v' _ rst' h' => rw [h'] at hrq; cases hrq; rfl

/-- Il caso delle load (la cache `k` in `S` o in `M`). -/
theorem comm_load {a b : MSIState n} {k : Fin n} {rst : List Event} {s : SeqState n}
    (ha : Reach a) (hab : trans_refl (rule n) a b) (hf : flush a s)
    (hrq : (a.caches k).extqueue.rq = Event.ld_rq :: rst)
    (hst : (a.caches k).state = Bstate.S ∨ (a.caches k).state = Bstate.M) :
    ∃ b' d j, trans_refl (rule n) b b' ∧
      msi_step_external b' (.cache (Event.ld_rs (a.caches k).value) k) d ∧
      trans_refl (rule n) (comm_extSt a k (comm_ldC (a.caches k) (a.caches k).value rst)) j ∧
      trans_refl (rule n) d j := by
  have hkI : (a.caches k).state ≠ Bstate.I := by
    rcases hst with h | h <;> rw [h] <;> intro h' <;> cases h'
  have hval : (a.caches k).value = s.memory := hf.2.2.1 k hkI
  have hw : wantsS (a.caches k) := ⟨rst, hrq⟩
  -- il metodo in `a`
  have hac : msi_step_external a (.cache (Event.ld_rs (a.caches k).value) k)
      (comm_extSt a k (comm_ldC (a.caches k) (a.caches k).value rst)) := by
    rcases hst with h | h
    · exact msi_step_external.cache a _ _ k (cache_msi_step.ld_rq_data_available1 _ rst hrq h)
    · exact msi_step_external.cache a _ _ k (cache_msi_step.ld_rq_data_available _ rst hrq h)
  have hrc : Reach (comm_extSt a k (comm_ldC (a.caches k) (a.caches k).value rst)) :=
    reach_of_step_ext ha hac
  obtain ⟨s', hs'⟩ := flush_method hf hac
  have hfc := flush_step_ext hf hac hs'
  have hmem' : s'.memory = s.memory := comm_seq_ld_memory hs'
  -- il canonico di `a`
  have hca : trans_refl (rule n) a (canon a s.memory) := reach_canon ha hf
  have hrca : Reach (canon a s.memory) := reach_trans ha hca
  have hfca : flush (canon a s.memory) s := flush_trans hf hca
  -- da `b` al canonico di `a`
  have hb : Reach b := reach_trans ha hab
  have hfb : flush b s := flush_trans hf hab
  have hbc : trans_refl (rule n) b (canon a s.memory) := by
    have := reach_canon hb hfb
    rwa [canon_trans ha hf hab] at this
  -- la cache `k` riprende la linea in `S`
  obtain ⟨y, hcy, hyS, hyv, hye, hyo, -⟩ := acquire_S hrca hw
  have hry : Reach y := reach_trans hrca hcy
  have hfy : flush y s := flush_trans hfca hcy
  have hyrq : (y.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hye]; exact hrq
  have hyv' : (y.caches k).value = (a.caches k).value := hyv.trans hval.symm
  have hd : msi_step_external y (.cache (Event.ld_rs (a.caches k).value) k)
      (comm_extSt y k (comm_ldC (y.caches k) (a.caches k).value rst)) := by
    rw [← hyv']
    exact msi_step_external.cache y _ _ k (cache_msi_step.ld_rq_data_available1 _ rst hyrq hyS)
  have hrd : Reach (comm_extSt y k (comm_ldC (y.caches k) (a.caches k).value rst)) :=
    reach_of_step_ext hry hd
  obtain ⟨s'', hs''⟩ := flush_method hfy hd
  have hfd := flush_step_ext hfy hd hs''
  have hmem'' : s''.memory = s.memory := comm_seq_ld_memory hs''
  have hcj := reach_canon hrc hfc
  rw [hmem'] at hcj
  have hdj := reach_canon hrd hfd
  rw [hmem''] at hdj
  -- i due canonici coincidono
  have heq : canon (comm_extSt y k (comm_ldC (y.caches k) (a.caches k).value rst)) s.memory
      = canon (comm_extSt a k (comm_ldC (a.caches k) (a.caches k).value rst)) s.memory := by
    refine canon_ext (fun j => ?_) (fun j => ?_)
    · by_cases hjk : j = k
      · subst hjk
        have h1 : active (comm_extSt y j (comm_ldC (y.caches j) (a.caches j).value rst)) j :=
          Or.inl (by rw [comm_extSt_caches_self]; simp [comm_ldC, hyS])
        have h2 : active (comm_extSt a j (comm_ldC (a.caches j) (a.caches j).value rst)) j :=
          Or.inl (by rw [comm_extSt_caches_self]; simpa [comm_ldC] using hkI)
        rw [if_pos h1, if_pos h2]
      · have hdj' : (comm_extSt y k (comm_ldC (y.caches k) (a.caches k).value rst)).caches j
            = (canon a s.memory).caches j := by
          rw [comm_extSt_caches_other hjk]; exact hyo j hjk
        have hcj' : (comm_extSt a k (comm_ldC (a.caches k) (a.caches k).value rst)).caches j
            = a.caches j := comm_extSt_caches_other hjk
        have hact_d := (comm_active_iff hdj').trans comm_active_canon
        have hact_c := comm_active_iff hcj'
        by_cases hw' : wantsM (a.caches j) ∨ wantsS (a.caches j)
        · rw [if_pos (hact_d.mpr hw'), if_pos (hact_c.mpr (comm_active_of_wants hw'))]
        · rw [if_neg (fun h => hw' (hact_d.mp h)), hdj', hcj', comm_canon_value]
          by_cases ha' : active a j
          · rw [if_pos ha', if_pos (hact_c.mpr ha')]
          · rw [if_neg ha', if_neg (fun h => ha' (hact_c.mp h))]
    · by_cases hjk : j = k
      · subst hjk
        rw [comm_extSt_caches_self, comm_extSt_caches_self]
        simp [comm_ldC, hye]
      · rw [comm_extSt_caches_other hjk, comm_extSt_caches_other hjk, hyo j hjk, comm_canon_extqueue]
  refine ⟨y, _, _, ReachingStar.trans_refl_trans hbc hcy, hd, hcj, ?_⟩
  rw [heq] at hdj; exact hdj

/-- Il caso della store (la cache `k` in `M`). -/
theorem comm_store {a b : MSIState n} {k : Fin n} {v : Value} {rst : List Event} {s : SeqState n}
    (ha : Reach a) (hab : trans_refl (rule n) a b) (hf : flush a s)
    (hrq : (a.caches k).extqueue.rq = Event.st_rq v :: rst)
    (hM : (a.caches k).state = Bstate.M) :
    ∃ b' d j, trans_refl (rule n) b b' ∧
      msi_step_external b' (.cache Event.st_rs k) d ∧
      trans_refl (rule n) (comm_extSt a k (comm_stC (a.caches k) v rst)) j ∧
      trans_refl (rule n) d j := by
  have hw : wantsM (a.caches k) := ⟨v, rst, hrq⟩
  -- il metodo in `a`
  have hac : msi_step_external a (.cache Event.st_rs k) (comm_extSt a k (comm_stC (a.caches k) v rst)) :=
    msi_step_external.cache a _ _ k (cache_msi_step.st_rq_M_state _ v rst hrq hM)
  have hrc : Reach (comm_extSt a k (comm_stC (a.caches k) v rst)) := reach_of_step_ext ha hac
  obtain ⟨s', hs'⟩ := flush_method hf hac
  have hfc := flush_step_ext hf hac hs'
  have hmem' : s'.memory = v := comm_seq_st_memory hs' (by rw [← hf.2.1 k]; exact hrq)
  -- il canonico di `a`
  have hca : trans_refl (rule n) a (canon a s.memory) := reach_canon ha hf
  have hrca : Reach (canon a s.memory) := reach_trans ha hca
  have hfca : flush (canon a s.memory) s := flush_trans hf hca
  -- da `b` al canonico di `a`
  have hb : Reach b := reach_trans ha hab
  have hfb : flush b s := flush_trans hf hab
  have hbc : trans_refl (rule n) b (canon a s.memory) := by
    have := reach_canon hb hfb
    rwa [canon_trans ha hf hab] at this
  -- la cache `k` riprende la linea in `M`
  obtain ⟨y, hcy, hyM, hyv, hye, hyo, -⟩ := acquire_M hrca hw
  have hry : Reach y := reach_trans hrca hcy
  have hfy : flush y s := flush_trans hfca hcy
  have hyrq : (y.caches k).extqueue.rq = Event.st_rq v :: rst := by rw [hye]; exact hrq
  have hd : msi_step_external y (.cache Event.st_rs k) (comm_extSt y k (comm_stC (y.caches k) v rst)) :=
    msi_step_external.cache y _ _ k (cache_msi_step.st_rq_M_state _ v rst hyrq hyM)
  have hrd : Reach (comm_extSt y k (comm_stC (y.caches k) v rst)) := reach_of_step_ext hry hd
  obtain ⟨s'', hs''⟩ := flush_method hfy hd
  have hfd := flush_step_ext hfy hd hs''
  have hmem'' : s''.memory = v := comm_seq_st_memory hs'' (by rw [← hfy.2.1 k]; exact hyrq)
  have hcj := reach_canon hrc hfc
  rw [hmem'] at hcj
  have hdj := reach_canon hrd hfd
  rw [hmem''] at hdj
  -- in `a` la cache `k` è in `M`: nessun'altra cache è attiva senza una richiesta del programma
  have hnot : ∀ j, j ≠ k → active a j → wantsM (a.caches j) ∨ wantsS (a.caches j) := by
    intro j hjk hact
    have hdem := (demandOK_of_reach ha j).1
    rcases hact with hst | hp | hg | hw' | hw'
    · exfalso
      have hrowk : a.parent.shared_state k = Bstate.M := by
        by_contra h; exact not_reach_of_M hM (Or.inr (Or.inr h)) ha
      have hrowj : a.parent.shared_state j = Bstate.I := by
        by_contra h; exact not_reach_of_rowM_rowJ (Ne.symm hjk) hrowk h ha
      cases hsj : (a.caches j).state with
      | I => exact hst hsj
      | M => exact not_reach_of_M hsj (Or.inr (Or.inr (by rw [hrowj]; intro h; cases h))) ha
      | S => exact not_reach_of_S hsj (Or.inr (Or.inr (by rw [hrowj]; intro h; cases h))) ha
    · exact hdem (Or.inl hp)
    · exact hdem (Or.inr hg)
    · exact Or.inl hw'
    · exact Or.inr hw'
  -- i due canonici coincidono
  have heq : canon (comm_extSt y k (comm_stC (y.caches k) v rst)) v
      = canon (comm_extSt a k (comm_stC (a.caches k) v rst)) v := by
    refine canon_ext (fun j => ?_) (fun j => ?_)
    · by_cases hjk : j = k
      · subst hjk
        have h1 : active (comm_extSt y j (comm_stC (y.caches j) v rst)) j :=
          Or.inl (by rw [comm_extSt_caches_self]; simp [comm_stC, hyM])
        have h2 : active (comm_extSt a j (comm_stC (a.caches j) v rst)) j :=
          Or.inl (by rw [comm_extSt_caches_self]; simp [comm_stC, hM])
        rw [if_pos h1, if_pos h2]
      · have hdj' : (comm_extSt y k (comm_stC (y.caches k) v rst)).caches j
            = (canon a s.memory).caches j := by
          rw [comm_extSt_caches_other hjk]; exact hyo j hjk
        have hcj' : (comm_extSt a k (comm_stC (a.caches k) v rst)).caches j = a.caches j :=
          comm_extSt_caches_other hjk
        have hact_d := (comm_active_iff hdj').trans comm_active_canon
        have hact_c := comm_active_iff hcj'
        by_cases hw' : wantsM (a.caches j) ∨ wantsS (a.caches j)
        · rw [if_pos (hact_d.mpr hw'), if_pos (hact_c.mpr (comm_active_of_wants hw'))]
        · have hna : ¬ active a j := fun h => hw' (hnot j hjk h)
          rw [if_neg (fun h => hw' (hact_d.mp h)), if_neg (fun h => hna (hact_c.mp h)), hdj', hcj',
            comm_canon_value, if_neg hna]
    · by_cases hjk : j = k
      · subst hjk
        rw [comm_extSt_caches_self, comm_extSt_caches_self]
        simp [comm_stC, hye]
      · rw [comm_extSt_caches_other hjk, comm_extSt_caches_other hjk, hyo j hjk, comm_canon_extqueue]
  refine ⟨y, _, _, ReachingStar.trans_refl_trans hbc hcy, hd, hcj, ?_⟩
  rw [heq] at hdj; exact hdj

/-- `commutes_method_rule_upto_on` di ARS per `MSI_trial`. -/
theorem msi_trial_commutes_upto :
    ReachingStar.commutes_method_rule_upto_on (Reach (n := n)) msi_step_external (rule n) := by
  intro a b c e ha hab hac
  obtain ⟨s, hf⟩ := exists_flush_of_reach ha
  cases hac with
  | cache ev cache' k hc =>
    cases hc with
    | ld_rq =>
        exact ⟨b, _, _, trans_refl.refl,
          msi_step_external.cache b Event.ld_rq _ k (cache_msi_step.ld_rq _),
          comm_enq_path (ev := Event.ld_rq) (k := k) (synced_of_reach ha) hab, trans_refl.refl⟩
    | st_rq v =>
        exact ⟨b, _, _, trans_refl.refl,
          msi_step_external.cache b (Event.st_rq v) _ k (cache_msi_step.st_rq _ v),
          comm_enq_path (ev := Event.st_rq v) (k := k) (synced_of_reach ha) hab, trans_refl.refl⟩
    | ld_rq_data_available1 rst hrq hS => exact comm_load ha hab hf hrq (Or.inl hS)
    | ld_rq_data_available rst hrq hM => exact comm_load ha hab hf hrq (Or.inr hM)
    | st_rq_M_state v rst hrq hM => exact comm_store ha hab hf hrq hM

end MSITrial
