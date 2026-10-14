import StarExperimental.MSI_trial_canon

/-!
# `MSI_trial`: svuotamento, tappe 1–2

Da uno stato raggiungibile qualsiasi a `Quiet2`: rilasci spontanei, prese dei grant, consumi dei
rilasci (tappa 1, misura pesata su detentori, grant e rilasci), poi scarto degli invalidate (tappa 2).
Le righe tornano a `I` per i pattern 14–15 (`bearer_of_rowM`, `bearer_of_rowS`).
-/

open THEORY Relation MSIView
open ReachingStar (Rule trans_refl)

namespace MSITrial

variable {n : Nat}

/-! ## Misure

Una misura è la somma, su tutte le cache, di un peso che dipende solo dalla cache; un passo che
tocca la sola cache `k` (le code del parent non contano) la fa calare se il peso di `k` cala. -/

/-- Somma su tutte le cache di un peso `w`. -/
theorem drain1_sum_lt (w : CacheState → Nat) {x y : MSIState n} {k : Fin n} {c' : CacheState}
    (hy : y.caches = update_Fin k c' x.caches) (hw : w c' < w (x.caches k)) :
    Finset.univ.sum (fun j => w (y.caches j)) < Finset.univ.sum (fun j => w (x.caches j)) := by
  rw [hy]
  apply Finset.sum_lt_sum
  · intro j _
    show w (update_Fin k c' x.caches j) ≤ w (x.caches j)
    by_cases hj : j = k
    · subst hj; rw [update_Fin_gss]; exact Nat.le_of_lt hw
    · exact Nat.le_of_eq (congrArg w (update_Fin_gso2 _ _ _ _ hj))
  · exact ⟨k, Finset.mem_univ k, by
      show w (update_Fin k c' x.caches k) < w (x.caches k)
      rw [update_Fin_gss]; exact hw⟩

/-- Un messaggio parent → cache che porta un token (`rsM`, `rsS`). -/
def drain1_isGrant (e : PCEvent) : Bool := isGrantM e || isGrantS e

/-- Un messaggio cache → parent che porta un token (`rsIμ`, `rsIσ`). -/
def drain1_isRelease (e : CPEvent) : Bool := isReleaseM e || isReleaseS e

/-- Peso di chi tiene la linea. -/
def drain1_hold : Bstate → Nat
  | .I => 0
  | _ => 3

theorem drain1_hold_I : drain1_hold Bstate.I = 0 := rfl

theorem drain1_hold_of_ne {b : Bstate} (h : b ≠ Bstate.I) : drain1_hold b = 3 := by
  cases b with
  | I => exact absurd rfl h
  | M => rfl
  | S => rfl

/-- Peso della tappa 1: `3·[state ≠ I] + 4·#grant + #rilasci`. -/
def drain1_w (c : CacheState) : Nat :=
  drain1_hold c.state + 4 * c.queue_pc.countP drain1_isGrant + c.queue_cp.countP drain1_isRelease

/-- Misura della tappa 1. -/
def drain1_mu (x : MSIState n) : Nat := Finset.univ.sum (fun k => drain1_w (x.caches k))

theorem drain1_mu_lt {x y : MSIState n} {k : Fin n} {c' : CacheState}
    (hy : y.caches = update_Fin k c' x.caches) (hw : drain1_w c' < drain1_w (x.caches k)) :
    drain1_mu y < drain1_mu x :=
  drain1_sum_lt drain1_w hy hw

/-- Consumo di un rilascio al parent: `−1`. -/
theorem drain1_w_lt_release {c c' : CacheState} (hs : c'.state = c.state)
    (hpc : c'.queue_pc = c.queue_pc) {j : Nat} {a : CPEvent}
    (hcp : c'.queue_cp = c.queue_cp.eraseIdx j) (h : c.queue_cp[j]? = some a)
    (ha : drain1_isRelease a = true) : drain1_w c' < drain1_w c := by
  unfold drain1_w
  rw [hs, hpc, hcp]
  have hc := countP_eraseIdx drain1_isRelease c.queue_cp j a h
  rw [if_pos ha] at hc
  omega

/-- Rilascio spontaneo: `−3 + 1`. -/
theorem drain1_w_lt_holder {c c' : CacheState} (hs : c.state ≠ Bstate.I) (hs' : c'.state = Bstate.I)
    (hpc : c'.queue_pc = c.queue_pc) {a : CPEvent} (hcp : c'.queue_cp = c.queue_cp ++ [a]) :
    drain1_w c' < drain1_w c := by
  unfold drain1_w
  rw [hs', hpc, hcp, drain1_hold_of_ne hs, drain1_hold_I, List.countP_append, List.countP_cons,
    List.countP_nil]
  split <;> omega

/-- Presa di un grant: `−4 + 3`. -/
theorem drain1_w_lt_take {c c' : CacheState} (hs : c.state = Bstate.I) (hs' : c'.state ≠ Bstate.I)
    (hcp : c'.queue_cp = c.queue_cp) {j : Nat} {a : PCEvent}
    (hpc : c'.queue_pc = c.queue_pc.eraseIdx j) (h : c.queue_pc[j]? = some a)
    (ha : drain1_isGrant a = true) : drain1_w c' < drain1_w c := by
  unfold drain1_w
  rw [hs, hcp, hpc, drain1_hold_of_ne hs', drain1_hold_I]
  have hc := countP_eraseIdx drain1_isGrant c.queue_pc j a h
  rw [if_pos ha] at hc
  omega

/-! ## `Keeps` per un passo che tocca una sola cache -/

/-- `active` letta sulla sola cache. -/
def drain1_act (c : CacheState) : Prop :=
  c.state ≠ Bstate.I ∨ pending c ∨ grantInFlight c ∨ wantsM c ∨ wantsS c

/-- Se le code di `c'` sono incluse in quelle di `c` (stesso stato, stessa `extqueue`), l'attività
di `c'` implica quella di `c`. -/
theorem drain1_act_mono {c c' : CacheState} (h : drain1_act c')
    (hs : c'.state = c.state) (hext : c'.extqueue = c.extqueue)
    (hcp : ∀ e, e ∈ c'.queue_cp → e ∈ c.queue_cp) (hpc : ∀ e, e ∈ c'.queue_pc → e ∈ c.queue_pc) :
    drain1_act c := by
  rcases h with h | h | h | h | h
  · exact Or.inl (fun h' => h (hs.trans h'))
  · rcases h with h | h
    · exact Or.inr (Or.inl (Or.inl (hcp _ h)))
    · exact Or.inr (Or.inl (Or.inr (hcp _ h)))
  · rcases h with ⟨v, h⟩ | ⟨v, h⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨v, hpc _ h⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨v, hpc _ h⟩)))
  · obtain ⟨v, rst, h⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rst, by rw [← hext]; exact h⟩)))
  · obtain ⟨rst, h⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rst, by rw [← hext]; exact h⟩)))

/-- `Keeps` per un passo che sostituisce la sola cache `k` con `c'`. -/
theorem drain1_keeps_upd {x y : MSIState n} {k : Fin n} {c' : CacheState} {m : Value}
    (hy : y.caches = update_Fin k c' x.caches)
    (hext : c'.extqueue = (x.caches k).extqueue)
    (hact : ¬ drain1_act (x.caches k) → ¬ drain1_act c')
    (hval : ¬ drain1_act (x.caches k) → c'.value = (x.caches k).value)
    (hv2 : c'.value = (x.caches k).value ∨ c'.value = m) :
    Keeps x y m := by
  have hcj : ∀ j, j ≠ k → y.caches j = x.caches j := fun j hj => by
    rw [hy, update_Fin_gso2 _ _ _ _ hj]
  have hck : y.caches k = c' := by rw [hy, update_Fin_gss]
  refine ⟨fun j => ?_, fun j ha => ?_, fun j ha => ?_, fun j => ?_⟩
  · by_cases hj : j = k
    · subst hj; rw [hck]; exact hext
    · rw [hcj j hj]
  · unfold active
    by_cases hj : j = k
    · subst hj; rw [hck]; exact hact ha
    · rw [hcj j hj]; exact ha
  · by_cases hj : j = k
    · subst hj; rw [hck]; exact hval ha
    · rw [hcj j hj]
  · by_cases hj : j = k
    · subst hj; rw [hck]; exact hv2
    · rw [hcj j hj]; exact Or.inl rfl

/-! ## Progresso della tappa 1 -/

/-- Un passo che fa calare la misura e conserva `Keeps`. -/
def drain1_Prog (x : MSIState n) (m : Value) : Prop :=
  ∃ y, rule n x y ∧ drain1_mu y < drain1_mu x ∧ Keeps x y m

/-- (a) Un rilascio `rsIμ` in volo: il parent lo consuma (`downgrade_from_M_rq1`). -/
theorem drain1_prog_relM {x : MSIState n} {m : Value} (hr : Reach x) {k : Fin n} {v : Value}
    (hk : CPEvent.rsIμ v ∈ (x.caches k).queue_cp) : drain1_Prog x m := by
  have hsy := synced_of_reach hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
  have hj' : (x.parent.queue_cip k)[j]? = some (CPEvent.rsIμ v) := by rw [(hsy k).1]; exact hj
  have hstep := step_int.parent_upd_queue x _ (.downgrade_from_M_rq1 v) k
    (parent_msi_step.downgrade_from_M_rq1 x.parent v k j hj')
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_release rfl (hsy k).2
      (by show update_Fin k ((x.parent.queue_cip k).eraseIdx j) x.parent.queue_cip k = _
          rw [update_Fin_gss, (hsy k).1]) hj rfl
  · refine drain1_keeps_upd rfl rfl ?_ (fun _ => rfl) (Or.inl rfl)
    intro hna hc
    apply hna
    refine drain1_act_mono hc rfl rfl ?_ ?_
    · intro e he
      have he' : e ∈ update_Fin k ((x.parent.queue_cip k).eraseIdx j) x.parent.queue_cip k := he
      rw [update_Fin_gss, (hsy k).1] at he'
      exact List.mem_of_mem_eraseIdx he'
    · intro e he
      have he' : e ∈ x.parent.queue_pci k := he
      rw [(hsy k).2] at he'
      exact he'

/-- (a) Un rilascio `rsIσ` in volo: il parent lo consuma (`downgrade_from_M_rq2`). -/
theorem drain1_prog_relS {x : MSIState n} {m : Value} (hr : Reach x) {k : Fin n}
    (hk : CPEvent.rsIσ ∈ (x.caches k).queue_cp) : drain1_Prog x m := by
  have hsy := synced_of_reach hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
  have hj' : (x.parent.queue_cip k)[j]? = some CPEvent.rsIσ := by rw [(hsy k).1]; exact hj
  have hstep := step_int.parent_upd_queue x _ .downgrade_from_S_rq1S k
    (parent_msi_step.downgrade_from_M_rq2 x.parent k j hj')
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_release rfl (hsy k).2
      (by show update_Fin k ((x.parent.queue_cip k).eraseIdx j) x.parent.queue_cip k = _
          rw [update_Fin_gss, (hsy k).1]) hj rfl
  · refine drain1_keeps_upd rfl rfl ?_ (fun _ => rfl) (Or.inl rfl)
    intro hna hc
    apply hna
    refine drain1_act_mono hc rfl rfl ?_ ?_
    · intro e he
      have he' : e ∈ update_Fin k ((x.parent.queue_cip k).eraseIdx j) x.parent.queue_cip k := he
      rw [update_Fin_gss, (hsy k).1] at he'
      exact List.mem_of_mem_eraseIdx he'
    · intro e he
      have he' : e ∈ x.parent.queue_pci k := he
      rw [(hsy k).2] at he'
      exact he'

/-- (b) Una cache in `M`: rilascio spontaneo (`rq_data_not_available`). -/
theorem drain1_prog_M {x : MSIState n} {m : Value} {k : Fin n}
    (hk : (x.caches k).state = Bstate.M) : drain1_Prog x m := by
  have hstep := step_int.cache x _ k _ (cache_step.rq_data_not_available (x.caches k) hk)
  have hne : (x.caches k).state ≠ Bstate.I := by rw [hk]; intro h; cases h
  have hact : drain1_act (x.caches k) := Or.inl hne
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_holder hne rfl rfl rfl
  · exact drain1_keeps_upd rfl rfl (fun hna => absurd hact hna) (fun hna => absurd hact hna)
      (Or.inl rfl)

/-- (b) Una cache in `S`: rilascio spontaneo (`rq_data_not_available1`). -/
theorem drain1_prog_S {x : MSIState n} {m : Value} {k : Fin n}
    (hk : (x.caches k).state = Bstate.S) : drain1_Prog x m := by
  have hstep := step_int.cache x _ k _ (cache_step.rq_data_not_available1 (x.caches k) hk)
  have hne : (x.caches k).state ≠ Bstate.I := by rw [hk]; intro h; cases h
  have hact : drain1_act (x.caches k) := Or.inl hne
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_holder hne rfl rfl rfl
  · exact drain1_keeps_upd rfl rfl (fun hna => absurd hact hna) (fun hna => absurd hact hna)
      (Or.inl rfl)

/-- (c) Un grant `rsM` in volo: la cache è in `I` (vista cattiva 3 altrimenti) e lo prende
(`upgrade_from_I_rs`); il valore preso è `s.memory` (clausola 4 di `flush`). -/
theorem drain1_prog_grantM {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    {k : Fin n} {v : Value} (hk : PCEvent.rsM v ∈ (x.caches k).queue_pc) :
    drain1_Prog x s.memory := by
  have hsy := synced_of_reach hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
  have hj' : (x.parent.queue_pci k)[j]? = some (PCEvent.rsM v) := by rw [(hsy k).2]; exact hj
  have hI : (x.caches k).state = Bstate.I := by
    cases hst : (x.caches k).state with
    | I => rfl
    | M => exact absurd hr (not_reach_of_M hst (Or.inl (muMsgs_ne_zero_of_rsM hj')))
    | S => exact absurd hr (not_reach_of_S hst (Or.inl (muMsgs_ne_zero_of_rsM hj')))
  have hstep := step_int.cache x _ k _ (cache_step.upgrade_from_I_rs (x.caches k) v j hj hI)
  have hact : drain1_act (x.caches k) := Or.inr (Or.inr (Or.inl (Or.inl ⟨v, hk⟩)))
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_take hI (by intro h; cases h) rfl rfl hj rfl
  · exact drain1_keeps_upd rfl rfl (fun hna => absurd hact hna) (fun hna => absurd hact hna)
      (Or.inr (hf.2.2.2.1 k v hk))

/-- (c) Un grant `rsS` in volo: la cache è in `I` e lo prende (`upgrade_from_I_rsS`); il valore
preso è `s.memory` (clausola 5 di `flush`). -/
theorem drain1_prog_grantS {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    {k : Fin n} {v : Value} (hk : PCEvent.rsS v ∈ (x.caches k).queue_pc) :
    drain1_Prog x s.memory := by
  have hsy := synced_of_reach hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
  have hj' : (x.parent.queue_pci k)[j]? = some (PCEvent.rsS v) := by rw [(hsy k).2]; exact hj
  have hI : (x.caches k).state = Bstate.I := by
    cases hst : (x.caches k).state with
    | I => rfl
    | M => exact absurd hr (not_reach_of_M hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsS hj'))))
    | S => exact absurd hr (not_reach_of_S hst (Or.inr (Or.inl (sigMsgs_ne_zero_of_rsS hj'))))
  have hstep := step_int.cache x _ k _ (cache_step.upgrade_from_I_rsS (x.caches k) v j hj hI)
  have hact : drain1_act (x.caches k) := Or.inr (Or.inr (Or.inl (Or.inr ⟨v, hk⟩)))
  refine ⟨_, ⟨_, hstep⟩, ?_, ?_⟩
  · refine drain1_mu_lt rfl ?_
    exact drain1_w_lt_take hI (by intro h; cases h) rfl rfl hj rfl
  · exact drain1_keeps_upd rfl rfl (fun hna => absurd hact hna) (fun hna => absurd hact hna)
      (Or.inr (hf.2.2.2.2.1 k v hk))

/-- La cache `k` ha ancora qualcosa da svuotare nella tappa 1. -/
def drain1_busy (c : CacheState) : Prop :=
  c.state ≠ Bstate.I ∨ (∃ v, PCEvent.rsM v ∈ c.queue_pc) ∨ (∃ v, PCEvent.rsS v ∈ c.queue_pc) ∨
  (∃ v, CPEvent.rsIμ v ∈ c.queue_cp) ∨ CPEvent.rsIσ ∈ c.queue_cp

/-- Lemma di progresso della tappa 1. -/
theorem drain1_progress {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    {k : Fin n} (hk : drain1_busy (x.caches k)) : drain1_Prog x s.memory := by
  rcases hk with h | ⟨v, h⟩ | ⟨v, h⟩ | ⟨v, h⟩ | h
  · cases hst : (x.caches k).state with
    | I => exact absurd hst h
    | M => exact drain1_prog_M hst
    | S => exact drain1_prog_S hst
  · exact drain1_prog_grantM hr hf h
  · exact drain1_prog_grantS hr hf h
  · exact drain1_prog_relM hr h
  · exact drain1_prog_relS hr h

/-! ## Quando nessuna cache è occupata: `Quiet1` -/

theorem drain1_cnt_grantM {l : List PCEvent} (h : ∀ v, PCEvent.rsM v ∉ l) : l.countP isGrantM = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  cases e with
  | rsM v => exact absurd he (h v)
  | rsS _ => exact Bool.false_ne_true
  | rqIμ => exact Bool.false_ne_true
  | rqIσ => exact Bool.false_ne_true

theorem drain1_cnt_grantS {l : List PCEvent} (h : ∀ v, PCEvent.rsS v ∉ l) : l.countP isGrantS = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  cases e with
  | rsS v => exact absurd he (h v)
  | rsM _ => exact Bool.false_ne_true
  | rqIμ => exact Bool.false_ne_true
  | rqIσ => exact Bool.false_ne_true

theorem drain1_cnt_relM {l : List CPEvent} (h : ∀ v, CPEvent.rsIμ v ∉ l) : l.countP isReleaseM = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  cases e with
  | rsIμ v => exact absurd he (h v)
  | rsIσ => exact Bool.false_ne_true
  | rqS => exact Bool.false_ne_true
  | rqM => exact Bool.false_ne_true

theorem drain1_cnt_relS {l : List CPEvent} (h : CPEvent.rsIσ ∉ l) : l.countP isReleaseS = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  cases e with
  | rsIσ => exact absurd he h
  | rsIμ _ => exact Bool.false_ne_true
  | rqS => exact Bool.false_ne_true
  | rqM => exact Bool.false_ne_true

/-- Nessuna cache occupata ⇒ `Quiet1`: le righe sono a `I` per i pattern 14–15. -/
theorem drain1_quiet {x : MSIState n} (hr : Reach x) (hq : ∀ k, ¬ drain1_busy (x.caches k)) :
    Quiet1 x := by
  have h1 : ∀ k, (x.caches k).state = Bstate.I := fun k =>
    Classical.byContradiction fun h => hq k (Or.inl h)
  have h2 : ∀ k v, PCEvent.rsM v ∉ (x.caches k).queue_pc := fun k v h =>
    hq k (Or.inr (Or.inl ⟨v, h⟩))
  have h3 : ∀ k v, PCEvent.rsS v ∉ (x.caches k).queue_pc := fun k v h =>
    hq k (Or.inr (Or.inr (Or.inl ⟨v, h⟩)))
  have h4 : ∀ k v, CPEvent.rsIμ v ∉ (x.caches k).queue_cp := fun k v h =>
    hq k (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, h⟩))))
  have h5 : ∀ k, CPEvent.rsIσ ∉ (x.caches k).queue_cp := fun k h =>
    hq k (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hsy := synced_of_reach hr
  have hmu : ∀ k, muMsgs x.parent k = 0 := by
    intro k
    show (x.parent.queue_pci k).countP isGrantM + (x.parent.queue_cip k).countP isReleaseM = 0
    rw [(hsy k).1, (hsy k).2, drain1_cnt_grantM (h2 k), drain1_cnt_relM (h4 k)]
  have hsig : ∀ k, sigMsgs x.parent k = 0 := by
    intro k
    show (x.parent.queue_pci k).countP isGrantS + (x.parent.queue_cip k).countP isReleaseS = 0
    rw [(hsy k).1, (hsy k).2, drain1_cnt_grantS (h3 k), drain1_cnt_relS (h5 k)]
  refine ⟨h1, h2, h3, h4, h5, fun k => ?_⟩
  cases hrow : x.parent.shared_state k with
  | I => rfl
  | M =>
    rcases bearer_of_rowM hr hrow with hM | hne
    · rw [h1 k] at hM; cases hM
    · exact absurd (hmu k) hne
  | S =>
    rcases bearer_of_rowS hr hrow with hS | hne
    · rw [h1 k] at hS; cases hS
    · exact absurd (hsig k) hne

/-- **Tappa 1**: rilasci spontanei, prese dei grant, consumi dei rilasci, finché nessuno tiene la
linea e nessun token è in volo; allora le righe sono a `I` (pattern 14–15). -/
theorem drain_tokens {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet1 y ∧ Keeps x y s.memory := by
  suffices h : ∀ N (z : MSIState n), drain1_mu z = N → Reach z → flush z s →
      ∃ y, trans_refl (rule n) z y ∧ Quiet1 y ∧ Keeps z y s.memory from h _ x rfl hr hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hN hrz hfz
    by_cases hb : ∃ k, drain1_busy (z.caches k)
    · obtain ⟨k, hk⟩ := hb
      obtain ⟨y, hzy, hlt, hkeep⟩ := drain1_progress hrz hfz hk
      obtain ⟨w, hyw, hq, hkeep'⟩ := ih (drain1_mu y) (by rw [← hN]; exact hlt) y rfl
        (reach_step hrz hzy) (flush_trans hfz (trans_refl.step hzy trans_refl.refl))
      exact ⟨w, trans_refl.step hzy hyw, hq, hkeep.trans hkeep'⟩
    · exact ⟨z, trans_refl.refl, drain1_quiet hrz (fun k hk => hb ⟨k, hk⟩), Keeps.refl z _⟩

/-! ## Tappa 2: scarto degli invalidate -/

/-- Un invalidate (`rqIμ`, `rqIσ`). -/
def drain1_isInv : PCEvent → Bool
  | .rqIμ => true
  | .rqIσ => true
  | _ => false

/-- Peso della tappa 2: il numero di invalidate in `queue_pc`. -/
def drain1_wInv (c : CacheState) : Nat := c.queue_pc.countP drain1_isInv

/-- Misura della tappa 2. -/
def drain1_nu (x : MSIState n) : Nat := Finset.univ.sum (fun k => drain1_wInv (x.caches k))

theorem drain1_nu_lt {x y : MSIState n} {k : Fin n} {c' : CacheState}
    (hy : y.caches = update_Fin k c' x.caches) (hw : drain1_wInv c' < drain1_wInv (x.caches k)) :
    drain1_nu y < drain1_nu x :=
  drain1_sum_lt drain1_wInv hy hw

/-- Lo scarto di un invalidate in posizione `j` della cache `k`: la misura cala, `Quiet1` e `Keeps`
restano. -/
theorem drain1_drop_aux {x y : MSIState n} {m : Value} (hq : Quiet1 x) {k : Fin n} {j : Nat}
    {a : PCEvent} (hj : (x.caches k).queue_pc[j]? = some a) (ha : drain1_isInv a = true)
    (hy : y.caches = update_Fin k { x.caches k with queue_pc := (x.caches k).queue_pc.eraseIdx j }
      x.caches)
    (hp : y.parent.shared_state = x.parent.shared_state) :
    drain1_nu y < drain1_nu x ∧ Quiet1 y ∧ Keeps x y m := by
  have hcj : ∀ i, i ≠ k → y.caches i = x.caches i := fun i hi => by
    rw [hy, update_Fin_gso2 _ _ _ _ hi]
  have hck : y.caches k = { x.caches k with queue_pc := (x.caches k).queue_pc.eraseIdx j } := by
    rw [hy, update_Fin_gss]
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  refine ⟨?_, ⟨fun i => ?_, fun i v hv => ?_, fun i v hv => ?_, fun i v hv => ?_, fun i hv => ?_,
    fun i => ?_⟩, ?_⟩
  · refine drain1_nu_lt hy ?_
    show ((x.caches k).queue_pc.eraseIdx j).countP drain1_isInv
      < (x.caches k).queue_pc.countP drain1_isInv
    have hc := countP_eraseIdx drain1_isInv (x.caches k).queue_pc j a hj
    rw [if_pos ha] at hc
    omega
  · by_cases hi : i = k
    · subst hi; rw [hck]; exact q1 _
    · rw [hcj i hi]; exact q1 i
  · by_cases hi : i = k
    · subst hi; rw [hck] at hv; exact q2 _ v (List.mem_of_mem_eraseIdx hv)
    · rw [hcj i hi] at hv; exact q2 i v hv
  · by_cases hi : i = k
    · subst hi; rw [hck] at hv; exact q3 _ v (List.mem_of_mem_eraseIdx hv)
    · rw [hcj i hi] at hv; exact q3 i v hv
  · by_cases hi : i = k
    · subst hi; rw [hck] at hv; exact q4 _ v hv
    · rw [hcj i hi] at hv; exact q4 i v hv
  · by_cases hi : i = k
    · subst hi; rw [hck] at hv; exact q5 _ hv
    · rw [hcj i hi] at hv; exact q5 i hv
  · rw [hp]; exact q6 i
  · refine drain1_keeps_upd hy rfl ?_ (fun _ => rfl) (Or.inl rfl)
    intro hna hc
    apply hna
    exact drain1_act_mono hc rfl rfl (fun e he => he) (fun e he => List.mem_of_mem_eraseIdx he)

/-- Un passo di scarto per una cache con un invalidate in coda (`Quiet1`: la cache è in `I`). -/
theorem drain1_drop {x : MSIState n} {m : Value} (hq : Quiet1 x) {k : Fin n}
    (hk : PCEvent.rqIμ ∈ (x.caches k).queue_pc ∨ PCEvent.rqIσ ∈ (x.caches k).queue_pc) :
    ∃ y, rule n x y ∧ drain1_nu y < drain1_nu x ∧ Quiet1 y ∧ Keeps x y m := by
  have hI := hq.1 k
  rcases hk with hk | hk
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
    refine ⟨_, ⟨_, step_int.cache x _ k _ (cache_step.drop_rqIμ (x.caches k) j hj hI)⟩, ?_⟩
    exact drain1_drop_aux hq hj rfl rfl rfl
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hk
    refine ⟨_, ⟨_, step_int.cache x _ k _ (cache_step.drop_rqIσ (x.caches k) j hj hI)⟩, ?_⟩
    exact drain1_drop_aux hq hj rfl rfl rfl

/-- **Tappa 2**: scarto degli invalidate (tutte le cache sono in `I`). -/
theorem drain_invalidates {x : MSIState n} {s : SeqState n} (hr : Reach x) (hf : flush x s)
    (hq : Quiet1 x) :
    ∃ y, trans_refl (rule n) x y ∧ Quiet2 y ∧ Keeps x y s.memory := by
  suffices h : ∀ N (z : MSIState n), drain1_nu z = N → Quiet1 z →
      ∃ y, trans_refl (rule n) z y ∧ Quiet2 y ∧ Keeps z y s.memory from h _ x rfl hq
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hN hqz
    by_cases hb : ∃ k, PCEvent.rqIμ ∈ (z.caches k).queue_pc ∨ PCEvent.rqIσ ∈ (z.caches k).queue_pc
    · obtain ⟨k, hk⟩ := hb
      obtain ⟨y, hzy, hlt, hqy, hkeep⟩ := drain1_drop (m := s.memory) hqz hk
      obtain ⟨w, hyw, hq2, hkeep'⟩ := ih (drain1_nu y) (by rw [← hN]; exact hlt) y rfl hqy
      exact ⟨w, trans_refl.step hzy hyw, hq2, hkeep.trans hkeep'⟩
    · exact ⟨z, trans_refl.refl,
        ⟨hqz, fun k hk => hb ⟨k, Or.inl hk⟩, fun k hk => hb ⟨k, Or.inr hk⟩⟩, Keeps.refl z _⟩


end MSITrial
