import StarExperimental.a

/-! # `a_unreachable`: i 18 diamanti che non convergono sono irraggiungibili, senza `badView`

`A` (`a.lean`) raccoglie gli stati in cui i 18 teoremi di commutazione di `MSI.lean` non
convergono: un costruttore `t1 … t18` per teorema, con le guardie dei due passi e la
condizione di blocco. Qui si dimostra che nessuno di quegli stati è raggiungibile **senza
scrivere nessun invariante**: né `badView`, né i lemmi `not_reachable_of_*`, né altro.

L'idea, in quattro passi:

1. **Dai costruttori alle viste** (`viewA`). Ogni costruttore è tradotto nei sei campi di
   `msiView` sulla coppia di indici in cui il problema si vede. È una traduzione, non un
   invariante: dice solo come appare uno stato bloccato attraverso la vista.
2. **All'indietro** (`viewA_unreachable`). La tattica parte dalle viste di `viewA` e va
   all'indietro lungo le regole vere: per ogni vista calcola i predecessori; se un
   predecessore è già nell'insieme si ferma, altrimenti lo aggiunge e riparte da lui. Si chiude
   senza mai incontrare la vista dello stato iniziale. L'insieme chiuso lo costruisce la
   tattica: nessuno lo scrive.
3. **Da `A` alle viste** (`A_view`, `A_unreachable`). Ogni stato di `A` ha una vista in `viewA`.
4. **I 18 diamanti** (`diamond_1 … diamond_18`). Per ogni teorema: se i due passi partono da
   `s` (e vale la condizione di blocco), allora `s` non è raggiungibile.

L'unica cosa usata oltre alle regole è `synced`, cioè che le due copie di ogni coda (lato
parent e lato cache) coincidono: è un fatto sulle code del modello, non sul protocollo, e la
tattica lo richiede come `Inv`. In fondo al file `#no_badView` controlla che le dimostrazioni
non dipendano da `badView`. -/

open THEORY Relation BackwardGen MSIView

namespace AClosure

/-! ## 1. Dai costruttori alle viste -/

/-- **Le viste dei 18 costruttori di `A`.** Sulla coppia `(i, i)` i problemi di una cache sola;
sulla coppia `(i, k)` con `i ≠ k` quelli della cache `i` contro la riga di `k`. -/
def viewA (v : View) : Prop :=
  (v.eq = true ∧ v.d0 = v.d1 ∧
    ( (v.m0 ≠ .zero ∧ v.d0 ≠ .M)                    -- t1, t2: token `M` in volo, riga non `M`
    ∨ (v.s0 ≠ .zero ∧ v.d0 = .I)                    -- t3: token `S` in volo, riga `I`
    ∨ (v.c0 ≠ .I ∧ v.d0 = .I)                       -- t4–t7: cache non in `I`, riga `I`
    ∨ (v.c0 = .I ∧ v.m0 = .many)                    -- t10: due `rsM` in coda
    ∨ (v.c0 = .I ∧ v.m0 ≠ .zero ∧ v.s0 ≠ .zero)     -- t11: un `rsM` e un `rsS` in coda
    ∨ (v.c0 = .I ∧ v.s0 = .many) ))                 -- t12: due `rsS` in coda
  ∨ (v.eq = false ∧
    ( (v.c0 = .I ∧ v.m0 ≠ .zero ∧ v.d1 ≠ .I)        -- t8: `rsM` in coda, riga di `k` non `I`
    ∨ (v.c0 = .I ∧ v.s0 ≠ .zero ∧ v.d1 = .M)        -- t9: `rsS` in coda, riga di `k` a `M`
    ∨ (v.c0 = .M ∧ v.d1 ≠ .I)                       -- t13, t15, t17, t18: cache `M`, riga di `k` non `I`
    ∨ (v.c0 = .S ∧ v.d1 = .M) ))                    -- t14, t16: cache `S`, riga di `k` a `M`

/-! ## 2. All'indietro dalle viste di `A` -/

/-- Il sistema `MSI` (passi interni, `synced`, stato iniziale `default`) con `viewA` come
insieme da cui partire. -/
def msiSetupA (n : Nat) : SymSetup (MSIState n) (MSIInternalEvent n) (Fin n) View where
  trans := msi_step_internal
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step hs h
  view := msiView
  bad := viewA
  s0 := default
  inv0 := fun _ => ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **La ricerca all'indietro.** Parte dalle viste di `viewA`, aggiunge i predecessori finché
ce ne sono di nuovi, e non incontra mai la vista iniziale: nessuno stato con una vista di
`viewA` è raggiungibile da `default`. -/
theorem viewA_unreachable {n} : (msiSetupA n).Unreachable := by
  new_backward_tatic (msiSetupA _)

/-! ## 3. Da `A` alle viste -/

/-- Ogni stato di `A` con le code allineate ha una vista in `viewA`. -/
theorem A_view {n} {s : MSIState n} (hsync : synced s) (h : A s) :
    ∃ i j, viewA (msiView s i j) := by
  cases h with
  | t1 i₁ i₂ j₁ j₂ v h₁ _ hall =>
    exact ⟨i₁, i₁, Or.inl ⟨decide_eq_true rfl, rfl, Or.inl
      ⟨cnt_ne_zero (muMsgs_ne_zero_of_rsIμ h₁),
       by show ¬(s.parent.shared_state i₁ = Bstate.M); rw [hall i₁]; intro h; cases h⟩⟩⟩
  | t2 i₁ i₂ j₁ j₂ v h₁ _ _ hnoM =>
    exact ⟨i₁, i₁, Or.inl ⟨decide_eq_true rfl, rfl, Or.inl
      ⟨cnt_ne_zero (muMsgs_ne_zero_of_rsIμ h₁), hnoM i₁⟩⟩⟩
  | t3 i j₁ j₂ h₁ _ hall =>
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inl
      ⟨cnt_ne_zero (sigMsgs_ne_zero_of_rsIσ h₁), hall i⟩)⟩⟩
  | t4 i j₁ j₂ _ _ hI _ hc =>
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inl ⟨hc, hI⟩))⟩⟩
  | t5 i₁ i₂ i j₁ j₂ _ _ hall _ hc =>
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inl ⟨hc, hall i⟩))⟩⟩
  | t6 i₁ i₂ i j₁ j₂ _ _ hall _ hc =>
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inl ⟨hc, hall i⟩))⟩⟩
  | t7 i j₁ j₂ _ _ _ hI _ hc =>
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inl ⟨hc, hI⟩))⟩⟩
  | t8 i k j v hI hj hne hk =>
    rw [← (hsync i).2] at hj
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inl
      ⟨hI, cnt_ne_zero (muMsgs_ne_zero_of_rsM hj), hk⟩⟩⟩
  | t9 i k j v hI hj _ hne hk =>
    rw [← (hsync i).2] at hj
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inl
      ⟨hI, cnt_ne_zero (sigMsgs_ne_zero_of_rsS hj), hk⟩)⟩⟩
  | t10 i j₁ j₂ v₁ v₂ hI hj₁ hj₂ hj =>
    rw [← (hsync i).2] at hj₁ hj₂
    have h2 := two_le_countP_of_ne isGrantM _ hj₁ hj₂ hj rfl rfl
    have hmu : 2 ≤ muMsgs s.parent i := by unfold muMsgs; omega
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hI, show Cnt.ofCount (muMsgs s.parent i) = .many from (Cnt.ofCount_eq_many _).2 hmu⟩)))⟩⟩
  | t11 i j₁ j₂ v₁ v₂ hI hj₁ hj₂ =>
    rw [← (hsync i).2] at hj₁ hj₂
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hI, cnt_ne_zero (muMsgs_ne_zero_of_rsM hj₁), cnt_ne_zero (sigMsgs_ne_zero_of_rsS hj₂)⟩))))⟩⟩
  | t12 i j₁ j₂ v₁ v₂ hI hj₁ hj₂ hj =>
    rw [← (hsync i).2] at hj₁ hj₂
    have h2 := two_le_countP_of_ne isGrantS _ hj₁ hj₂ hj rfl rfl
    have hsig : 2 ≤ sigMsgs s.parent i := by unfold sigMsgs; omega
    exact ⟨i, i, Or.inl ⟨decide_eq_true rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hI, show Cnt.ofCount (sigMsgs s.parent i) = .many from (Cnt.ofCount_eq_many _).2 hsig⟩))))⟩⟩
  | t13 i k rst hM _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inl ⟨hM, hk⟩))⟩⟩
  | t14 i k rst hS _ _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inr ⟨hS, hk⟩))⟩⟩
  | t15 i k j rst hM _ _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inl ⟨hM, hk⟩))⟩⟩
  | t16 i k j rst hS _ _ _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inr ⟨hS, hk⟩))⟩⟩
  | t17 i k v rst hM _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inl ⟨hM, hk⟩))⟩⟩
  | t18 i k j v rst hM _ _ hne hk =>
    exact ⟨i, k, Or.inr ⟨decide_eq_false hne, Or.inr (Or.inr (Or.inl ⟨hM, hk⟩))⟩⟩

/-- **Nessuno stato di `A` è raggiungibile.** Se `s` è raggiungibile ha le code allineate
(`synced_of_reachable`), quindi una vista in `viewA`, contro la ricerca all'indietro. -/
theorem A_unreachable {n} {s : MSIState n} (h : A s) : ¬ MSI.reachable s := fun hreach =>
  viewA_unreachable s (A_view (synced_of_reachable hreach) h)
    (hreach (default : MSIState n) msi_init_default)

/-! ## 4. I 18 diamanti

Per ogni teorema di `MSI.lean` che non converge: se i due passi partono da `s`, e vale la
condizione di blocco, `s` non è raggiungibile. La dimostrazione è sempre la stessa: le guardie
dei due passi danno il costruttore di `A`, e `A_unreachable` conclude. -/

variable {n : Nat} {s s' s'' : MSIState n}

/-- 1. `comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1`: sempre bloccato. -/
theorem diamond_1 {i₁ i₂ : Fin n} {v : Value}
    (h₁ : msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'') :
    ¬ MSI.reachable s := by
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨j₂, hj₂, hall, _⟩ := grantM_inv h₂
  exact A_unreachable (A.t1 s i₁ i₂ j₁ j₂ v hj₁ hj₂ hall)

/-- 2. `comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq2`: sempre bloccato. -/
theorem diamond_2 {i₁ i₂ : Fin n} {v : Value}
    (h₁ : msi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'') :
    ¬ MSI.reachable s := by
  have hI := grantS_rowI h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeM_inv h₁
  obtain ⟨j₂, hj₂, hnoM, _⟩ := grantS_inv h₂
  exact A_unreachable (A.t2 s i₁ i₂ j₁ j₂ v hj₁ hj₂ hI hnoM)

/-- 3. `comm_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq1`: bloccato sullo stesso indice. -/
theorem diamond_3 {i : Fin n}
    (h₁ : msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) s'') :
    ¬ MSI.reachable s := by
  obtain ⟨j₁, hj₁, _⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, hall, _⟩ := grantM_inv h₂
  exact A_unreachable (A.t3 s i j₁ j₂ hj₁ hj₂ hall)

/-- 4. `comm_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq2`: stesso indice, cache non in `I`. -/
theorem diamond_4 {i : Fin n}
    (h₁ : msi_step_internal s (.parent (.upd_queue .downgrade_from_S_rq1S i)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) s'')
    (hc : ¬((s.caches i).state = Bstate.I)) : ¬ MSI.reachable s := by
  have hI := grantS_rowI h₂
  obtain ⟨j₁, hj₁, _⟩ := downgradeS_inv h₁
  obtain ⟨j₂, hj₂, hnoM, _⟩ := grantS_inv h₂
  exact A_unreachable (A.t4 s i j₁ j₂ hj₁ hj₂ hI hnoM hc)

/-- 5. `comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1`: la cache di uno dei
due richiedenti non è in `I`. -/
theorem diamond_5 {i₁ i₂ i : Fin n}
    (h₁ : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) s'')
    (hi : i = i₁ ∨ i = i₂) (hc : ¬((s.caches i).state = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨j₁, hj₁, hall, _⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, _, _⟩ := grantM_inv h₂
  exact A_unreachable (A.t5 s i₁ i₂ i j₁ j₂ hj₁ hj₂ hall hi hc)

/-- 6. `comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq2`: la cache di uno dei
due richiedenti non è in `I`. -/
theorem diamond_6 {i₁ i₂ i : Fin n}
    (h₁ : msi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i₂)) s'')
    (hi : i = i₁ ∨ i = i₂) (hc : ¬((s.caches i).state = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨j₁, hj₁, hall, _⟩ := grantM_inv h₁
  obtain ⟨j₂, hj₂, _, _⟩ := grantS_inv h₂
  exact A_unreachable (A.t6 s i₁ i₂ i j₁ j₂ hj₁ hj₂ hall hi hc)

/-- 7. `comm_upgrade_to_M_data_avilable_rq2_upgrade_to_M_data_avilable_rq2`: stesso indice, due
`rqS` diversi (`s' ≠ s''`), cache non in `I`. -/
theorem diamond_7 {i : Fin n}
    (h₁ : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) s')
    (h₂ : msi_step_internal s (.parent (.upd_queue .upgrade_to_S_data_avilable_rq1S i)) s'')
    (hne : s' ≠ s'') (hc : ¬((s.caches i).state = Bstate.I)) : ¬ MSI.reachable s := by
  have hI := grantS_rowI h₁
  obtain ⟨j₁, hj₁, hnoM, rfl⟩ := grantS_inv h₁
  obtain ⟨j₂, hj₂, _, rfl⟩ := grantS_inv h₂
  by_cases hj : j₁ = j₂
  · subst hj; exact absurd rfl hne
  · exact A_unreachable (A.t7 s i j₁ j₂ hj hj₁ hj₂ hI hnoM hc)

/-- 8. `comm_upgrade_from_I_rq_upgrade_from_I_rs`: la riga di un `k ≠ i` non è a `I`. -/
theorem diamond_8 {i k : Fin n} {v : Value}
    (_h₁ : msi_step_internal s (.cache .upgrade_from_I_rq i) s')
    (h₂ : msi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'')
    (hne : i ≠ k) (hk : ¬(s.parent.shared_state k = Bstate.I)) : ¬ MSI.reachable s := by
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j hj hI => exact A_unreachable (A.t8 s i k j v hI hj hne hk)

/-- 9. `comm_upgrade_from_I_rq1_upgrade_from_I_rsS`: il `rsS` porta il valore del parent e la riga
di un `k ≠ i` è a `M`. -/
theorem diamond_9 {i k : Fin n} {v : Value}
    (_h₁ : msi_step_internal s (.cache .upgrade_from_I_rqS i) s')
    (h₂ : msi_step_internal s (.cache (.upgrade_from_I_rsS v) i) s'')
    (hv : v = s.parent.value) (hne : i ≠ k) (hk : s.parent.shared_state k = Bstate.M) :
    ¬ MSI.reachable s := by
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rsS _ j hj hI => exact A_unreachable (A.t9 s i k j v hI hj hv hne hk)

/-- 10. `comm_upgrade_from_I_rs_upgrade_from_I_rs`: due `rsM` diversi (`s' ≠ s''`). -/
theorem diamond_10 {i : Fin n} {v₁ v₂ : Value}
    (h₁ : msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s')
    (h₂ : msi_step_internal s (.cache (.upgrade_from_I_rs v₂) i) s'')
    (hne : s' ≠ s'') : ¬ MSI.reachable s := by
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI =>
        cases hc₂ with
        | upgrade_from_I_rs _ j₂ hj₂ _ =>
          by_cases hj : j₁ = j₂
          · subst hj; rw [hj₁] at hj₂; cases hj₂; exact absurd rfl hne
          · exact A_unreachable (A.t10 s i j₁ j₂ v₁ v₂ hI hj₁ hj₂ hj)

/-- 11. `comm_upgrade_from_I_rs_upgrade_from_I_rsS`: sempre bloccato. -/
theorem diamond_11 {i : Fin n} {v₁ v₂ : Value}
    (h₁ : msi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s')
    (h₂ : msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'') : ¬ MSI.reachable s := by
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rs _ j₁ hj₁ hI =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j₂ hj₂ _ =>
          exact A_unreachable (A.t11 s i j₁ j₂ v₁ v₂ hI hj₁ hj₂)

/-- 12. `comm_upgrade_from_I_rsS_upgrade_from_I_rsS`: due `rsS` diversi (`s' ≠ s''`). -/
theorem diamond_12 {i : Fin n} {v₁ v₂ : Value}
    (h₁ : msi_step_internal s (.cache (.upgrade_from_I_rsS v₁) i) s')
    (h₂ : msi_step_internal s (.cache (.upgrade_from_I_rsS v₂) i) s'')
    (hne : s' ≠ s'') : ¬ MSI.reachable s := by
  cases h₁ with
  | cache c₁ _ _ hc₁ =>
    cases h₂ with
    | cache c₂ _ _ hc₂ =>
      cases hc₁ with
      | upgrade_from_I_rsS _ j₁ hj₁ hI =>
        cases hc₂ with
        | upgrade_from_I_rsS _ j₂ hj₂ _ =>
          by_cases hj : j₁ = j₂
          · subst hj; rw [hj₁] at hj₂; cases hj₂; exact absurd rfl hne
          · exact A_unreachable (A.t12 s i j₁ j₂ v₁ v₂ hI hj₁ hj₂ hj)

/-- 13. `comm_ext_ld_rs_rq_data_not_available`: stessa cache, la riga di un `k ≠ i` non è a `I`. -/
theorem diamond_13 {i k : Fin n} {w : Value}
    (h₁ : msi_step_external s (.cache (.ld_rs w) i) s')
    (h₂ : msi_step_internal s (.cache .rq_data_not_available i) s'')
    (hne : i ≠ k) (hk : ¬(s.parent.shared_state k = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | rq_data_not_available hM =>
      cases hc₁ with
      | ld_rq_data_available1 _ _ hS => exact Bstate.noConfusion (hS.symm.trans hM)
      | ld_rq_data_available rst hrq _ => exact A_unreachable (A.t13 s i k rst hM hrq hne hk)

/-- 14. `comm_ext_ld_rs_rq_data_not_available1`: stessa cache, la load risponde il valore del
parent, la riga di un `k ≠ i` è a `M`. -/
theorem diamond_14 {i k : Fin n} {w : Value}
    (h₁ : msi_step_external s (.cache (.ld_rs w) i) s')
    (h₂ : msi_step_internal s (.cache .ld_rq_data_not_availableS i) s'')
    (hw : w = s.parent.value) (hne : i ≠ k) (hk : s.parent.shared_state k = Bstate.M) :
    ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | rq_data_not_available1 hS =>
      cases hc₁ with
      | ld_rq_data_available1 rst hrq _ => exact A_unreachable (A.t14 s i k rst hS hrq hw hne hk)
      | ld_rq_data_available _ _ hM => exact Bstate.noConfusion (hM.symm.trans hS)

/-- 15. `comm_ext_ld_rs_downgrade_from_M_rs`: stessa cache, la riga di un `k ≠ i` non è a `I`. -/
theorem diamond_15 {i k : Fin n} {w : Value}
    (h₁ : msi_step_external s (.cache (.ld_rs w) i) s')
    (h₂ : msi_step_internal s (.cache .downgrade_from_M_rs i) s'')
    (hne : i ≠ k) (hk : ¬(s.parent.shared_state k = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | downgrade_from_M_rs j hj hM =>
      cases hc₁ with
      | ld_rq_data_available1 _ _ hS => exact Bstate.noConfusion (hS.symm.trans hM)
      | ld_rq_data_available rst hrq _ => exact A_unreachable (A.t15 s i k j rst hM hj hrq hne hk)

/-- 16. `comm_ext_ld_rs_downgrade_from_M_rs1`: stessa cache, la load risponde il valore del
parent, la riga di un `k ≠ i` è a `M`. -/
theorem diamond_16 {i k : Fin n} {w : Value}
    (h₁ : msi_step_external s (.cache (.ld_rs w) i) s')
    (h₂ : msi_step_internal s (.cache .downgrade_from_S_rsS i) s'')
    (hw : w = s.parent.value) (hne : i ≠ k) (hk : s.parent.shared_state k = Bstate.M) :
    ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | downgrade_from_M_rs1 j hj hS =>
      cases hc₁ with
      | ld_rq_data_available1 rst hrq _ =>
        exact A_unreachable (A.t16 s i k j rst hS hj hrq hw hne hk)
      | ld_rq_data_available _ _ hM => exact Bstate.noConfusion (hM.symm.trans hS)

/-- 17. `comm_ext_st_rs_rq_data_not_available`: stessa cache, la riga di un `k ≠ i` non è a `I`. -/
theorem diamond_17 {i k : Fin n}
    (h₁ : msi_step_external s (.cache .st_rs i) s')
    (h₂ : msi_step_internal s (.cache .rq_data_not_available i) s'')
    (hne : i ≠ k) (hk : ¬(s.parent.shared_state k = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | rq_data_not_available hM =>
      cases hc₁ with
      | st_rq_M_state v rst hrq _ => exact A_unreachable (A.t17 s i k v rst hM hrq hne hk)

/-- 18. `comm_ext_st_rs_downgrade_from_M_rs`: stessa cache, la riga di un `k ≠ i` non è a `I`. -/
theorem diamond_18 {i k : Fin n}
    (h₁ : msi_step_external s (.cache .st_rs i) s')
    (h₂ : msi_step_internal s (.cache .downgrade_from_M_rs i) s'')
    (hne : i ≠ k) (hk : ¬(s.parent.shared_state k = Bstate.I)) : ¬ MSI.reachable s := by
  obtain ⟨c₁, hc₁, _⟩ := ext_inv h₁
  cases h₂ with
  | cache c₂ _ _ hc₂ =>
    cases hc₂ with
    | downgrade_from_M_rs j hj hM =>
      cases hc₁ with
      | st_rq_M_state v rst hrq _ => exact A_unreachable (A.t18 s i k j v rst hM hj hrq hne hk)

end AClosure

/-! ## Controllo: nessuna dipendenza da `badView` -/

open Lean Elab Command in
/-- `#no_badView thm₁ thm₂ …`: controlla che le dimostrazioni non dipendano, neanche
indirettamente, da `MSIView.badView`. -/
elab "#no_badView " ids:ident+ : command => do
  let env ← getEnv
  let forbidden : Name := ``MSIView.badView
  let mut bad : Array Name := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[n]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        for d in ci.type.getUsedConstants do todo := todo.push d
        if let some v := ci.value? (allowOpaque := true) then
          for d in v.getUsedConstants do todo := todo.push d
    if seen.contains forbidden then bad := bad.push n
  if bad.isEmpty then
    logInfo m!"#no_badView: nessuno dei {ids.size} teoremi dipende da `badView`."
  else
    throwError "#no_badView: dipendono da `badView`: {bad}"

#no_badView AClosure.viewA_unreachable AClosure.A_unreachable
  AClosure.diamond_1 AClosure.diamond_2 AClosure.diamond_3 AClosure.diamond_4 AClosure.diamond_5
  AClosure.diamond_6 AClosure.diamond_7 AClosure.diamond_8 AClosure.diamond_9 AClosure.diamond_10
  AClosure.diamond_11 AClosure.diamond_12 AClosure.diamond_13 AClosure.diamond_14
  AClosure.diamond_15 AClosure.diamond_16 AClosure.diamond_17 AClosure.diamond_18

#print axioms AClosure.viewA_unreachable
#print axioms AClosure.A_unreachable
#print axioms AClosure.diamond_1
#print axioms AClosure.diamond_18
