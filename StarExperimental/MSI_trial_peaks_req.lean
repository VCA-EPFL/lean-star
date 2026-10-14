import StarExperimental.MSI_trial_dec
import StarExperimental.MSI_trial_old_pp
import StarExperimental.MSI_trial_old_cc
import StarExperimental.MSI_trial_old_pc1
import StarExperimental.MSI_trial_old_pc2

/-!
# `MSI_trial`: sollevamento dei picchi con una richiesta

Per ogni coppia di regole di `MSI_def` il teorema `old_*` (copia di `MSI.lean`) dà il ricongiungimento
con passi di `MSI_def`; qui lo si trasporta ai passi di `MSI_trial` (`step_int_old` in entrata,
`step_int_of_old_*` in uscita) e lo si mette nella forma `DecJoin` di `DecreasingDiagrams`.
Qui i picchi in cui uno dei due passi è una richiesta: la ripetizione della richiesta dall'altro
stato deve rispettare la guardia nuova (`req_guard_preserved`), e i casi sulla stessa cache sono
vuoti o identici.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

/-- Sollevamento di `old_rq_data_not_available_upgrade_from_I_rq`.
Il rilascio spontaneo da `M` richiede `state = M`, la richiesta di `M` richiede `state = I`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_rq_data_not_available_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .upgrade_from_I_rq i) s'') :
    DecJoin 2 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available hM =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq hI _ _ _ => exact nomatch hM.symm.trans hI

/-- Sollevamento di `old_rq_data_not_available_upgrade_from_I_rq1`.
Il rilascio spontaneo da `M` richiede `state = M`, la richiesta di `S` richiede `state = I`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_rq_data_not_available_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .rq_data_not_available i) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i) s'') :
    DecJoin 2 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available hM =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq1 hI _ _ _ => exact nomatch hM.symm.trans hI

/-- Sollevamento di `old_rq_data_not_available1_upgrade_from_I_rq`.
Il rilascio spontaneo da `S` richiede `state = S`, la richiesta di `M` richiede `state = I`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_ld_rq_data_not_availableS_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache .upgrade_from_I_rq i) s'') :
    DecJoin 2 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available1 hS =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq hI _ _ _ => exact nomatch hS.symm.trans hI

/-- Sollevamento di `old_rq_data_not_available1_upgrade_from_I_rq1`.
Il rilascio spontaneo da `S` richiede `state = S`, la richiesta di `S` richiede `state = I`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_ld_rq_data_not_availableS_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .ld_rq_data_not_availableS i) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i) s'') :
    DecJoin 2 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available1 hS =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq1 hI _ _ _ => exact nomatch hS.symm.trans hI

/-- Sollevamento di `old_upgrade_from_I_rq_upgrade_from_I_rq`. Due richieste di `M` della stessa cache `i`: è lo stesso passo
(entrambe accodano `rqM` alla stessa `queue_cp`), quindi `s' = s''` (secondo disgiunto). Non si usa il
quadrato del teorema vecchio: in `MSI_trial` una seconda richiesta è vietata dalla guardia `¬ pending`. -/
theorem peak_upgrade_from_I_rq_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache .upgrade_from_I_rq i) s'') :
    DecJoin 7 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq _ _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq _ _ _ _ => exact Or.inr (Or.inl rfl)

/-- Sollevamento di `old_upgrade_from_I_rq_downgrade_from_M_rs`.
La richiesta di `M` richiede `state = I`, il rilascio su invalidate da `M` richiede `state = M`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_upgrade_from_I_rq_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 7 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq hI _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs _ _ hM => exact nomatch hI.symm.trans hM

/-- Sollevamento di `old_upgrade_from_I_rq_downgrade_from_M_rs1`.
La richiesta di `M` richiede `state = I`, il rilascio su invalidate da `S` richiede `state = S`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_upgrade_from_I_rq_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rq i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 7 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq hI _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs1 _ _ hS => exact nomatch hI.symm.trans hS

/-- Sollevamento di `old_upgrade_from_I_rq1_upgrade_from_I_rq1`. Due richieste di `S` della stessa cache `i`: è lo stesso passo
(entrambe accodano `rqS` alla stessa `queue_cp`), quindi `s' = s''` (secondo disgiunto). Non si usa il
quadrato del teorema vecchio: in `MSI_trial` una seconda richiesta è vietata dalla guardia `¬ pending`. -/
theorem peak_upgrade_from_I_rqS_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rqS i) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i) s'') :
    DecJoin 7 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq1 _ _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rq1 _ _ _ _ => exact Or.inr (Or.inl rfl)

/-- Sollevamento di `old_upgrade_from_I_rq1_downgrade_from_M_rs`.
La richiesta di `S` richiede `state = I`, il rilascio su invalidate da `M` richiede `state = M`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_upgrade_from_I_rqS_downgrade_from_M_rs {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rqS i) s') (h2 : step_int s (.cache .downgrade_from_M_rs i) s'') :
    DecJoin 7 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq1 hI _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs _ _ hM => exact nomatch hI.symm.trans hM

/-- Sollevamento di `old_upgrade_from_I_rq1_downgrade_from_M_rs1`.
La richiesta di `S` richiede `state = I`, il rilascio su invalidate da `S` richiede `state = S`.
Picco vuoto: nessun disgiunto serve, si deriva `False`
dalle due guardie sullo stato della stessa cache `i`. -/
theorem peak_upgrade_from_I_rqS_downgrade_from_S_rsS {s s' s'' : MSIState n}
    (h1 : step_int s (.cache .upgrade_from_I_rqS i) s') (h2 : step_int s (.cache .downgrade_from_S_rsS i) s'') :
    DecJoin 7 2 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  cases h1 with
  | cache _ _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq1 hI _ _ _ =>
      cases h2 with
      | cache _ _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs1 _ _ hS => exact nomatch hI.symm.trans hS

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_from_I_rq`: consumo di `rsIμ v` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_downgrade_from_M_rq1_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 1 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_downgrade_from_M_rq1_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq1_upgrade_from_I_rq1`: consumo di `rsIμ v` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_downgrade_from_M_rq1_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.downgrade_from_M_rq1 v) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 1 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_downgrade_from_M_rq1_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_from_I_rq`: consumo di `rsIσ` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 1 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_downgrade_from_M_rq2_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_from_I_rq1`: consumo di `rsIσ` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 1 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_downgrade_from_M_rq2_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq`: grant di `M` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 4 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq1`: grant di `M` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 4 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq`: grant di `S` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 4 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq1`: grant di `S` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 4 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_from_I_rq`: invalidate `rqIμ` verso `k` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all_upgrade_from_I_rq1`: invalidate `rqIμ` verso `k` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_upgrade_to_M_invalid_all_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_M_invalid_all k) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_from_I_rq`: invalidate `rqIσ` del proprietario su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_invalid_allS_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all1_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all1_upgrade_from_I_rq1`: invalidate `rqIσ` del proprietario su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_invalid_allS_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .invalid_allS i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all1_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_upgrade_from_I_rq`: invalidate `rqIσ` verso `k` su `i₁` e richiesta di `M` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsM_step_int`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rq {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rq i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all2_upgrade_from_I_rq (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqM_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨fun _ => wantsM_step_int h1 hw, fun h => nomatch h⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_invalid_all2_upgrade_from_I_rq1`: invalidate `rqIσ` verso `k` su `i₁` e richiesta di `S` della cache `i₂`.
Se le code non sono allineate: terzo disgiunto (`not_reach_of_not_synced`). Altrimenti il teorema vecchio dà
il quadrato (primo disgiunto, `DecJoin.square`), `s' = s''` (secondo) o `¬ Reach s` (terzo). Nel quadrato la
richiesta è ripetuta da `s'`: la guardia nuova (`¬ pending`, `¬ grantInFlight`) si trasporta lungo il passo del
parent con `req_guard_preserved` (che esclude da sé il caso di un grant verso `i₂`), la domanda con `wantsS_step_int`. -/
theorem peak_upgrade_to_S_invalid_2_rq1S_upgrade_from_I_rqS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent (.upgrade_to_S_invalid_2_rq1S k) i₁) s') (h2 : step_int s (.cache .upgrade_from_I_rqS i₂) s'') :
    DecJoin 6 7 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  by_cases hs : synced s
  swap
  · exact Or.inr (Or.inr (not_reach_of_not_synced hs))
  rcases old_upgrade_to_M_invalid_all2_upgrade_from_I_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop, CEvent.isDrop])) with ⟨d, hc, hb⟩ | heq | hun
  · obtain ⟨_, hp, hg, hw⟩ := reqS_guards h2
    obtain ⟨hp', hg'⟩ := req_guard_preserved hs h1 hp hg (fun _ h => nomatch h)
    exact Or.inl (DecJoin.square (step_int_of_old_req hb hp' hg' ⟨(fun h => nomatch h), fun _ => wantsS_step_int h1 hw⟩)
      (step_int_of_old_parent hc) rfl rfl)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

end MSITrial
