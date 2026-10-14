import StarExperimental.MSI_trial_dec
import StarExperimental.MSI_trial_old_pp
import StarExperimental.MSI_trial_old_cc
import StarExperimental.MSI_trial_old_pc1
import StarExperimental.MSI_trial_old_pc2

/-!
# `MSI_trial`: sollevamento dei picchi con cammini lunghi

Per ogni coppia di regole di `MSI_def` il teorema `old_*` (copia di `MSI.lean`) dà il ricongiungimento
con passi di `MSI_def`; qui lo si trasporta ai passi di `MSI_trial` (`step_int_old` in entrata,
`step_int_of_old_*` in uscita) e lo si mette nella forma `DecJoin` di `DecreasingDiagrams`.
Qui i picchi il cui ricongiungimento in `MSI.lean` è un cammino di più passi (grant/grant,
grant S/invalidate S, consumo/grant S): si sollevano passo per passo e si mettono nella forma
`big`/`Lt` di `DecreasingDiagrams`.

Nessuno dei cammini contiene richieste (etichetta 7), quindi ogni passo di cache si solleva con
`step_int_of_old_cache _ ⟨nofun, nofun⟩` e ogni passo del parent con `step_int_of_old_parent`.
Le etichette dei passi sollevati sono: presa 3, rilascio/cessione 2, consumo 1, grant 4, invalidate 6.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

/-- Sollevamento di `old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq2` (consumo di un `rsIσ`
all'indice `i₁` × grant di `S` all'indice `i₂`, etichette 1 e 4).
* Quadrato (indici o posizioni indipendenti): `DecJoin.square` con i due passi scambiati.
* Cammino lungo (il grant a `i₂` è reso stantio dal consumo): `DecJoin.mix` con `1 < 4`; dal lato
  `s'` si fa SUBITO il passo di etichetta 4 (il grant a `i₂`) e poi presa (3), rilascio spontaneo (2),
  consumo (1), tutti `< 4`; dal lato `s''` si fanno consumo (1), presa (3), rilascio (2), consumo (1),
  tutti `< 4`.
* `s' = s''`: secondo disgiunto.
* Code non allineate o vista cattiva: `¬ Reach s`. -/
theorem peak_downgrade_from_S_rq1S_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .downgrade_from_S_rq1S i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 1 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_downgrade_from_M_rq2_upgrade_to_M_data_avilable_rq2 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop])) with ⟨d, hc, hb⟩ | h | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · obtain ⟨t₁, t₂, t₃, u₁, u₂, u₃, d, a1, a2, a3, a4, b1, b2, b3, b4⟩ := h
    exact Or.inl (DecJoin.mix (by decide)
      (Or.inr (lstep_of' (step_int_of_old_parent b1) rfl))
      (ltStar_cons (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
        (ltStar_cons (step_int_of_old_cache b3 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_single (step_int_of_old_parent b4) (by simp [lab]))))
      (ltStar_cons (step_int_of_old_parent a1) (by simp [lab])
        (ltStar_cons (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a3 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a4) (by simp [lab]))))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1` (grant di `M`
a `i₁` × grant di `M` a `i₂`, etichette 4 e 4).
* Cammino 7+7: `DecJoin.top` con due passi grandi di livello 4: da `s'` presa (3), rilascio (2),
  consumo (1) a `i₁`, poi il passo `= 4` (grant a `i₂`), poi presa (3), rilascio (2), consumo (1) a `i₂`;
  da `s''` lo stesso con `i₁` e `i₂` scambiati. I due cammini riconvergono allo stesso stato.
* `s' = s''`: secondo disgiunto.
* Vista cattiva: `¬ Reach s`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₂) s'') :
    DecJoin 4 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop])) with h | heq | hun
  · obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, d,
      a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7⟩ := h
    exact Or.inl (DecJoin.top
      (big_mk
        (ltStar_cons (step_int_of_old_cache a1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent a4) rfl))
        (ltStar_cons (step_int_of_old_cache a5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a7) (by simp [lab])))))
      (big_mk
        (ltStar_cons (step_int_of_old_cache b1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent b4) rfl))
        (ltStar_cons (step_int_of_old_cache b5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b7) (by simp [lab]))))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq2` (grant di `M`
a `i₁` × grant di `S` a `i₂`, etichette 4 e 4).
* Cammino 7+7: `DecJoin.top` con due passi grandi di livello 4: da `s'` presa di `M` (3), rilascio da
  `M` (2), consumo (1) a `i₁`, poi il passo `= 4` (grant di `S` a `i₂`), poi presa di `S` (3), rilascio
  da `S` (2), consumo (1) a `i₂`; da `s''` prima il ciclo di `i₂`, poi il grant di `M` a `i₁` e il ciclo
  di `i₁`.
* `s' = s''`: secondo disgiunto.
* Vista cattiva: `¬ Reach s`. -/
theorem peak_upgrade_to_M_data_avilable_rq1_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_M_data_avilable_rq1 i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 4 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq2 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop])) with h | heq | hun
  · obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, d,
      a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7⟩ := h
    exact Or.inl (DecJoin.top
      (big_mk
        (ltStar_cons (step_int_of_old_cache a1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent a4) rfl))
        (ltStar_cons (step_int_of_old_cache a5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a7) (by simp [lab])))))
      (big_mk
        (ltStar_cons (step_int_of_old_cache b1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent b4) rfl))
        (ltStar_cons (step_int_of_old_cache b5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b7) (by simp [lab]))))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_data_avilable_rq2` (grant di `S`
a `i₁` × grant di `S` a `i₂`, etichette 4 e 4).
* Quadrato (le due richieste sono indipendenti): `DecJoin.square` con i due grant scambiati.
* Cammino 7+7 (stesso indice, due `rqS` in coda): `DecJoin.top` con due passi grandi di livello 4:
  da `s'` presa (3), rilascio (2), consumo (1) a `i₁`, poi il passo `= 4` (grant a `i₂`), poi presa (3),
  rilascio (2), consumo (1) a `i₂`; da `s''` lo stesso con `i₁` e `i₂` scambiati.
* `s' = s''`: secondo disgiunto.
* Vista cattiva: `¬ Reach s`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_upgrade_to_S_data_avilable_rq1S {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₂) s'') :
    DecJoin 4 4 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_data_avilable_rq2 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop])) with ⟨d, hc, hb⟩ | h | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, d,
      a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7⟩ := h
    exact Or.inl (DecJoin.top
      (big_mk
        (ltStar_cons (step_int_of_old_cache a1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent a4) rfl))
        (ltStar_cons (step_int_of_old_cache a5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache a6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent a7) (by simp [lab])))))
      (big_mk
        (ltStar_cons (step_int_of_old_cache b1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b3) (by simp [lab]))))
        (Or.inr (lstep_of' (step_int_of_old_parent b4) rfl))
        (ltStar_cons (step_int_of_old_cache b5 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_cons (step_int_of_old_cache b6 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
            (ltStar_single (step_int_of_old_parent b7) (by simp [lab]))))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

/-- Sollevamento di `old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1` (grant di `S` a
`i₁` × invalidate di tutti gli `S` per una `rqM` di `i₂`, etichette 4 e 6).
* Quadrato (l'invalidate non tocca la riga di `i₁`, o viceversa): `DecJoin.square` con i due passi
  scambiati.
* Cammino 2+2, prima variante: `DecJoin.mix` con `4 < 6`; dal lato `s'` si fa SUBITO il passo di
  etichetta 6 (l'invalidate), poi presa di `S` (3) e cessione su invalidate (2) a `i₁`; dal lato `s''`
  grant (4), presa (3), cessione (2), tutti `< 6`.
* Cammino 2+2, seconda variante (la cache `i₁` cede prima di prendere): come sopra con cessione (2) e
  presa (3) scambiate.
* `s' = s''`: secondo disgiunto.
* Code non allineate o vista cattiva: `¬ Reach s`. -/
theorem peak_upgrade_to_S_data_avilable_rq1S_invalid_allS {s s' s'' : MSIState n}
    (h1 : step_int s (.parent .upgrade_to_S_data_avilable_rq1S i₁) s') (h2 : step_int s (.parent .invalid_allS i₂) s'') :
    DecJoin 4 6 s' s'' ∨ s' = s'' ∨ ¬ Reach s := by
  rcases old_upgrade_to_M_data_avilable_rq2_upgrade_to_M_invalid_all1 (step_int_old h1 (by simp [IEvent.isDrop]))
      (step_int_old h2 (by simp [IEvent.isDrop])) with ⟨d, hc, hb⟩ | h | h | heq | hun
  · exact Or.inl (DecJoin.square (step_int_of_old_parent hb) (step_int_of_old_parent hc) rfl rfl)
  · obtain ⟨x, y, t₁, u₁, d, hx, hy, a1, a2, b1, b2⟩ := h
    exact Or.inl (DecJoin.mix (by decide)
      (Or.inr (lstep_of' (step_int_of_old_parent hy) rfl))
      (ltStar_cons (step_int_of_old_cache b1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
        (ltStar_single (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))
      (ltStar_cons (step_int_of_old_parent hx) (by simp [lab])
        (ltStar_cons (step_int_of_old_cache a1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_single (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))))
  · obtain ⟨x, y, t₁, u₁, d, hx, hy, a1, a2, b1, b2⟩ := h
    exact Or.inl (DecJoin.mix (by decide)
      (Or.inr (lstep_of' (step_int_of_old_parent hy) rfl))
      (ltStar_cons (step_int_of_old_cache b1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
        (ltStar_single (step_int_of_old_cache b2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))
      (ltStar_cons (step_int_of_old_parent hx) (by simp [lab])
        (ltStar_cons (step_int_of_old_cache a1 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])
          (ltStar_single (step_int_of_old_cache a2 ⟨nofun, nofun⟩) (by simp [lab, CEvent.ofOld])))))
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hun)

end MSITrial
