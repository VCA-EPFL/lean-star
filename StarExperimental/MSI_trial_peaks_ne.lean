import StarExperimental.MSI_trial_dec

/-!
# `MSI_trial`: due passi di cache su indici diversi commutano

Un passo di cache legge solo `caches i` e scrive solo `caches i`, `parent.queue_cip i`,
`parent.queue_pci i`. Con `i₁ ≠ i₂` i due passi toccano componenti disgiunte dello stato e si
ricongiungono in un passo: è la versione trial di `comm_cache_cache_ne` (`MSI_no_escape.lean`).
Le guardie delle richieste (`pending`, `grantInFlight`, `wantsM`/`wantsS`) guardano solo
`caches i`, che l'altro passo non tocca.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl)

namespace MSITrial

variable {n : Nat}

/-- **Due passi di cache su indici diversi**: diamante puro a un passo, per ogni coppia di regole
`c₁`, `c₂` di `cache_step`, senza alcuna ipotesi oltre a `i₁ ≠ i₂` (né `synced`, né `Reach`).
Lo stato comune `d` è `s` con le due cache aggiornate e le quattro copie delle code riallineate;
le due composizioni di `update_Fin` su indici distinti coincidono
(`comm_ext_cache_generic_aux_update_Fin_comm`). -/
theorem peak_cache_ne {s s' s'' : MSIState n} {c₁ c₂ : CEvent} {i₁ i₂ : Fin n} (hii : ¬ i₁ = i₂)
    (h1 : step_int s (.cache c₁ i₁) s') (h2 : step_int s (.cache c₂ i₂) s'') :
    ∃ d, step_int s'' (.cache c₁ i₁) d ∧ step_int s' (.cache c₂ i₂) d := by
  have hcongr : ∀ {a b b' : MSIState n} {e : IEvent n},
      step_int a e b → b = b' → step_int a e b' := fun h heq => heq ▸ h
  cases h1 with
  | cache cache₁ _ _ hc₁ =>
  cases h2 with
  | cache cache₂ _ _ hc₂ =>
  refine ⟨_, step_int.cache _ cache₁ i₁ c₁
    (by simp only [update_Fin_gso2 _ _ _ _ hii]; exact hc₁), ?_⟩
  refine hcongr (step_int.cache _ cache₂ i₂ c₂
    (by simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hii)]; exact hc₂)) ?_
  refine MSIState.ext_all ?_ ?_ ?_ ?_ ?_
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · rfl
  · intro k; rfl
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]
  · intro k; simp only [comm_ext_cache_generic_aux_update_Fin_comm _ _ _ _ _ (Ne.symm hii)]

end MSITrial
