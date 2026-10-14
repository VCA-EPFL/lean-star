import StarExperimental.MSI_trial_def
import StarExperimental.MSI

/-!
# `MSI_trial`: le viste cattive sono irraggiungibili

La tattica backward di `MSI.lean` (`backward_search_gen`) girata sul setup di `MSI_trial`
(`MSITrial.msiSetup`): stessa vista e stesse viste cattive di `MSI_def`, ma la transizione è
`step_any` (passi interni di `MSI_trial`, scarti compresi, **e** passi esterni), quindi il certificato
parla della raggiungibilità di ARS `Reach`, quella che compare in `has_diamond_property_on`.
Gli scarti non cambiano la vista (gli `rqIμ`/`rqIσ` non sono token), i passi esterni nemmeno.

Da qui discendono tutte le uscite `¬ Reach s` dei diagrammi locali di `MSI_trial`.
-/

open THEORY Relation BackwardGen MSIView

namespace MSITrial

variable {n : Nat}

syntax "trial_backward_tactic" : tactic
syntax "trial_backward_tactic?" : tactic

macro_rules
  | `(tactic| trial_backward_tactic) =>
    `(tactic| backward_search_gen (msiSetup _)
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
           countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [step_any, step_int, msi_step_external, cache_msi_step, cache_step, parent_msi_step])

macro_rules
  | `(tactic| trial_backward_tactic?) =>
    `(tactic| backward_search_gen? (msiSetup _)
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
           countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [step_any, step_int, msi_step_external, cache_msi_step, cache_step, parent_msi_step])

set_option maxHeartbeats 0 in
/-- **Il risultato della tattica**: nessuno stato con una vista cattiva è raggiungibile da `default`
con passi interni ed esterni di `MSI_trial`. -/
theorem badView_unreachable_from_default : (msiSetup n).Unreachable := by
  trial_backward_tactic

/-- Uno stato con una vista cattiva non è raggiungibile (`Reach` di ARS). -/
theorem badView_unreachable (s : MSIState n) (h : ∃ i j, badView (msiView s i j)) : ¬ Reach s :=
  fun hr => badView_unreachable_from_default s h (reach_iff_setup.mp hr)

end MSITrial
