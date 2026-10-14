import StarExperimental.MSI_bag_def
import StarExperimental.BackwardDiscover

/-! # `MSI_bag_discover`: le viste cattive di MSI *scoperte*, non assunte

`MSI_bag_def.badView_unreachable_from_default` parte dai 15 pattern di `badView` e verifica
con `bag_backward_tactic` che siano irraggiungibili. Qui si fa il contrario, con
`discover_views` (`BackwardDiscover.lean`): si parte da tutte le 486 viste senza assumere
nulla, per ognuna si fa il passo all'indietro sulle regole vere, e poi si segue il grafo dei
predecessori: le viste il cui cammino all'indietro non arriva mai alla vista iniziale sono
irraggiungibili, e formano l'insieme `U` scoperto dall'algoritmo.

Il teorema dice due cose: `U` è irraggiungibile (`UnreachableSet`), e `badView ⊆ U`, cioè i
15 pattern scritti a mano sono tutti tra le viste scoperte. Il messaggio della tattica
elenca anche le viste scoperte ma non dichiarate in `badView`, e le viste raggiungibili con
un cammino dalla vista iniziale. -/

open THEORY Relation BackwardGen

namespace MSIBag

/-- `discover_views` con i parametri del modello bag (gli stessi di `bag_backward_tactic`). -/
syntax "bag_discover_tactic" : tactic
syntax "bag_discover_tactic?" : tactic
macro_rules
  | `(tactic| bag_discover_tactic) =>
    `(tactic| discover_views (msiSetup _)
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, Multiset.countP_cons, Multiset.countP_zero,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_erase_grantM, countP_erase_grantS, countP_erase_releaseM, countP_erase_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [msi_step_any, msi_step_internal, msi_step_external, cache_msi_step,
           cache_msi_step_internal, parent_msi_step])
macro_rules
  | `(tactic| bag_discover_tactic?) =>
    `(tactic| discover_views? (msiSetup _)
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, Multiset.countP_cons, Multiset.countP_zero,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_erase_grantM, countP_erase_grantS, countP_erase_releaseM, countP_erase_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [msi_step_any, msi_step_internal, msi_step_external, cache_msi_step,
           cache_msi_step_internal, parent_msi_step])

set_option maxHeartbeats 0 in
/-- **Le viste irraggiungibili scoperte dall'algoritmo**, senza assumere `badView`: `U` è
irraggiungibile da `default` con passi interni ed esterni, e contiene tutti i pattern di
`badView`. -/
theorem discovered_views {n} :
    ∃ U : List MSIView.View, (msiSetup n).UnreachableSet U ∧ ∀ v, badView v → v ∈ U := by
  bag_discover_tactic

/-- Da qui si riottiene il risultato di `bag_backward_tactic`. -/
theorem badView_unreachable_from_default' {n} : (msiSetup n).Unreachable :=
  let ⟨U, hU, hbad⟩ := discovered_views (n := n)
  (msiSetup n).unreachable_of_set U hU hbad

end MSIBag

#print axioms MSIBag.discovered_views
#print axioms MSIBag.badView_unreachable_from_default'
