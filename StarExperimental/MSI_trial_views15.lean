import StarExperimental.MSI_trial_views

/-!
# `MSI_trial`: anche "riga registrata senza portatore" è irraggiungibile

Le 13 viste cattive di `MSIView.badView` più i due pattern 14–15 del modello a bag
(`MSI_bag_def.badView`): una riga `M` di `i` senza cache in `M` né token `M` in volo, una riga `S` di
`i` senza cache in `S` né token `S` in volo. La tattica di scoperta li aveva trovati irraggiungibili
nel modello a lista (`MSI_discover.lean`); qui la tattica backward li certifica per `MSI_trial`, con
passi interni ed esterni.

Servono al lemma di progresso di `commutes_method_rule_upto_on`: se il parent registra un detentore,
c'è davvero qualcuno che può rispondere all'invalidate.
-/

open THEORY Relation BackwardGen MSIView

namespace MSITrial

variable {n : Nat}

/-- `badView` (le 13 clausole, copiate perché la tattica srotola solo la testa del predicato) più i
pattern 14–15: riga `M` senza cache in `M` né token `M`, riga `S` senza cache in `S` né token `S`. -/
def badView15 (v : View) : Prop :=
  v.m0 = .many ∨ v.s0 = .many ∨ (v.m0 ≠ .zero ∧ v.s0 ≠ .zero)
  ∨ (v.m0 ≠ .zero ∧ v.d0 ≠ .M)
  ∨ (v.s0 ≠ .zero ∧ v.d0 ≠ .S)
  ∨ (v.c0 = .M ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .M))
  ∨ (v.c0 = .S ∧ (v.m0 ≠ .zero ∨ v.s0 ≠ .zero ∨ v.d0 ≠ .S))
  ∨ (v.eq = false ∧ v.d0 = .M ∧ v.d1 ≠ .I)
  ∨ (v.eq = false ∧ v.d0 = .S ∧ v.d1 = .M)
  ∨ (v.eq = false ∧ v.c0 = .M ∧ v.d1 ≠ .I)
  ∨ (v.eq = false ∧ v.c0 = .S ∧ v.d1 = .M)
  ∨ (v.eq = false ∧ v.m0 ≠ .zero ∧ v.d1 ≠ .I)
  ∨ (v.eq = false ∧ v.s0 ≠ .zero ∧ v.d1 = .M)
  ∨ (v.d0 = .M ∧ v.c0 ≠ .M ∧ v.m0 = .zero)
  ∨ (v.d0 = .S ∧ v.c0 ≠ .S ∧ v.s0 = .zero)

theorem badView15_of_badView {v : View} (h : badView v) : badView15 v := by
  unfold badView at h; unfold badView15
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))

theorem badView15_p14 {v : View} (h1 : v.d0 = .M) (h2 : v.c0 ≠ .M) (h3 : v.m0 = .zero) : badView15 v := by
  unfold badView15
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))))))))))))

theorem badView15_p15 {v : View} (h1 : v.d0 = .S) (h2 : v.c0 ≠ .S) (h3 : v.s0 = .zero) : badView15 v := by
  unfold badView15
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩)))))))))))))

def msiSetup15 (n : Nat) :
    SymSetup (MSIState n) (IEvent n ⊕ MSIExternalEvent n) (Fin n) View where
  trans := step_any
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step_any hs h
  view := msiView
  bad := badView15
  s0 := default
  inv0 := synced_default

set_option maxHeartbeats 0 in
/-- Il risultato della tattica con le 15 viste cattive. -/
theorem badView15_unreachable_from_default : (msiSetup15 n).Unreachable := by
  backward_search_gen (msiSetup15 _)
    simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
          update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
          isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
          Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
    fwd [countP_eraseIdx_grantM, countP_eraseIdx_grantS,
         countP_eraseIdx_releaseM, countP_eraseIdx_releaseS]
    split Cnt.ofCount_cases Cnt.ofCount
    upd update_Fin
    inv [step_any, step_int, msi_step_external, cache_msi_step, cache_step, parent_msi_step]

/-- Uno stato con una vista cattiva (15 pattern) non è raggiungibile. -/
theorem badView15_unreachable (s : MSIState n) (h : ∃ i j, badView15 (msiView s i j)) : ¬ Reach s :=
  fun hr => badView15_unreachable_from_default s h (reach_iff_setup.mp hr)

/-- Riga `M` di `i` ⇒ la cache `i` è in `M` o un token `M` è in volo per `i`. -/
theorem bearer_of_rowM {s : MSIState n} {i : Fin n} (hr : Reach s)
    (hd : s.parent.shared_state i = Bstate.M) :
    (s.caches i).state = Bstate.M ∨ muMsgs s.parent i ≠ 0 := by
  by_contra hno
  push_neg at hno
  apply badView15_unreachable s ⟨i, i, badView15_p14 hd hno.1 ?_⟩ hr
  show Cnt.ofCount (muMsgs s.parent i) = .zero
  rw [Cnt.ofCount_eq_zero]; exact hno.2

/-- Riga `S` di `i` ⇒ la cache `i` è in `S` o un token `S` è in volo per `i`. -/
theorem bearer_of_rowS {s : MSIState n} {i : Fin n} (hr : Reach s)
    (hd : s.parent.shared_state i = Bstate.S) :
    (s.caches i).state = Bstate.S ∨ sigMsgs s.parent i ≠ 0 := by
  by_contra hno
  push_neg at hno
  apply badView15_unreachable s ⟨i, i, badView15_p15 hd hno.1 ?_⟩ hr
  show Cnt.ofCount (sigMsgs s.parent i) = .zero
  rw [Cnt.ofCount_eq_zero]; exact hno.2

end MSITrial
