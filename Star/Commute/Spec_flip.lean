import Star.Commute.prove

open Star1

namespace Spec_flip


inductive Event where
  | ld_rq (ident : Nat) (c : Fin 2)
  | ld_rs (ident : Nat) (val : Nat) (c : Fin 2)
  | st_rq (ident : Nat) (val : Nat) (c : Fin 2)
  | st_rs (ident : Nat) (c : Fin 2)
  | null

def update_Fin {a: Type} (i' : Fin n)  (e : a) (f : Fin n -> a) : Fin n -> a :=
  fun i =>
    if i' == i then
      e
    else
      f i



@[simp]
theorem update_Fin_gso {a: Type} (i i' : Fin n)  (e : a) (f : Fin n -> a) :
  ¬(i' = i) -> update_Fin i' e f i = f i := by
    intro h1
    unfold update_Fin
    simp [*] at *

@[simp]
theorem update_Fin_gso2 {a: Type} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i = i') → update_Fin i' e f i = f i := by intros; simp [update_Fin, *]; intros; simp_all

@[simp]
theorem update_Fin_gss {a: Type} (i  : Fin n)  (e : a) (f : Fin n -> a) :
  update_Fin i e f i  = e := by
    unfold update_Fin
    simp

/-!
# Spec non determinist only methods
-/

structure Spec where
  memory : Nat
  extqueue_rq : Fin 2 -> List Event
  ident : Nat


inductive seq_step : Spec -> Event -> Spec-> Prop where
  | ld_rq : ∀ s i,
      seq_step s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | read : ∀ s t i rst v,
      s.extqueue_rq i = Event.ld_rq t i :: rst →
      seq_step s (Event.ld_rs t v i)
        { s with
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | write :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      seq_step s (Event.st_rs t i)
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq,
          memory := v }


namespace Spec_flip1


/-!
# Spec non determinist bit flip (without external percondiction) with internal rule non resposnse queue
-/

structure Spec_flip1 where
  memory : Nat
  bit : Fin 2
  extqueue_rq : Fin 2 -> List Event
  ident : Nat


inductive seq_step_flip1 : Spec_flip1 -> Event -> Spec_flip1-> Prop where
  | ld_rq : ∀ s i,
      seq_step_flip1 s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_flip1 s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | ld_rq_response : ∀ s t i rst v,
      s.extqueue_rq i = Event.ld_rq t i :: rst →
      s.bit = i →
      seq_step_flip1 s (Event.ld_rs t v i)
        { s with
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | st_rq_response :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      s.bit = i →
      seq_step_flip1 s (Event.st_rs t i)
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq,
          memory := v }



inductive seq_internal_step_flip1 : Spec_flip1 -> Spec_flip1-> Prop where
  | read : ∀ s i ,
      ¬(s.bit = i) →
      seq_internal_step_flip1 s --Event.null
        { s with bit := i}
  -- | null : ∀ s,
  --     seq_internal_step_flip1 s s


def flush (i : Spec_flip1) (s : Spec) : Prop :=
  i.memory = s.memory ∧
  i.extqueue_rq  = s.extqueue_rq ∧
  i.ident = s.ident


def rule : Spec_flip1 → Spec_flip1 → Prop := seq_internal_step_flip1

theorem relation_flush : ∀ (i i' : Spec_flip1) (s : Spec), flush i s -> trans_refl rule i i' -> flush i' s := by
  intro i i' s h1 h2
  induction h2
  . rename_i a b c d h2 h3 h4 h5
    apply h5
    unfold rule at *
    cases h2 ; cases h3 <;> unfold flush at * <;> simp_all
  . assumption



theorem relation_method : ∀ (i i' : Spec_flip1) (s : Spec) e, flush i s -> seq_step_flip1 i e i' -> ∃ s', seq_step s e s' := by
  intro i i' s e h1 h2
  unfold flush at h1
  rcases h1 with ⟨h1, h1', h1''⟩
  cases h2
  . constructor
    . simp_all
      constructor
  . constructor
    . simp_all
      constructor
  . constructor
    . simp_all
      constructor
      . assumption
  . constructor
    . simp_all
      constructor
      . assumption


theorem relation_flush_method : ∀ (i i' : Spec_flip1) (s s' : Spec) e, flush i s -> seq_step_flip1 i e i' -> seq_step s e s' ->
                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'  := by
  intro i i' s s' e h1 h2 h3
  constructor; rotate_left; exact i'
  constructor
  . apply trans_refl.refl
  . unfold flush at *
    rcases h1 with ⟨h1, h1', h1''⟩
    cases h3 <;> simp_all
    . rw[← h1''] at h2
      cases h2
      simp_all
    . rw[← h1''] at h2
      cases h2
      simp_all
    . cases h2
      simp_all
    . cases h2
      simp_all

-- theorem double_application_term1:
--   rule a b -> trans_refl rule a b := by
--   intro h
--   constructor
--   exact h
--   apply trans_refl.refl


theorem has_diamond_property2 : ∀ {a b c b' : Spec_flip1}, trans_refl rule a c → rule a b → rule b b' → ∃ d d', rule c d' ∧  rule d' d  ∧ trans_refl rule b' d := by
  intro a b c b' h1 h11 h2
  induction h1 generalizing b b' h2
  . clear a c
    rename_i a' c' d e f h4 h5 h6
    induction h5 generalizing a' b b' h2 h11
    . clear c
      rename_i a'' b'' c' h7 h8 h9
      cases h2
      rename_i p h7
      unfold rule at *
      have H := trans_refl seq_internal_step_flip1 --b' p
      cases h3
      rename_i p' h9
      simp_all
      . simp_all
        rename_i p' h9
        cases (decEq p' p)
        . simp_all
        . simp_all
          apply h5
          apply seq_internal_step_flip1.null <;> simp_all
    . rename_i a
      constructor; rotate_left
      . exact b'
      . constructor; constructor
        . admit
        . constructor
          . assumption
          . apply trans_refl.refl



theorem enogh_internal (i : Spec_flip1) (s : Spec) :
    φ flush rule i s -> ∀ i', trans_refl rule i i' -> φ flush rule i' s := by
      intro h1 i' h2
      apply enoght_internal
      . assumption
      . assumption
      . admit
      . unfold has_diamond_property
        clear i i' h2 h1
        intro a b c h1 h3
        induction h3 generalizing c
        . clear a b
          rename_i a b' b d  h2 h3 h5 h4
          have H := @has_diamond_property2 _ _ _ _  h1 h2 h3
          cases H
          rename_i c_star H
          cases H
          rename_i d' H
          rcases H with ⟨ H, H1, H'⟩
          specialize h4 H'
          cases h4; rename_i D h4
          rcases h4 with ⟨ h4, h4'⟩
          constructor; rotate_left
          . exact D
          . constructor
            . constructor
              . exact H
              . assumption
              . assumption
            . assumption
        . clear a; rename_i a
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption



theorem enough_external (i : Spec_flip1) (s : Spec) :
    φ flush rule i s ->
    ∀ i' e, seq_step_flip1 i e i' ->
    ∃ (s' : Spec), seq_step s e s' ∧ φ flush rule i' s' := by
      intro hφ i' e hstep
      apply enoght_external <;> try assumption
      . unfold commutes_weakly_method_rule
        intro a b c e' h1 h2
        cases h1
        . rename_i a' h3 h4
          induction h4 generalizing c a
          . clear a'
            rename_i a' b' c_star h6 h7 h8
            cases h2
            . rename_i p
              unfold rule at *
              have H := seq_step_flip1.ld_rq b' p
              cases h3
              . rename_i cache h9
                cases h6
                . rename_i cache' h11
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache'<;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip1.null
              . simp_all
                cases h6
                . rename_i cache' h11
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip1.null
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      .  apply seq_internal_step_flip1.null
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip1.null
            . rename_i p v
              unfold rule at *
              have H := seq_step_flip1.st_rq b' p v
              cases h3
              . rename_i cache h9
                cases h6
                . rename_i cache' h11
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                        . apply seq_internal_step_flip1.read _ cache <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip1.null
              . simp_all
                cases h6
                . rename_i cache' h11
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip1.null
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip1.read _ cache'<;> simp_all
                        . apply seq_internal_step_flip1.read _ cache' <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      .  apply seq_internal_step_flip1.null
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip1.null
            . unfold rule at *
              rename_i t p list v' h11 h12
              have H := seq_step_flip1.ld_rq_response b' t p list v' --h11 h12
              cases h3
              . rename_i cache h9
                simp_all
                cases h6
                . rename_i cache' h11
                  simp_all
                  have Hc : cache' = p := by admit
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip1.read _  cache <;> simp_all
                      . constructor
                        rotate_left
                        . exact h8'
                        . simp_all
                          apply seq_internal_step_flip1.read _ p <;> simp_all
                . simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip1.read _  cache <;> simp_all
                      . constructor
                        rotate_left
                        . exact h8'
                        . simp_all
                          apply seq_internal_step_flip1.read _ p <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip.null
              . rename_i ident  v cache l h9 h10
                cases h6
                . rename_i ident' cache' l' h11 h12
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
                . rename_i ident' v' cache' l' h11 h12
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.write _ ident' v' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip.null
              . simp_all
                cases h6
                . rename_i ident' cache' l' h11 h12
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip.null
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.ld_rq a'.ident p]) <;> simp_all
                . rename_i ident' v' cache' l' h11 h12
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      .  apply seq_internal_step_flip.null
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.write _ ident' v' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.ld_rq a'.ident p]) <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      .  apply seq_internal_step_flip.null
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip.null


theorem indistinguishability (i : Spec_flip) (s : Spec) :
    φ flush rule i s -> @indistinguishability  _ _ _ seq_step_flip seq_step i s := by
      intro hφ
      apply indistinguisability_preservation <;> try assumption
      . unfold commutes_weakly_method_rule
        intro a b c e' h1 h2
        cases h1
        . rename_i b' h3 h4
          unfold rule at *
          simp_all
        . constructor; rotate_left
          . exact c
          . constructor
            . assumption
            . apply trans_refl.refl
