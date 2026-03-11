import Star.Commute.ARS

open Star
namespace Spec_register_deterministic



inductive Event where
  | ld_rq (c : Fin 2)
  | ld_rs (val : Nat) (c : Fin 2)
  | st_rq (val : Nat) (c : Fin 2)
  | st_rs (c : Fin 2)
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
# Spec non determinist only methods with output response queue
-/

structure Spec where
  memory : Nat
  extqueue_rs : Fin 2 -> List Event


inductive seq_step : Spec -> Event -> Spec-> Prop where
  | ld_rq : ∀ s i,
      seq_step s (Event.ld_rq i)
      { s with
          extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.memory i]) s.extqueue_rs
      }
  | st_rq : ∀ s i v,
      seq_step s (Event.st_rq v i)
      { s with
          memory := v
      }
  | ld_rs : ∀ s i rst v,
      s.extqueue_rs i = Event.ld_rs v i :: rst →
      seq_step s (Event.ld_rs v i)
        { s with
            extqueue_rs := update_Fin i (rst) s.extqueue_rs}
/-!
# Implmentation determinist with internal rule and function f deterministic
-/



structure Imp where
  memory : Nat
  extqueue_rs : Fin 2 -> List Event
  slot : Fin 2 -> Option Event


opaque f : Imp → Fin 2


inductive imp_step : Imp -> Event -> Imp-> Prop where
  | ld_rq : ∀ s i,
      s.slot i = none →
      imp_step s (Event.ld_rq i)
      { s with
          slot := update_Fin i (Event.ld_rq i) s.slot }
  | st_rq : ∀ s i v,
      s.slot i = none →
      imp_step s (Event.st_rq v i)
      { s with
          slot := update_Fin i (Event.st_rq v i) s.slot
      }
  | ld_rs : ∀ s i rst v,
      s.extqueue_rs i = Event.ld_rs v i :: rst →
      imp_step s (Event.ld_rs v i)
        { s with
            extqueue_rs := update_Fin i (rst) s.extqueue_rs}



inductive imp_step_internal : Imp -> Imp-> Prop where
  | read : ∀ s i ,
      s.slot i = some (Event.ld_rq i) →
      ( ∀ j ≠ i, s.slot j = none) →
      imp_step_internal s
        { s with
            extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.memory i]) s.extqueue_rs,
            slot := update_Fin i none s.slot}
  | write :  ∀ s v i,
      s.slot i = some (Event.st_rq v i) →
      ( ∀ j ≠ i, s.slot j = none) →
      imp_step_internal s
        { s with
            memory := v,
            slot := update_Fin i none s.slot}
  | read1 : ∀ s i j,
      s.slot i = some (Event.ld_rq i) →
      j ≠ i →
      s.slot j ≠ none  →
      f s = i →
      imp_step_internal s
        { s with
            extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.memory i]) s.extqueue_rs,
            slot := update_Fin i none s.slot}
  | write1 :  ∀ s v i j,
      s.slot i = some (Event.st_rq v i) →
      j ≠ i →
      s.slot j ≠ none →
      f s = i →
      imp_step_internal s
        { s with
            memory := v,
            slot := update_Fin i none s.slot}



def flush (i : Imp) (s : Spec) : Prop :=
  i.memory = s.memory ∧
  i.extqueue_rs = s.extqueue_rs ∧
  ( ∀ c , i.slot c = none)


def rule : Imp → Imp → Prop := imp_step_internal



theorem relation_flush : ∀ (i i' : Imp) (s : Spec), flush i s -> trans_refl rule i i' -> flush i' s := by
  intro i i' s h1 h2
  induction h2
  . rename_i a b c h2 h3 h4
    apply h4
    unfold rule at *
    cases h2 <;> unfold flush at * <;> simp_all
  . assumption



theorem relation_method : ∀ (i i' : Imp) (s : Spec) e, flush i s -> imp_step i e i' -> ∃ s', seq_step s e s' := by
  intro i i' s e h1 h2
  unfold flush at h1
  rcases h1 with ⟨h1, h1'⟩
  cases h2
  . constructor; constructor
  . constructor; constructor
  . constructor
    . simp_all
      constructor
      . assumption


theorem relation_flush_method : ∀ (i i' : Imp) (s s' : Spec) e, flush i s -> imp_step i e i' -> seq_step s e s' ->
                                ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'  := by
  intro i i' s s' e h1 h2 h3
  cases h3
  . constructor; constructor
    . apply trans_refl.step
      . unfold rule at *
        cases h2
        rename_i  c _
        unfold flush at *
        apply imp_step_internal.read _ c <;> simp_all
      . apply trans_refl.refl
    . unfold flush at *
      simp_all
      rename_i c
      intro p
      cases (decEq p c)
      . simp_all
      . simp_all
  . constructor; constructor
    . apply trans_refl.step
      . unfold rule at *
        cases h2
        rename_i c v _
        unfold flush at *
        apply imp_step_internal.write _ v c <;> simp_all
      . apply trans_refl.refl
    . unfold flush at *
      simp_all
  . constructor; constructor
    . apply trans_refl.refl
    . unfold flush at *
      cases h2
      simp_all


theorem add_step1 (a b c : Imp) : trans_refl rule a b ->  trans_refl rule b c ->trans_refl rule a c := by
  intro h1 h2
  induction h1
  . clear a b
    rename_i a b c' h3 h4 h5
    specialize h5 h2
    constructor <;> assumption
  . clear a; rename_i a
    assumption


theorem has_diamond_property1 : ∀ {a b c : Imp}, trans_refl rule a c → rule a b → ∃ d, trans_refl rule c d ∧ trans_refl rule b d := by
  intro a b c h1 h2
  induction h1 generalizing b
  . clear a c
    rename_i a b' c h3 h4 h5
    cases h2
    . rename_i p h6 h7
      unfold rule at *
      have H := imp_step_internal.read b' p
      cases h3
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p) <;> simp_all
      . simp_all
        rename_i p' p'' h9 h10 h11 h12
        cases (decEq p' p) <;> simp_all
      . simp_all
        rename_i p' p'' h9 h10 h11 h12
        cases (decEq p' p) <;> simp_all
    . rename_i v p h6 h7
      unfold rule at *
      have H := imp_step_internal.write b' v p
      cases h3
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p) <;> simp_all
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption
      . simp_all
        rename_i p' p'' h9 h10 h11 h12
        cases (decEq p' p) <;> simp_all
      . simp_all
        rename_i p' p'' h9 h10 h11 h12
        cases (decEq p' p) <;> simp_all
    . rename_i p cc h6 h7 h13 h14
      unfold rule at *
      have H := imp_step_internal.read1 b' p
      cases h3
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . grind
        . simp_all
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . grind
        . simp_all
      . simp_all
        rename_i p' h9 h10 h15 h16
        cases (decEq p' p)
        . simp_all
        . simp_all
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption
      . simp_all
    . rename_i v p cc h6 h7 h13 h14
      unfold rule at *
      have H := imp_step_internal.write1 b' v p
      cases h3
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . grind
        . simp_all
      . simp_all
        rename_i p' h9 h10
        cases (decEq p' p)
        . grind
        . simp_all
      . simp_all
      . simp_all
        rename_i v' p' p'' h9 h10 h15 h16
        cases (decEq p' p)
        . simp_all
        . simp_all
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption
  . constructor; rotate_left
    . exact b
    . constructor
      . constructor
        . assumption
        . apply trans_refl.refl
      . apply trans_refl.refl



theorem enogh_internal (i : Imp) (s : Spec) :
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
          rename_i a b' b h2 h3 h4
          have H := @has_diamond_property1 a b' c h1 h2
          cases H
          rename_i c_star H
          rcases H with ⟨ H, H'⟩
          specialize h4 H'
          cases h4; rename_i d h4
          rcases h4 with ⟨ h4, h4'⟩
          constructor; rotate_left
          . exact d
          . constructor
            . have H1 := add_step1 _ _ _ H h4
              assumption
            . assumption
        . clear a; rename_i a
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption


theorem enough_external (i : Imp) (s : Spec) :
    φ flush rule i s ->
    ∀ i' e, imp_step i e i' ->
    ∃ (s' : Spec), seq_step s e s' ∧ φ flush rule i' s' := by
      intro hφ i' e hstep
      apply enoght_external <;> try assumption
      . unfold commutes_weakly_method_rule
        intro a b c e' h1 h2
        induction h1 generalizing c
        . rename_i a' b' c' h1 h3 h4
          cases h2
          . rename_i p h
            unfold rule at *
            have H := imp_step.ld_rq b' p
            cases h1
            . rename_i c h9 h10
              simp_all
              cases (decEq c p)
              . simp_all
                specialize @h4 _ H
                rcases h4 with ⟨ d, h4, h4'⟩
                constructor; rotate_left
                . exact d
                . constructor
                  . assumption
                  . constructor; rotate_left
                    . exact h4'
                    . apply imp_step_internal.read1
              . simp_all
