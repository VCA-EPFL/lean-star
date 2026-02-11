import Star.Commute.ARS

open Star
namespace Spec



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





/-!
# Spec non determinist with internal rule
-/

structure Spec_int where
  memory : Nat
  extqueue_rq : Fin 2 -> List Event
  extqueue_rs : Fin 2 -> List Event
  ident : Nat


inductive seq_step_int : Spec_int -> Event -> Spec_int-> Prop where
  | ld_rq : ∀ s i,
      seq_step_int s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_int s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | ld_rs : ∀ s v t rst i,
      s.extqueue_rs i = Event.ld_rs t v i :: rst →
      seq_step_int s (Event.ld_rs t v i)
      { s with
          extqueue_rs := update_Fin i (rst) s.extqueue_rs }


inductive seq_internal_step_int : Spec_int -> Spec_int -> Prop where
  | read : ∀ s t i rst,
      s.extqueue_rq i = Event.ld_rq t i:: rst →
      seq_internal_step_int s --Event.null
        { s with
            extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.ident s.memory i]) s.extqueue_rs,
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | write :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      seq_internal_step_int s --Event.null
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq,
          memory := v }

/-!
# Spec determinist
-/

structure Spec_det where
  memory : Nat
  extqueue_rq : Fin 2 -> List Event
  --extqueue_rs : Fin 2 -> List Event
  ident : Nat

inductive seq_step_det : Spec_det -> Event -> Spec_det-> Prop where
  | ld_rq : ∀ s i,
      seq_step_det s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_det s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | read : ∀ s t t' t'' i rst v,
      s.extqueue_rq i = Event.ld_rq t i :: rst →
      (∀ j, j ≠ i → s.extqueue_rq j = Event.ld_rq t' i :: _ → t < t') →
      (∀ j, j ≠ i → s.extqueue_rq j = Event.st_rq t'' i _ :: _ → t < t'') →
      seq_step_det s (Event.ld_rs t v i)
        { s with
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | write :  ∀ s t t' t'' v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      (∀ j, j ≠ i → s.extqueue_rq j = Event.ld_rq t' i :: _ → t < t') →
      (∀ j, j ≠ i → s.extqueue_rq j = Event.st_rq t'' i _ :: _ → t < t'') →
      seq_step_det s (Event.st_rs t i)
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq,
          memory := v }



-- inductive seq_step_det : Spec_det -> Event -> Spec_det-> Prop where
--   | ld_rq : ∀ s i,
--       seq_step_det s (Event.ld_rq s.ident)
--       { s with
--           ident := Nat.succ s.ident,
--           extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident]) s.extqueue_rq
--       }
--   | st_rq : ∀ s i v,
--       seq_step_det s (Event.st_rq s.ident v)
--       { s with
--           ident := Nat.succ s.ident,
--           extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v]) s.extqueue_rq
--       }
--   | ld_rs : ∀ s v t rst i,
--       s.extqueue_rs i = Event.ld_rs t v :: rst →
--       seq_step_det s (Event.ld_rs t v)
--       { s with
--           extqueue_rs := update_Fin i (rst) s.extqueue_rs }


-- inductive seq_internal_step_det : Spec -> Event -> Spec -> Prop where
--   | read : ∀ s t t' t'' i rst ,
--       s.extqueue_rq i = Event.ld_rq t :: rst →
--       (∀ j, j ≠ i → s.extqueue_rq j = Event.ld_rq t' :: _ → t < t') →
--       (∀ j, j ≠ i → s.extqueue_rq j = Event.st_rq t'' _ :: _ → t < t'') →
--       seq_internal_step_det s Event.null
--         { s with
--             extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.ident s.memory]) s.extqueue_rs,
--             extqueue_rq := update_Fin i (rst) s.extqueue_rq}
--   | write :  ∀ s t t' t'' v i rst,
--       s.extqueue_rq i = Event.st_rq t v :: rst →
--       (∀ j, j ≠ i → s.extqueue_rq j = Event.ld_rq t' :: _ → t < t') →
--       (∀ j, j ≠ i → s.extqueue_rq j = Event.st_rq t'' _ :: _ → t < t'') →
--       seq_internal_step_det s Event.null
--       { s with
--           extqueue_rq := update_Fin i (rst) s.extqueue_rq,
--           memory := v }


/-!
# Spec false
-/

--return always the value 42 for read and ignore the order of the request

structure Spec_false where
  memory : Nat
  extqueue_rq : Fin 2 -> List Event
  ident : Nat


inductive seq_step_false : Spec_false -> Event -> Spec_false-> Prop where
  | ld_rq : ∀ s i,
      seq_step_false s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_false s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | read : ∀ s v t rst i,
      s.extqueue_rq i = Event.ld_rs t v i :: rst →
      seq_step_false s (Event.ld_rs t 42 i)
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq }


/-!
# Spec non determinist refines itself, there are not internal events
-/


def flush (i : Spec) (s : Spec) : Prop :=
  i.memory = s.memory ∧
  i.extqueue_rq  = s.extqueue_rq ∧
  i.ident = s.ident


def rule : Spec → Spec → Prop := fun _ _ => False


theorem relation_method : ∀ (i i' : Spec) (s : Spec) e, flush i s -> seq_step i e i' -> ∃ s', seq_step s e s' := by
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


theorem relation_flush_method : ∀ (i i' : Spec) (s s' : Spec) e, flush i s -> seq_step i e i' -> seq_step s e s' ->
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


theorem enough_external (i : Spec) (s : Spec) :
    φ flush rule i s ->
    ∀ i' e, seq_step i e i' ->
    ∃ (s' : Spec), seq_step s e s' ∧ φ flush rule i' s' := by
      intro hφ i' e hstep
      apply enoght_external <;> try assumption
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

theorem indistinguishability (i : Spec) (s : Spec) :
    φ flush rule i s -> @indistinguishability  _ _ _ seq_step seq_step i s := by
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
