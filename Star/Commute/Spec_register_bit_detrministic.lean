import Star.Commute.ARS

open Star
namespace Spec_register_bit_deterministic



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
  bit : Fin 2

opaque f : Imp → Fin 2


inductive imp_step : Imp -> Event -> Imp-> Prop where
  | ld_rq : ∀ s i,
      imp_step s (Event.ld_rq i)
      { s with
          slot := update_Fin i (Event.ld_rq i) s.slot }
  | st_rq : ∀ s i v,
     imp_step s (Event.st_rq v i)
      { s with
          slot := update_Fin i (Event.ld_rq i) s.slot
      }
  | ld_rs : ∀ s i rst v,
      s.extqueue_rs i = Event.ld_rs v i :: rst →
      imp_step s (Event.ld_rs v i)
        { s with
            extqueue_rs := update_Fin i (rst) s.extqueue_rs}



inductive imp_step_internal : Imp -> Imp-> Prop where
  | read : ∀ s i ,
      s.slot i = some (Event.ld_rq i) →
      s.bit = i ->
      imp_step_internal s
        { s with
            extqueue_rs := update_Fin i ((s.extqueue_rs i) ++ [Event.ld_rs s.memory i]) s.extqueue_rs,
            bit := f s}
  | write :  ∀ s v i,
      s.slot i = some (Event.st_rq v i) →
      s.bit = i ->
      imp_step_internal s
        { s with
            memory := v,
            bit := f s}



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
        rename_i c
        apply imp_step_internal.read _ c <;> simp_all
  . constructor; constructor
    . apply trans_refl.step
      . unfold rule at *
        cases h2
        rename_i c v
        apply imp_step_internal.write _ v c <;> simp_all
  . constructor; rotate_left; exact i'
    constructor
    . apply trans_refl.refl
    . cases h2
      unfold flush at *
      simp_all
