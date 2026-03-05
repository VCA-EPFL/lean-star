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
# Spec non determinist only methods with response queue
-/

structure Spec_rs where
  memory : Nat
  extqueue_rq : Fin 2 -> List Event
  extqueue_rs : Fin 2 -> List Event
  ident : Nat


inductive seq_step_rs : Spec -> Event -> Spec-> Prop where
  | ld_rq : ∀ s i,
      seq_step_rs s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_rs s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | read : ∀ s t i rst v,
      s.extqueue_rq i = Event.ld_rq t i :: rst →
      seq_step_rs s (Event.ld_rs t v i)
        { s with
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | write :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      seq_step_rs s (Event.st_rs t i)
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
  | st_rs : ∀ s t rst i,
      s.extqueue_rs i = Event.st_rs t  i :: rst →
      seq_step_int s (Event.st_rs t i)
      { s with
          extqueue_rs := update_Fin i (rst) s.extqueue_rs }


inductive seq_internal_step_int : Spec_int -> Spec_int-> Prop where
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
# Spec non determinist bit flip with internal rule non resposnse queue
-/

structure Spec_flip where
  memory : Nat
  bit : Fin 2
  extqueue_rq : Fin 2 -> List Event
  extqueue_rs : Fin 2 -> List Event
  ident : Nat


inductive seq_step_flip : Spec_flip -> Event -> Spec_flip-> Prop where
  | ld_rq : ∀ s i,
      seq_step_flip s (Event.ld_rq s.ident i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++ [Event.ld_rq s.ident i]) s.extqueue_rq
      }
  | st_rq : ∀ s i v,
      seq_step_flip s (Event.st_rq s.ident v i)
      { s with
          ident := Nat.succ s.ident,
          extqueue_rq := update_Fin i ((s.extqueue_rq i) ++[Event.st_rq s.ident v i]) s.extqueue_rq
      }
  | ld_rq_response : ∀ s t i rst v,
      s.extqueue_rq i = Event.ld_rq t i :: rst →
      s.bit = i →
      seq_step_flip s (Event.ld_rs t v i)
        { s with
            extqueue_rq := update_Fin i (rst) s.extqueue_rq}
  | st_rq_response :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      s.bit = i →
      seq_step_flip s (Event.st_rs t i)
      { s with
          extqueue_rq := update_Fin i (rst) s.extqueue_rq,
          memory := v }



inductive seq_internal_step_flip : Spec_flip -> Spec_flip-> Prop where
  | read : ∀ s t i rst,
      s.extqueue_rq i = Event.ld_rq t i:: rst →
      ¬(s.bit = i) →
      seq_internal_step_flip s --Event.null
        { s with bit := i}
  | write :  ∀ s t v i rst,
      s.extqueue_rq i = Event.st_rq t v i :: rst →
      ¬(s.bit = i) →
      seq_internal_step_flip s --Event.null
        { s with bit := i}
  | null : ∀ s,
      seq_internal_step_flip s s


/-!
# Spec non determinist bit flip (without external percondiction) with internal rule non resposnse queue
-/

structure Spec_flip1 where
  memory : Nat
  bit : Fin 2
  extqueue_rq : Fin 2 -> List Event
  extqueue_rs : Fin 2 -> List Event
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

/-!
# Spec flip refines spec non determinist with only methods
-/

namespace Spec_flip

def flush (i : Spec_flip) (s : Spec) : Prop :=
  i.memory = s.memory ∧
  i.extqueue_rq  = s.extqueue_rq ∧
  i.ident = s.ident


def rule : Spec_flip → Spec_flip → Prop := seq_internal_step_flip

theorem relation_flush : ∀ (i i' : Spec_flip) (s : Spec), flush i s -> trans_refl rule i i' -> flush i' s := by
  intro i i' s h1 h2
  induction h2
  . rename_i a b c h2 h3 h4
    apply h4
    unfold rule at *
    cases h2 <;> unfold flush at * <;> simp_all
  . assumption



theorem relation_method : ∀ (i i' : Spec_flip) (s : Spec) e, flush i s -> seq_step_flip i e i' -> ∃ s', seq_step s e s' := by
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


theorem relation_flush_method : ∀ (i i' : Spec_flip) (s s' : Spec) e, flush i s -> seq_step_flip i e i' -> seq_step s e s' ->
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

theorem double_application_term1:
  rule a b -> trans_refl rule a b := by
  intro h
  constructor
  exact h
  apply trans_refl.refl


theorem has_diamond_property2 : ∀ {a b c : Spec_flip}, trans_refl rule a c → rule a b → ∃ d, rule c d ∧ trans_refl rule b d := by
  intro a b c h1 h2
  induction h1 generalizing b
  . clear a c
    rename_i a b' c h3 h4 h5
    cases h2
    . rename_i t p l h6 h7
      unfold rule at *
      have H := seq_internal_step_flip.read b' t p l
      cases h3
      . simp_all
        rename_i t' p' l' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
          apply h5
          apply seq_internal_step_flip.null <;> simp_all
      . simp_all
        rename_i t' p' l' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
      . simp_all
    . rename_i t v p l h6 h7
      unfold rule at *
      have H := seq_internal_step_flip.write b' t v p l
      cases h3
      . simp_all
        rename_i t' p' l' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
      . simp_all
        rename_i t' p' l' h9 h10
        cases (decEq p' p)
        . simp_all
        . simp_all
          apply h5
          apply seq_internal_step_flip.null <;> simp_all
      . simp_all
    . unfold rule at *
      have H := seq_internal_step_flip.null b'
      have H3 := h3
      cases h3
      . rename_i t' p' l' h9 h10
        specialize @h5 _ H
        cases h5 ; rename_i d h5
        rcases h5 with ⟨ h5, h5'⟩
        constructor; rotate_left
        . exact d
        . constructor
          . assumption
          . constructor
            . exact H3
            . assumption
      . rename_i t' p' l' h9 h10
        specialize @h5 _ H
        cases h5 ; rename_i d h5
        rcases h5 with ⟨ h5, h5'⟩
        constructor; rotate_left
        . exact d
        . constructor
          . assumption
          . constructor
            . exact H3
            . assumption
      . simp_all
  . clear a c
    rename_i a
    constructor; rotate_left
    . exact b
    . constructor
      . assumption
      . apply trans_refl.refl




theorem add_step (a b c : Spec_flip) : trans_refl rule a b -> rule b c ->trans_refl rule a c := by
  intro h1 h2
  induction h1
  . clear a b
    rename_i a b c' h3 h4 h5
    specialize h5 h2
    constructor <;> assumption
  . clear a; rename_i a
    apply double_application_term1 <;> assumption

theorem add_step1 (a b c : Spec_flip) : trans_refl rule a b ->  trans_refl rule b c ->trans_refl rule a c := by
  intro h1 h2
  induction h1
  . clear a b
    rename_i a b c' h3 h4 h5
    specialize h5 h2
    constructor <;> assumption
  . clear a; rename_i a
    assumption


theorem enogh_internal (i : Spec_flip) (s : Spec) :
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
          have H := @has_diamond_property2 a b' c h1 h2
          cases H
          rename_i c_star H
          rcases H with ⟨ H, H'⟩
          specialize h4 H'
          cases h4; rename_i d h4
          rcases h4 with ⟨ h4, h4'⟩
          constructor; rotate_left
          . exact d
          . constructor
            . constructor
              . exact H
              . assumption
            . assumption
        . clear a; rename_i a
          constructor; rotate_left
          . exact c
          . constructor
            . apply trans_refl.refl
            . assumption


-- theorem enough_external (i : Spec_flip) (s : Spec) :
--     φ flush rule i s ->
--     ∀ i' e, seq_step_flip i e i' ->
--     ∃ (s' : Spec), seq_step s e s' ∧ φ flush rule i' s' := by
--       intro hφ i' e hstep
--       apply enoght_external <;> try assumption
--       . unfold commutes_weakly_method_rule
--         intro a b c e' h1 h2
--         induction h1 generalizing c
--         . clear a b
--           rename_i a b c' h3 h4 h5
--           cases h2
--           . rename_i p
--             unfold rule at *
--             have H := seq_step_flip.ld_rq b p
--             cases h3
--             . rename_i ident cache l h6 h7
--               simp_all
--               specialize @h5 _ H
--               cases h5; rename_i d h5
--               rcases h5 with ⟨ h5, h5'⟩
--               constructor; rotate_left
--               . exact d
--               . constructor
--                 . assumption
--                 . constructor
--                   rotate_left
--                   . exact h5'
--                   . cases (decEq p cache)
--                     . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
--                     . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--             . rename_i ident value cache l h6 h7
--               simp_all
--               specialize @h5 _ H
--               cases h5; rename_i d h5
--               rcases h5 with ⟨ h5, h5'⟩
--               constructor; rotate_left
--               . exact d
--               . constructor
--                 . assumption
--                 . constructor
--                   rotate_left
--                   . exact h5'
--                   . cases (decEq p cache)
--                     . apply seq_internal_step_flip.write _ ident value cache l <;> simp_all
--                     . apply seq_internal_step_flip.write _ ident value cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--             . simp_all
--           . rename_i p v
--             unfold rule at *
--             have H := seq_step_flip.st_rq b p v
--             cases h3
--             . rename_i ident cache l h6 h7
--               simp_all
--               specialize @h5 _ H
--               cases h5; rename_i d h5
--               rcases h5 with ⟨ h5, h5'⟩
--               constructor; rotate_left
--               . exact d
--               . constructor
--                 . assumption
--                 . constructor
--                   rotate_left
--                   . exact h5'
--                   . cases (decEq p cache)
--                     . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
--                     . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
--             . rename_i ident value cache l h6 h7
--               simp_all
--               specialize @h5 _ H
--               cases h5; rename_i d h5
--               rcases h5 with ⟨ h5, h5'⟩
--               constructor; rotate_left
--               . exact d
--               . constructor
--                 . assumption
--                 . constructor
--                   rotate_left
--                   . exact h5'
--                   . cases (decEq p cache)
--                     . apply seq_internal_step_flip.write _ ident value cache l <;> simp_all
--                     . apply seq_internal_step_flip.write _ ident value cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
--             . simp_all
--           . rename_i id p list v h8 h9
--             unfold rule at *
--             have H := seq_step_flip.ld_rq_response b id p list v
--             cases h3
--             . rename_i ident cache l h6 h7
--               simp_all
--               cases (decEq p cache)
--               . induction h4
--               . simp_all
--               -- . simp_all
--               -- dsimp at *
--               -- simp_all
--               -- specialize @h5 _ H
--               -- cases h5; rename_i d h5
--               -- rcases h5 with ⟨ h5, h5'⟩
--               -- constructor; rotate_left
--               -- . exact d
--               -- . constructor
--               --   . assumption
--               --   . constructor
--               --     rotate_left
--               --     . exact h5'
--               --     . cases (decEq p cache)
--               --       . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
--               --       . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all


theorem enough_external (i : Spec_flip) (s : Spec) :
    φ flush rule i s ->
    ∀ i' e, seq_step_flip i e i' ->
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
              have H := seq_step_flip.ld_rq b' p
              cases h3
              . rename_i ident cache l h9 h10
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
                        . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
                . rename_i ident' v cache' l' h11 h12
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
                        . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.write _ ident' v cache' l' <;> simp_all
                        . apply seq_internal_step_flip.write _ ident' v cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
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
            . rename_i p v
              unfold rule at *
              have H := seq_step_flip.st_rq b' p v
              cases h3
              . rename_i ident cache l h9 h10
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
                        . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.st_rq a.ident v p]) <;> simp_all
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
                        . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.write _ ident' v' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.st_rq a.ident v p]) <;> simp_all
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
                        . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . apply seq_internal_step_flip.null
              . rename_i ident  v' cache l h9 h10
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
                        . apply seq_internal_step_flip.write _ ident v' cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v' cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.st_rq a.ident v p]) <;> simp_all
                . rename_i ident' v'' cache' l' h11 h12
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
                        . apply seq_internal_step_flip.write _ ident v' cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v' cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
                      constructor
                      rotate_left
                      . exact h8'
                      . cases (decEq p cache')
                        . apply seq_internal_step_flip.write _ ident' v'' cache' l' <;> simp_all
                        . apply seq_internal_step_flip.write _ ident' v'' cache' (l' ++ [Event.st_rq a.ident v p]) <;> simp_all
                . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . cases (decEq p cache)
                        . apply seq_internal_step_flip.write _ ident v' cache l <;> simp_all
                        . apply seq_internal_step_flip.write _ ident v' cache (l ++ [Event.st_rq a.ident v p]) <;> simp_all
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
                        . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.st_rq a'.ident v p]) <;> simp_all
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
                        . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.st_rq a'.ident v p]) <;> simp_all
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
            . unfold rule at *
              rename_i t p list v' h11' h12'
              have H := seq_step_flip.ld_rq_response b'
              cases h3
              . rename_i ident cache l h9 h10
                cases h6
                . rename_i ident' cache' l' h11 h12
                  simp_all
                  have Hc : cache' = p := by admit
                  specialize H ident' p l' v'
                  simp_all
                  specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
                  cases h8; rename_i d h8
                  rcases h8 with ⟨ h8, h8'⟩
                  constructor; rotate_left
                  . exact d
                  . constructor
                    . assumption
                    . constructor
                      . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
                      . constructor
                        rotate_left
                        . exact h8'
                        . apply seq_internal_step_flip.read _ ident' p l' <;> dsimp
                          . admit
                          . simp_all


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

end Spec_flip


/-!
# Spec flip1 refines spec non determinist with only methods
-/


-- with null
-- namespace Spec_flip1

-- def flush (i : Spec_flip1) (s : Spec) : Prop :=
--   i.memory = s.memory ∧
--   i.extqueue_rq  = s.extqueue_rq ∧
--   i.ident = s.ident


-- def rule : Spec_flip1 → Spec_flip1 → Prop := seq_internal_step_flip1

-- theorem relation_flush : ∀ (i i' : Spec_flip1) (s : Spec), flush i s -> trans_refl rule i i' -> flush i' s := by
--   intro i i' s h1 h2
--   induction h2
--   . rename_i a b c h2 h3 h4
--     apply h4
--     unfold rule at *
--     cases h2 <;> unfold flush at * <;> simp_all
--   . assumption



-- theorem relation_method : ∀ (i i' : Spec_flip1) (s : Spec) e, flush i s -> seq_step_flip1 i e i' -> ∃ s', seq_step s e s' := by
--   intro i i' s e h1 h2
--   unfold flush at h1
--   rcases h1 with ⟨h1, h1', h1''⟩
--   cases h2
--   . constructor
--     . simp_all
--       constructor
--   . constructor
--     . simp_all
--       constructor
--   . constructor
--     . simp_all
--       constructor
--       . assumption
--   . constructor
--     . simp_all
--       constructor
--       . assumption


-- theorem relation_flush_method : ∀ (i i' : Spec_flip1) (s s' : Spec) e, flush i s -> seq_step_flip1 i e i' -> seq_step s e s' ->
--                                 ∃ i'', trans_refl rule i' i'' ∧ flush i'' s'  := by
--   intro i i' s s' e h1 h2 h3
--   constructor; rotate_left; exact i'
--   constructor
--   . apply trans_refl.refl
--   . unfold flush at *
--     rcases h1 with ⟨h1, h1', h1''⟩
--     cases h3 <;> simp_all
--     . rw[← h1''] at h2
--       cases h2
--       simp_all
--     . rw[← h1''] at h2
--       cases h2
--       simp_all
--     . cases h2
--       simp_all
--     . cases h2
--       simp_all

-- theorem double_application_term1:
--   rule a b -> trans_refl rule a b := by
--   intro h
--   constructor
--   exact h
--   apply trans_refl.refl


-- theorem has_diamond_property2 : ∀ {a b c : Spec_flip1}, trans_refl rule a c → rule a b → ∃ d, rule c d ∧ trans_refl rule b d := by
--   intro a b c h1 h2
--   induction h1 generalizing b
--   . clear a c
--     rename_i a b' c h3 h4 h5
--     cases h2
--     . rename_i p h6
--       unfold rule at *
--       have H := seq_internal_step_flip1.read b' p
--       cases h3
--       . simp_all
--         rename_i p' h9
--         cases (decEq p' p)
--         . simp_all
--         . simp_all
--           apply h5
--           apply seq_internal_step_flip1.null <;> simp_all
--       . simp_all
--     . unfold rule at *
--       have H := seq_internal_step_flip1.null b'
--       have H3 := h3
--       cases h3
--       . rename_i p' h9
--         specialize @h5 _ H
--         cases h5 ; rename_i d h5
--         rcases h5 with ⟨ h5, h5'⟩
--         constructor; rotate_left
--         . exact d
--         . constructor
--           . assumption
--           . constructor
--             . exact H3
--             . assumption
--       . simp_all
--   . clear a c
--     rename_i a
--     constructor; rotate_left
--     . exact b
--     . constructor
--       . assumption
--       . apply trans_refl.refl



-- theorem enogh_internal (i : Spec_flip1) (s : Spec) :
--     φ flush rule i s -> ∀ i', trans_refl rule i i' -> φ flush rule i' s := by
--       intro h1 i' h2
--       apply enoght_internal
--       . assumption
--       . assumption
--       . admit
--       . unfold has_diamond_property
--         clear i i' h2 h1
--         intro a b c h1 h3
--         induction h3 generalizing c
--         . clear a b
--           rename_i a b' b h2 h3 h4
--           have H := @has_diamond_property2 a b' c h1 h2
--           cases H
--           rename_i c_star H
--           rcases H with ⟨ H, H'⟩
--           specialize h4 H'
--           cases h4; rename_i d h4
--           rcases h4 with ⟨ h4, h4'⟩
--           constructor; rotate_left
--           . exact d
--           . constructor
--             . constructor
--               . exact H
--               . assumption
--             . assumption
--         . clear a; rename_i a
--           constructor; rotate_left
--           . exact c
--           . constructor
--             . apply trans_refl.refl
--             . assumption



-- theorem enough_external (i : Spec_flip1) (s : Spec) :
--     φ flush rule i s ->
--     ∀ i' e, seq_step_flip1 i e i' ->
--     ∃ (s' : Spec), seq_step s e s' ∧ φ flush rule i' s' := by
--       intro hφ i' e hstep
--       apply enoght_external <;> try assumption
--       . unfold commutes_weakly_method_rule
--         intro a b c e' h1 h2
--         cases h1
--         . rename_i a' h3 h4
--           induction h4 generalizing c a
--           . clear a'
--             rename_i a' b' c_star h6 h7 h8
--             cases h2
--             . rename_i p
--               unfold rule at *
--               have H := seq_step_flip1.ld_rq b' p
--               cases h3
--               . rename_i cache h9
--                 cases h6
--                 . rename_i cache' h11
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache'<;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip1.null
--               . simp_all
--                 cases h6
--                 . rename_i cache' h11
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . apply seq_internal_step_flip1.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       .  apply seq_internal_step_flip1.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip1.null
--             . rename_i p v
--               unfold rule at *
--               have H := seq_step_flip1.st_rq b' p v
--               cases h3
--               . rename_i cache h9
--                 cases h6
--                 . rename_i cache' h11
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip1.null
--               . simp_all
--                 cases h6
--                 . rename_i cache' h11
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . apply seq_internal_step_flip1.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip1.read _ cache'<;> simp_all
--                         . apply seq_internal_step_flip1.read _ cache' <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       .  apply seq_internal_step_flip1.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip1.null
--             . unfold rule at *
--               rename_i t p list v' h11 h12
--               have H := seq_step_flip1.ld_rq_response b' t p list v' --h11 h12
--               cases h3
--               . rename_i cache h9
--                 simp_all
--                 cases h6
--                 . rename_i cache' h11
--                   simp_all
--                   have Hc : cache' = p := by admit
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . apply seq_internal_step_flip1.read _  cache <;> simp_all
--                       . constructor
--                         rotate_left
--                         . exact h8'
--                         . simp_all
--                           apply seq_internal_step_flip1.read _ p <;> simp_all
--                 . simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip1.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . apply seq_internal_step_flip1.read _  cache <;> simp_all
--                       . constructor
--                         rotate_left
--                         . exact h8'
--                         . simp_all
--                           apply seq_internal_step_flip1.read _ p <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip.read _ ident cache l <;> simp_all
--                         . apply seq_internal_step_flip.read _ ident cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip.null
--               . rename_i ident  v cache l h9 h10
--                 cases h6
--                 . rename_i ident' cache' l' h11 h12
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
--                         . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
--                         . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
--                 . rename_i ident' v' cache' l' h11 h12
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
--                         . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip.write _ ident' v' cache' l' <;> simp_all
--                         . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.ld_rq a.ident p]) <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . cases (decEq p cache)
--                         . apply seq_internal_step_flip.write _ ident v cache l <;> simp_all
--                         . apply seq_internal_step_flip.write _ ident v cache (l ++ [Event.ld_rq a.ident p]) <;> simp_all
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip.null
--               . simp_all
--                 cases h6
--                 . rename_i ident' cache' l' h11 h12
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       . apply seq_internal_step_flip.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip.read _ ident' cache' l' <;> simp_all
--                         . apply seq_internal_step_flip.read _ ident' cache' (l' ++ [Event.ld_rq a'.ident p]) <;> simp_all
--                 . rename_i ident' v' cache' l' h11 h12
--                   simp_all
--                   specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       .  apply seq_internal_step_flip.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . cases (decEq p cache')
--                         . apply seq_internal_step_flip.write _ ident' v' cache' l' <;> simp_all
--                         . apply seq_internal_step_flip.write _ ident' v' cache' (l' ++ [Event.ld_rq a'.ident p]) <;> simp_all
--                 . specialize @h8 _ _ H (by apply seq_internal_step_flip.null )
--                   cases h8; rename_i d h8
--                   rcases h8 with ⟨ h8, h8'⟩
--                   constructor; rotate_left
--                   . exact d
--                   . constructor
--                     . assumption
--                     . constructor
--                       .  apply seq_internal_step_flip.null
--                       constructor
--                       rotate_left
--                       . exact h8'
--                       . apply seq_internal_step_flip.null


-- theorem indistinguishability (i : Spec_flip) (s : Spec) :
--     φ flush rule i s -> @indistinguishability  _ _ _ seq_step_flip seq_step i s := by
--       intro hφ
--       apply indistinguisability_preservation <;> try assumption
--       . unfold commutes_weakly_method_rule
--         intro a b c e' h1 h2
--         cases h1
--         . rename_i b' h3 h4
--           unfold rule at *
--           simp_all
--         . constructor; rotate_left
--           . exact c
--           . constructor
--             . assumption
--             . apply trans_refl.refl


namespace Spec_flip1


def flush (i : Spec_flip1) (s : Spec) : Prop :=
  i.memory = s.memory ∧
  i.extqueue_rq  = s.extqueue_rq ∧
  i.ident = s.ident


def rule : Spec_flip1 → Spec_flip1 → Prop := seq_internal_step_flip1

theorem relation_flush : ∀ (i i' : Spec_flip1) (s : Spec), flush i s -> trans_refl rule i i' -> flush i' s := by
  intro i i' s h1 h2
  induction h2
  . rename_i a b c h2 h3 h4
    apply h4
    unfold rule at *
    cases h2 <;> unfold flush at * <;> simp_all
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

theorem double_application_term1:
  rule a b -> trans_refl rule a b := by
  intro h
  constructor
  exact h
  apply trans_refl.refl


theorem has_diamond_property2 : ∀ {a b c : Spec_flip1}, trans_refl rule a c → rule a b → ∃ d, rule c d ∧ trans_refl rule b d := by
  intro a b c h1 h2
  induction h1 generalizing b
  . clear a c
    rename_i a' b' c h4 h5 h6
    induction h5 generalizing a' b h2
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
    . clear a c
      rename_i a
      constructor; rotate_left
      . exact b
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
          rename_i a b' b h2 h3 h4
          have H := @has_diamond_property2 a b' c h1 h2
          cases H
          rename_i c_star H
          rcases H with ⟨ H, H'⟩
          specialize h4 H'
          cases h4; rename_i d h4
          rcases h4 with ⟨ h4, h4'⟩
          constructor; rotate_left
          . exact d
          . constructor
            . constructor
              . exact H
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
