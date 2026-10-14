import StarExperimental.MSI_def
import Star.Commute.ARS

/-!
# Lo spec sequenziale, per `MSI_trial`

Copia **letterale** di `SeqState`, `seq_step` e `seq_init` di `MSI_flush_proof.lean` (righe 22–51),
nel namespace `MSITrial`. Serve una copia perché `MSI_flush_proof.lean` e `MSI.lean` definiscono
entrambi `isRequest` al livello radice e non si possono importare insieme, e la confluenza di
`MSI_trial` dipende dai diamanti di `MSI.lean`. Le definizioni sono identiche carattere per carattere.
-/

open THEORY Relation

namespace MSITrial

/-- Stato dello spec sequenziale: una memoria e, per ogni cache, la coda esterna. -/
structure SeqState (n : Nat) where
  memory : Value
  extqueue : Fin n -> RsRqEvent

instance {n : Nat} : Inhabited (SeqState n) where
  default := SeqState.mk default (fun _ => default)

/-- Lo spec sequenziale: gli eventi portano l'indice della cache (`MSIExternalEvent n`), come
`msi_step_external`. Le richieste vengono servite in ordine FIFO; `ld_rs v` richiede `v` uguale alla
memoria, `st_rs` scrive il valore in testa. -/
inductive seq_step {n : Nat} : SeqState n -> MSIExternalEvent n -> SeqState n -> Prop where
  | ld_rq : ∀ (s1 : SeqState n) i,
      seq_step s1 (.cache Event.ld_rq i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.ld_rq] } s1.extqueue }
  | st_rq : ∀ (s1 : SeqState n) v i,
      seq_step s1 (.cache (Event.st_rq v) i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rq := (s1.extqueue i).rq ++ [Event.st_rq v] } s1.extqueue }
  | ld_rs : ∀ (s1 : SeqState n) v i rst,
      (s1.extqueue i).rq = Event.ld_rq :: rst →
      s1.memory = v ->
      seq_step s1 (.cache (Event.ld_rs v) i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rs := (s1.extqueue i).rs ++ [Event.ld_rs v], rq := rst } s1.extqueue }
  | st_rs : ∀ (s1 : SeqState n) v i rst,
      (s1.extqueue i).rq = Event.st_rq v :: rst →
      seq_step s1 (.cache Event.st_rs i)
        { s1 with extqueue := update_Fin i { s1.extqueue i with rs := (s1.extqueue i).rs ++ [Event.st_rs],rq := rst } s1.extqueue, memory := v }

@[simp]
def seq_init (n : Nat) : SeqState n := Inhabited.default

end MSITrial
