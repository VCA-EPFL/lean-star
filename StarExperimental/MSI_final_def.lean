import StarExperimental.MSI_def
import Star.Commute.ARS

/-! # `MSI_final_def`: MSI con passi interni terminanti

Stessi stati, stessi messaggi e stessi eventi di `MSI_def.lean`; cambiano le guardie delle regole
interne, in modo che tra due eventi esterni il protocollo possa fare solo un numero finito di passi.
Le quattro sorgenti di cammini interni infiniti del modello originale e il rimedio:

| sorgente                      | rimedio                                                             |
|-------------------------------|---------------------------------------------------------------------|
| richieste spontanee           | si chiede `M` solo per una store pendente, `S` solo per una load pendente, mai due volte |
| rilasci spontanei             | tolti; si cede solo su invalidate, o da `S` per una store (serve `M`) |
| invalidate ripetuti           | un solo invalidate in coda per cache, e mai a chi sta già rilasciando |
| ping-pong tra due richiedenti | chi tiene la linea con una richiesta del programma pendente non la cede |

Ogni regola nuova ha la guardia della regola originale più qualcosa, e lo stesso effetto: quindi
ogni passo interno di `MSI_final` è un passo interno di `MSI_def` (`step_int_sub`). I passi esterni
sono gli stessi (`msi_step_external`). Le etichette degli eventi sono quelle di `MSI_def`:
`release_S_for_store` usa l'etichetta del vecchio rilascio spontaneo da `S`. -/

open THEORY Relation
open ReachingStar (Rule)

namespace MSIFinal

variable {n : Nat}

/-- La cache ha già una richiesta in viaggio. -/
def pending (c : CacheState) : Prop := CPEvent.rqM ∈ c.queue_cp ∨ CPEvent.rqS ∈ c.queue_cp

/-- In testa alla coda del programma c'è una load. -/
def headLoad (c : CacheState) : Prop := ∃ rst, c.extqueue.rq = Event.ld_rq :: rst

/-! ## Regole interne della cache -/

inductive cache_step : CacheState → CacheInternalEvent → CacheState → Prop where
  /-- Rilascio da `S` **su domanda**: c'è una store in testa, e per scrivere serve `M`, che si
  ottiene solo da `I`. Sostituisce il rilascio spontaneo `rq_data_not_available1`. -/
  | release_S_for_store : ∀ s1 v rst,
      s1.state = Bstate.S →
      s1.extqueue.rq = Event.st_rq v :: rst →
      cache_step s1 .ld_rq_data_not_availableS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIσ], state := Bstate.I }
  /-- Richiesta di `M`: solo da `I`, solo per una store in testa, solo se non c'è già una richiesta
  in viaggio. -/
  | upgrade_from_I_rq : ∀ s1 v rst,
      s1.state = Bstate.I →
      s1.extqueue.rq = Event.st_rq v :: rst →
      ¬ pending s1 →
      cache_step s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM] }
  /-- Richiesta di `S`: solo da `I`, solo per una load in testa, solo se non c'è già una richiesta
  in viaggio. -/
  | upgrade_from_I_rq1 : ∀ s1 rst,
      s1.state = Bstate.I →
      s1.extqueue.rq = Event.ld_rq :: rst →
      ¬ pending s1 →
      cache_step s1 .upgrade_from_I_rqS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqS] }
  /-- Presa del grant di `M` (come in `MSI_def`). -/
  | upgrade_from_I_rs : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsM v) →
      s1.state = Bstate.I →
      cache_step s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M, value := v, queue_pc := s1.queue_pc.eraseIdx j }
  /-- Presa del grant di `S` (come in `MSI_def`). -/
  | upgrade_from_I_rsS : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsS v) →
      s1.state = Bstate.I →
      cache_step s1 (.upgrade_from_I_rsS v)
        { s1 with state := Bstate.S, value := v, queue_pc := s1.queue_pc.eraseIdx j }
  /-- Invalidate ricevuto in `M`: si cede **solo se non c'è niente in sospeso** dal programma.
  Altrimenti l'`rqIμ` resta in coda e verrà onorato dopo. -/
  | downgrade_from_M_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIμ →
      s1.state = Bstate.M →
      s1.extqueue.rq = [] →
      cache_step s1 .downgrade_from_M_rs
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value] }
  /-- Invalidate ricevuto in `S`: si cede **solo se non c'è una load in sospeso** (una store può
  aspettare: per lei bisogna comunque passare da `I`). -/
  | downgrade_from_M_rs1 : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIσ →
      s1.state = Bstate.S →
      ¬ headLoad s1 →
      cache_step s1 .downgrade_from_S_rsS
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIσ] }

/-! ## Regole del parent -/

/-- Nessun invalidate verso `i'` è già in coda, e `i'` non sta già rilasciando. -/
def quietTarget (p : ParentState n) (i' : Fin n) : Prop :=
  PCEvent.rqIμ ∉ p.queue_pci i' ∧ PCEvent.rqIσ ∉ p.queue_pci i'
  ∧ (∀ v, CPEvent.rsIμ v ∉ p.queue_cip i') ∧ CPEvent.rsIσ ∉ p.queue_cip i'

inductive parent_step : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  /-- Consuma un `rsIμ`: riga a `I`, dato aggiornato (come in `MSI_def`). -/
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) v i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      parent_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i)
        { p1 with value := v,
                  shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip }
  /-- Consuma un `rsIσ`: riga a `I` (come in `MSI_def`). -/
  | downgrade_from_M_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rsIσ →
      parent_step p1 (.upd_queue .downgrade_from_S_rq1S i)
        { p1 with shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip }
  /-- Concessione di `M`: tutte le righe a `I` (come in `MSI_def`). -/
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_step p1 (.upd_queue .upgrade_to_M_data_avilable_rq1 i)
        { p1 with shared_state := update_Fin i Bstate.M p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsM p1.value]) p1.queue_pci }
  /-- Concessione di `S`: riga del richiedente a `I`, nessuna riga a `M` (come in `MSI_def`). -/
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      p1.shared_state i = Bstate.I →
      (∀ i, ¬(p1.shared_state i = Bstate.M)) →
      parent_step p1 (.upd_queue .upgrade_to_S_data_avilable_rq1S i)
        { p1 with shared_state := update_Fin i Bstate.S p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsS p1.value]) p1.queue_pci }
  /-- `i` chiede `M`, `i'` tiene `M`: un `rqIμ` a `i'`, **uno solo** e non a chi sta rilasciando. -/
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      p1.shared_state i' = Bstate.M →
      quietTarget p1 i' →
      parent_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }
  /-- `i` chiede `M`, `i'` tiene `S`: un `rqIσ` a `i'`, uno solo. -/
  | upgrade_to_M_invalid_all1 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      p1.shared_state i' = Bstate.S →
      quietTarget p1 i' →
      parent_step p1 (.upd_queue .invalid_allS i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIσ]) p1.queue_pci }
  /-- `i` chiede `S`, `i'` tiene `M`: un `rqIμ` a `i'`, uno solo. La regola `upgrade_to_M_invalid_all2`
  di `MSI_def` (invalidare un lettore perché un altro vuole leggere) non c'è più. -/
  | upgrade_to_M_invalid_all3 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      p1.shared_state i' = Bstate.M →
      quietTarget p1 i' →
      parent_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }

/-! ## Passi di sistema -/

/-- Un passo interno: una regola della cache `i` (le sue code vengono copiate nel parent) o una
regola del parent sull'indice `i` (le code della cache `i` vengono riallineate). Stessa
composizione di `msi_step_internal`. -/
inductive step_int : MSIState n → MSIInternalEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (cache' : CacheState) (i : Fin n) (e : CacheInternalEvent),
      cache_step (m1.caches i) e cache' →
      step_int m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }
  | parent_upd_queue : ∀ (m1 : MSIState n) (parent' : ParentState n)
      (e : ParentUpdQueueInternalEvent n) (i : Fin n),
      parent_step m1.parent (.upd_queue e i) parent' →
      step_int m1 (.parent (.upd_queue e i))
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i,
                                                             queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent' }

/-- I passi esterni sono quelli di `MSI_def`: il programma accoda load e store, la cache le serve. -/
abbrev step_ext : MSIState n → MSIExternalEvent n → MSIState n → Prop := msi_step_external

/-- I passi interni come `Rule` del framework ARS. -/
def rule (n : Nat) : Rule (MSIState n) := fun a b => ∃ e, step_int a e b

/-- Raggiungibilità nel senso di ARS: da `default`, con passi interni ed esterni. -/
def Reach (x : MSIState n) : Prop :=
  ReachingStar.reachable (rule n) step_ext x (default : MSIState n)

/-! ## Ogni passo nuovo è un passo vecchio -/

theorem cache_step_sub {c c' : CacheState} {e : CacheInternalEvent}
    (h : cache_step c e c') : cache_msi_step_internal c e c' := by
  cases h with
  | release_S_for_store _ _ hS _ => exact .rq_data_not_available1 _ hS
  | upgrade_from_I_rq _ _ hI _ _ => exact .upgrade_from_I_rq _ hI
  | upgrade_from_I_rq1 _ hI _ _ => exact .upgrade_from_I_rq1 _ hI
  | upgrade_from_I_rs v j hj hI => exact .upgrade_from_I_rs _ v j hj hI
  | upgrade_from_I_rsS v j hj hI => exact .upgrade_from_I_rsS _ v j hj hI
  | downgrade_from_M_rs j hj hM _ => exact .downgrade_from_M_rs _ j hj hM
  | downgrade_from_M_rs1 j hj hS _ => exact .downgrade_from_M_rs1 _ j hj hS

theorem parent_step_sub {p p' : ParentState n} {e : ParentInternalEvent n}
    (h : parent_step p e p') : parent_msi_step p e p' := by
  cases h with
  | downgrade_from_M_rq1 v i j hj => exact .downgrade_from_M_rq1 _ v i j hj
  | downgrade_from_M_rq2 i j hj => exact .downgrade_from_M_rq2 _ i j hj
  | upgrade_to_M_data_avilable_rq1 i j hj hall => exact .upgrade_to_M_data_avilable_rq1 _ i j hj hall
  | upgrade_to_M_data_avilable_rq2 i j hj hI hnoM => exact .upgrade_to_M_data_avilable_rq2 _ i j hj hI hnoM
  | upgrade_to_M_invalid_all i i' j hj hM _ => exact .upgrade_to_M_invalid_all _ i i' j hj hM
  | upgrade_to_M_invalid_all1 i i' j hj hS _ => exact .upgrade_to_M_invalid_all1 _ i i' j hj hS
  | upgrade_to_M_invalid_all3 i i' j hj hM _ => exact .upgrade_to_M_invalid_all3 _ i i' j hj hM

/-- **Ogni passo interno di `MSI_final` è un passo interno di `MSI_def`**, con la stessa etichetta.
Quindi gli stati raggiungibili di `MSI_final` sono raggiungibili anche in `MSI_def`, e ciò che è
irraggiungibile là lo è anche qui. -/
theorem step_int_sub {s s' : MSIState n} {e : MSIInternalEvent n} (h : step_int s e s') :
    msi_step_internal s e s' := by
  cases h with
  | cache c' i e hc => exact .cache _ c' i e (cache_step_sub hc)
  | parent_upd_queue p' e i hp => exact .parent_upd_queue _ p' e i (parent_step_sub hp)

end MSIFinal
