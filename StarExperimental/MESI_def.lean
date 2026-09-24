import StarExperimental.MSI_def

/-! # `MESI_def`: il protocollo MESI

Implementazione di MESI ottenuta da MSI (`MSI_def.lean`) cambiando il meno possibile, con lo
**stesso spec** sequenziale di `MSI_flush_proof.lean` (copiato identico in fondo al file). Tutto ciò
che non dipende dal protocollo è riusato da `MSI_def`: `Event`, `Value`, `RsRqEvent`, `update_Fin`
con i suoi lemmi, `MSIExternalEvent` (gli eventi esterni con l'indice della cache). Il resto vive nel
namespace `MESI`.

Che cosa aggiunge `E` (exclusive, linea posseduta in esclusiva ma pulita):
* la directory ha la riga `E`; il parent concede `E` a chi chiede `S` quando nessun'altra cache
  tiene la linea (`upgrade_to_E`), e concede `S` solo se nessuna riga è `M` o `E`;
* la cache in `E` serve le load (passo esterno `ld_rq_data_availableE`), passa a `M` in silenzio e
  senza messaggi quando vuole scrivere (`upgrade_from_E`), e cede la linea come da `M`
  (rilascio spontaneo `rq_data_not_availableE`, invalidate `downgrade_from_E_rs`), rispondendo con
  `rsIμ` e il dato: la riga `E` è trattata dal parent come una riga `M` (il possessore potrebbe
  essere passato a `M` in silenzio), quindi i rilasci portano il dato e le regole del parent che
  processano `rsIμ` restano quelle di MSI;
* le invalidazioni verso una riga `E` sono `rqIμ`, come per `M` (`upgrade_to_M_invalid_allE`,
  `upgrade_to_S_invalid_E`).
Tutto il resto (richieste, grant di `M`/`S`, rilasci da `M`/`S`, invalidazioni) è identico a MSI. -/

open THEORY
open Relation

namespace MESI

/-! ## Eventi e stati -/

inductive Bstate where
  | M -- modified
  | I -- invalid
  | S -- shared
  | E -- exclusive (posseduta in esclusiva, pulita)
deriving DecidableEq, BEq, Repr

instance : Inhabited Bstate where
  default := Bstate.I

/-- Messaggi cache → parent: gli stessi di MSI (chi cede da `E` usa `rsIμ` con il dato). -/
inductive CPEvent where
  | rsIμ (value : Value) -- rilascio da `M` o da `E` (porta il dato)
  | rsIσ                 -- rilascio da `S`
  | rqS                  -- richiesta di `S` (o di `E`, se nessuno tiene la linea)
  | rqM                  -- richiesta di `M`
deriving DecidableEq

/-- Messaggi parent → cache: MSI più il grant di `E`. -/
inductive PCEvent where
  | rqIμ                 -- invalida chi è in `M` o in `E`
  | rqIσ                 -- invalida chi è in `S`
  | rsM (val : Value)    -- grant di `M`
  | rsS (val : Value)    -- grant di `S`
  | rsE (val : Value)    -- grant di `E`
deriving DecidableEq

structure CacheState where
  state : Bstate
  value : Value
  queue_cp : List CPEvent
  queue_pc : List PCEvent
  extqueue : RsRqEvent

deriving instance Inhabited for CacheState

structure ParentState (n : Nat) where
  value : Value
  shared_state : Fin n -> Bstate
  queue_cip : Fin n -> List CPEvent
  queue_pci : Fin n -> List PCEvent

instance : Inhabited (ParentState n) where
  default := ParentState.mk default (fun _ => default) (fun _ => default) default

structure MESIState (n : Nat) where
  caches : Fin n -> CacheState
  parent : ParentState n

instance : Inhabited (MESIState n) where
  default := MESIState.mk default default

/-- Stato iniziale, come `msi_init`: l'unico stato iniziale è `default`. -/
@[simp]
def mesi_init (s : MESIState n) : Prop :=
  (∀ k, (s.caches k).state = Bstate.I ∧ (s.caches k).queue_cp = [] ∧ (s.caches k).queue_pc = []
        ∧ (s.caches k).extqueue.rs = [] ∧ (s.caches k).extqueue.rq = [] ∧ (s.caches k).value = 0)
  ∧ (∀ k, s.parent.shared_state k = Bstate.I ∧ s.parent.queue_cip k = [] ∧ s.parent.queue_pci k = [])
  ∧ s.parent.value = 0

/-- Eventi interni della cache: quelli di MSI più i tre di `E`. -/
inductive CacheInternalEvent where
  | rq_data_not_available
  | upgrade_from_I_rq
  | upgrade_from_I_rs  (v : Value)
  | downgrade_from_M_rs
  | ld_rq_data_not_availableS
  | upgrade_from_I_rqS
  | upgrade_from_I_rsS  (v : Value)
  | downgrade_from_S_rsS
  | upgrade_from_I_rsE  (v : Value)  -- presa del grant di `E`
  | upgrade_from_E                   -- passaggio silenzioso `E → M`
  | rq_data_not_availableE           -- rilascio spontaneo da `E`
  | downgrade_from_E_rs              -- invalidate ricevuto in `E`

/-- Eventi interni del parent: quelli di MSI più il grant di `E` e le invalidazioni di `E`. -/
inductive ParentUpdQueueInternalEvent n where
  | downgrade_from_M_rq1 (v : Value)
  | upgrade_to_M_data_avilable_rq1
  | upgrade_to_M_invalid_all (p' : Fin n)
  | downgrade_from_S_rq1S
  | upgrade_to_S_data_avilable_rq1S
  | upgrade_to_S_invalid_2_rq1S (p' : Fin n)
  | invalid_allS
  | upgrade_to_E_rq1S                 -- grant di `E`
  | upgrade_to_M_invalid_allE (p' : Fin n) -- invalidazione di una riga `E`
  deriving Repr

inductive ParentInternalEvent n where
  | upd_queue (pe : ParentUpdQueueInternalEvent n) (p : Fin n)

inductive MESIInternalEvent n where
  | cache (ce : CacheInternalEvent) (p : Fin n)
  | parent (pe : ParentInternalEvent n)

/-! ## Passi esterni della cache (con l'indice, come `msi_step_external`) -/

/-- Come `cache_msi_step`, più la load servita in `E`. Lo store resta possibile solo in `M`: da `E`
si passa prima a `M` in silenzio (`upgrade_from_E`). -/
inductive cache_mesi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ s1,
      cache_mesi_step s1 Event.ld_rq
        { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.ld_rq] }
  | st_rq : ∀ s1 v,
      cache_mesi_step s1 (Event.st_rq v)
        { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.st_rq v] }
  -- load servita in `S`
  | ld_rq_data_available1 : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.S →
      cache_mesi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst }
  -- load servita in `M`
  | ld_rq_data_available : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.M →
      cache_mesi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst }
  -- load servita in `E` (nuova)
  | ld_rq_data_availableE : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.E →
      cache_mesi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst }
  -- store servita in `M`
  | st_rq_M_state : ∀ s1 v rst,
      s1.extqueue.rq = Event.st_rq v :: rst →
      s1.state = Bstate.M →
      cache_mesi_step s1 Event.st_rs
        { s1 with value := v,
                  extqueue.rs := s1.extqueue.rs ++ [Event.st_rs],
                  extqueue.rq := rst }

/-! ## Passi del parent -/

/-- Le regole di MSI, con tre differenze: il grant di `S` richiede che nessuna riga sia `E` (oltre
che `M`); c'è il grant di `E` (`upgrade_to_E`) a chi chiede `S` quando tutte le righe sono `I`; le
invalidazioni verso una riga `E` sono `rqIμ`, come per `M`. -/
inductive parent_mesi_step : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  -- la cache `i` cede la linea da `M` o da `E`: il parent prende il dato e la mette a `I`
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) v i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      parent_mesi_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i)
        { p1 with value := v,
                  shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip }
  -- la cache `i` cede la linea da `S`
  | downgrade_from_M_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rsIσ →
      parent_mesi_step p1 (.upd_queue .downgrade_from_S_rq1S i)
        { p1 with shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip }
  -- grant di `M` a `i`: nessun'altra cache tiene la linea
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_mesi_step p1 (.upd_queue .upgrade_to_M_data_avilable_rq1 i)
        { p1 with shared_state := update_Fin i Bstate.M p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsM p1.value]) p1.queue_pci }
  -- grant di `S` a `i`: la riga di `i` è `I` e nessuna cache tiene la linea in `M` o in `E`
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      p1.shared_state i = Bstate.I →
      (∀ i, ¬(p1.shared_state i = Bstate.M)) →
      (∀ i, ¬(p1.shared_state i = Bstate.E)) →
      parent_mesi_step p1 (.upd_queue .upgrade_to_S_data_avilable_rq1S i)
        { p1 with shared_state := update_Fin i Bstate.S p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsS p1.value]) p1.queue_pci }
  -- grant di `E` a `i` (nuova): `i` chiede `S` e nessun'altra cache tiene la linea
  | upgrade_to_E : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_mesi_step p1 (.upd_queue .upgrade_to_E_rq1S i)
        { p1 with shared_state := update_Fin i Bstate.E p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsE p1.value]) p1.queue_pci }
  -- `i` chiede `M` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      p1.shared_state i' = Bstate.M →
      parent_mesi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }
  -- `i` chiede `M` e `i'` tiene la linea in `E`: invalida `i'` (nuova)
  | upgrade_to_M_invalid_allE : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      p1.shared_state i' = Bstate.E →
      parent_mesi_step p1 (.upd_queue (.upgrade_to_M_invalid_allE i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }
  -- `i` chiede `M` e `i'` tiene la linea in `S`: invalida `i'`
  | upgrade_to_M_invalid_all1 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqM →
      p1.shared_state i' = Bstate.S →
      parent_mesi_step p1 (.upd_queue .invalid_allS i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIσ]) p1.queue_pci }
  -- `i` chiede `S` e un'altra cache `i'` tiene la linea in `S`: invalida `i'` (facoltativa, come in MSI)
  | upgrade_to_M_invalid_all2 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      ¬(i' = i) →
      p1.shared_state i' = Bstate.S →
      parent_mesi_step p1 (.upd_queue (.upgrade_to_S_invalid_2_rq1S i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIσ]) p1.queue_pci }
  -- `i` chiede `S` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all3 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      p1.shared_state i' = Bstate.M →
      parent_mesi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }
  -- `i` chiede `S` e `i'` tiene la linea in `E`: invalida `i'` (nuova)
  | upgrade_to_S_invalid_E : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some CPEvent.rqS →
      p1.shared_state i' = Bstate.E →
      parent_mesi_step p1 (.upd_queue (.upgrade_to_M_invalid_allE i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci }

/-! ## Passi interni della cache -/

/-- Le regole di MSI più le quattro di `E`: presa del grant di `E`, passaggio silenzioso `E → M`,
rilascio spontaneo da `E` e invalidate ricevuto in `E` (entrambi con `rsIμ` e il dato, come da `M`). -/
inductive cache_mesi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  -- rilascio spontaneo da `M` (porta il dato)
  | rq_data_not_available : ∀ s1,
      s1.state = Bstate.M →
      cache_mesi_step_internal s1 .rq_data_not_available
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value],
                  state := Bstate.I }
  -- rilascio spontaneo da `S`
  | rq_data_not_available1 : ∀ s1,
      s1.state = Bstate.S →
      cache_mesi_step_internal s1 .ld_rq_data_not_availableS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIσ],
                  state := Bstate.I }
  -- rilascio spontaneo da `E` (nuova): la linea è pulita, ma si manda comunque il dato
  | rq_data_not_availableE : ∀ s1,
      s1.state = Bstate.E →
      cache_mesi_step_internal s1 .rq_data_not_availableE
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value],
                  state := Bstate.I }
  -- richiesta di `M` da `I`
  | upgrade_from_I_rq : ∀ s1,
      s1.state = Bstate.I →
      cache_mesi_step_internal s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM] }
  -- richiesta di `S` da `I`
  | upgrade_from_I_rq1 : ∀ s1,
      s1.state = Bstate.I →
      cache_mesi_step_internal s1 .upgrade_from_I_rqS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqS] }
  -- presa del grant di `M`
  | upgrade_from_I_rs : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsM v) →
      s1.state = Bstate.I →
      cache_mesi_step_internal s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j }
  -- presa del grant di `S`
  | upgrade_from_I_rsS : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsS v) →
      s1.state = Bstate.I →
      cache_mesi_step_internal s1 (.upgrade_from_I_rsS v)
        { s1 with state := Bstate.S,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j }
  -- presa del grant di `E` (nuova)
  | upgrade_from_I_rsE : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsE v) →
      s1.state = Bstate.I →
      cache_mesi_step_internal s1 (.upgrade_from_I_rsE v)
        { s1 with state := Bstate.E,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j }
  -- passaggio silenzioso `E → M` (nuova): nessun messaggio, il parent non lo vede
  | upgrade_from_E : ∀ s1,
      s1.state = Bstate.E →
      cache_mesi_step_internal s1 .upgrade_from_E
        { s1 with state := Bstate.M }
  -- invalidate ricevuto in `M`: cede la linea con il dato
  | downgrade_from_M_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIμ →
      s1.state = Bstate.M →
      cache_mesi_step_internal s1 .downgrade_from_M_rs
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value] }
  -- invalidate ricevuto in `E` (nuova): cede la linea con il dato, come da `M`
  | downgrade_from_E_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIμ →
      s1.state = Bstate.E →
      cache_mesi_step_internal s1 .downgrade_from_E_rs
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value] }
  -- invalidate ricevuto in `S`: cede la linea
  | downgrade_from_M_rs1 : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIσ →
      s1.state = Bstate.S →
      cache_mesi_step_internal s1 .downgrade_from_S_rsS
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIσ] }

/-! ## Passi di sistema -/

inductive mesi_step_internal : MESIState n → MESIInternalEvent n → MESIState n → Prop where
  | cache : ∀ m1 cache' i e,
      cache_mesi_step_internal (m1.caches i) e cache' →
      @mesi_step_internal n m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }
  | parent_upd_queue : ∀ m1 parent' e i,
      parent_mesi_step m1.parent (.upd_queue e i) parent' →
      @mesi_step_internal n m1 (.parent (.upd_queue e i))
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i,
                                                             queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent' }

/-- Il passo esterno, etichettato con la cache che riceve l'evento (`MSIExternalEvent n`). -/
inductive mesi_step_external : MESIState n → MSIExternalEvent n → MESIState n → Prop where
  | cache : ∀ m1 e cache' i,
      cache_mesi_step (m1.caches i) e cache' →
      @mesi_step_external n m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }

/-- Comportamenti dell'implementazione, come `imp_behaviour` di MSI. -/
def imp_behaviour (n : Nat) :=
  behaviour_extend (default : MESIState n) mesi_step_external mesi_step_internal

/-! ## Lo spec, identico a quello di `MSI_flush_proof.lean` -/

structure SeqState (n : Nat) where
  memory : Value
  extqueue : Fin n -> RsRqEvent

instance : Inhabited (SeqState n) where
  default := SeqState.mk default (fun _ => default)

/-- Lo spec sequenziale: una memoria e, per ogni cache, la coda esterna; gli eventi portano
l'indice della cache. Identico a `seq_step` di `MSI_flush_proof.lean`. -/
inductive seq_step : SeqState n -> MSIExternalEvent n -> SeqState n -> Prop where
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

def spec_behaviour (n : Nat) :=
  behaviour (seq_init n : SeqState n) seq_step

/-! ## La relazione di flush e l'obiettivo -/

/-- La parte di quiete della flush, come `flush0` di MSI. -/
inductive flush0 (i : MESIState n) (s : SeqState n) : Prop where
  | intro :
      (∀ k, (i.caches k).state = Bstate.I ∧ (i.caches k).queue_cp = [] ∧ (i.caches k).queue_pc = []) →
      (∀ k, i.parent.shared_state k = Bstate.I ∧ i.parent.queue_cip k = [] ∧ i.parent.queue_pci k = []) →
      i.parent.value = s.memory →
      flush0 i s

/-- La flush completa, con le `extqueue`, come in MSI. -/
def flush (i : MESIState n) (s : SeqState n) : Prop :=
  flush0 i s ∧ ∀ k, (i.caches k).extqueue = s.extqueue k

/-! L'obiettivo, `trace_inclusion`, è dimostrato in `MESI_flush_proof.lean`. -/

end MESI
