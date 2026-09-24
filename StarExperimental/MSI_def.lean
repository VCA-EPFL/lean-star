
import Star.BackwardsInvariants.TwoPhaseCommit
import StarExperimental.BackwardGen
import Star.SplitJoin.star

/-! # `MSI_def`: definizioni del protocollo MSI

File di sole *definizioni*, estratto da `MSI.lean` (che ora importa questo file e contiene tutti i
teoremi): eventi, stati, passi di cache/parent/sistema, LTS `MSI`, viste e `msiSetup` per la tattica
backward, stati di arrivo espliciti, passo esterno `msi_step_external`. Restano qui anche i cinque
lemmi di cui le definizioni hanno bisogno: `update_Fin_gso`, `update_Fin_gso2`, `update_Fin_gss`,
`MSIView.parent_step_local` e `MSIView.synced_step` (il campo `inv_step` di `msiSetup` è `synced_step`).
Così `MSI_flush_proof.lean` può importare solo questo file. -/


open THEORY
open Relation


/-!
# Define Events

Protocollo MSI a indirizzo singolo, nello stile di `MI.lean`: niente lenti, niente `Addr`/`Ident`/`Tag`,
niente memoria del parent. Rispetto a MI ci sono lo stato `S` (shared) e i messaggi per prenderlo,
cederlo e invalidarlo.
-/
inductive Bstate where
  | M -- modified
  | I -- invalid
  | S -- shared

deriving instance BEq, Repr for Bstate

instance : Inhabited Bstate where
  default := Bstate.I

abbrev Value := Nat



inductive CPEvent where
  | rsIμ (value : Value) -- rilascio da `M` (porta il dato)
  | rsIσ                 -- rilascio da `S`
  | rqS                  -- richiesta di `S`
  | rqM                  -- richiesta di `M`
deriving DecidableEq

inductive PCEvent where
  | rqIμ                 -- invalida chi è in `M`
  | rqIσ                 -- invalida chi è in `S`
  | rsM (val : Value)    -- grant di `M`
  | rsS (val : Value)    -- grant di `S`
deriving DecidableEq

/-!
# Metadate and Parent Metadata
-/

structure ParentMetadata (n : Nat) where
  state : Bstate
  shared_state : Fin n -> Bstate

inductive Event where
  | ld_rq
  | ld_rs (val : Value)
  | st_rq (val : Value)
  | st_rs
deriving DecidableEq, BEq

structure RsRqEvent where
  rs : List Event
  rq : List Event

deriving instance BEq, Inhabited for RsRqEvent

structure CacheParent (n : Nat) where
  metadata : ParentMetadata n
  value : Value

/-!
# CacheState and ParentState
-/
structure CacheState where
  state : Bstate
  value : Value
  queue_cp : List CPEvent
  queue_pc : List PCEvent
  extqueue : RsRqEvent

deriving instance Inhabited for CacheState

structure ParentState (n : Nat) where
  --state : Bstate
  value : Value
  shared_state : Fin n -> Bstate
  queue_cip : Fin n -> List CPEvent
  queue_pci : Fin n -> List PCEvent
  --memory : Addr -> Value



instance : Inhabited (ParentState n) where
  default := ParentState.mk default (fun _ => default) (fun _ => default)  default



structure MSIState (n : Nat) where
  caches : Fin n -> CacheState
  parent : ParentState n



instance : Inhabited (MSIState n) where
  default:= MSIState.mk default default

/-- Stato iniziale: nessun messaggio in volo, tutte le cache in `I` con le code vuote e
valore `0`, directory del parent tutta a `I` con le code vuote e valore `0`.

I valori vanno fissati (come in `mi_init`): se fossero liberi, nessuno stato sarebbe
raggiungibile da *tutti* gli stati iniziali e `¬ MSI.reachable s` tornerebbe vero a vuoto.
Così invece l'unico stato iniziale è `default`. -/
@[simp]
def msi_init (s : MSIState n) : Prop :=
  (∀ k, (s.caches k).state = Bstate.I ∧ (s.caches k).queue_cp = [] ∧ (s.caches k).queue_pc = []
        ∧ (s.caches k).extqueue.rs = [] ∧ (s.caches k).extqueue.rq = [] ∧ (s.caches k).value = 0)
  ∧ (∀ k, s.parent.shared_state k = Bstate.I ∧ s.parent.queue_cip k = [] ∧ s.parent.queue_pci k = [])
  ∧ s.parent.value = 0



inductive CacheInternalEvent where
  | ld_rs (value : Value)
  | st_rs (value : Value)
  | rq_data_not_available
  | upgrade_from_I_rq
  | upgrade_from_I_rs  (v: Value)
  | downgrade_from_M_rs
  | intro: CacheInternalEvent
  | ld_rq_data_not_availableS
  | upgrade_from_I_rqS
  | upgrade_from_I_rsS  (v: Value)
  | downgrade_from_S_rsS

inductive ParentUpdQueueInternalEvent n where
  | downgrade_from_M_rq1 (v : Value)
  | upgrade_to_M_data_avilable_rq1
  | upgrade_to_M_invalid_all (p' : Fin n)
  | downgrade_from_S_rq1S
  | upgrade_to_S_data_avilable_rq1S
  | upgrade_to_S_invalid_2_rq1S (p' : Fin n)
  | invalid_allS
  | invalid_allM
  | dawngrade_safe_parent_rq1
  | dawngrade_safe_parent_rq1S
  deriving Repr

inductive ParentNoQueueInternalEvent where
  | upgrade_to_M_data_not_avilable_rq1
  | dawngrade_safe_parent_rq1
  | upgrade_to_S_data_not_avilable_rq1S
  | dawngrade_safe_parent_rq1S
deriving Repr

inductive ParentInternalEvent n where
  | upd_queue (pe : ParentUpdQueueInternalEvent n) (p : Fin n)
  | no_queue (pe : ParentNoQueueInternalEvent) (p : Fin n)
  | intro: ParentInternalEvent n

inductive MSIInternalEvent n where
  | cache (ce : CacheInternalEvent) (p : Fin n)
  | parent (pe : ParentInternalEvent n)
  | intro : MSIInternalEvent n
/-!
# MSI State
-/


/-!
# Cache step and Cache internal step
-/



inductive cache_msi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ s1 ,
      cache_msi_step s1 Event.ld_rq
        { s1 with extqueue.rq := (s1.extqueue.rq) ++ [Event.ld_rq]
        }
  | st_rq : ∀ s1 v,
      cache_msi_step s1 (Event.st_rq v)
      { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.st_rq v]
      }
  -- load servita in `S`: risposta all'esterno (evento `ld_rs value`)
  | ld_rq_data_available1 : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.S →
      cache_msi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst
        }
  -- load servita in `M`: risposta all'esterno (evento `ld_rs value`). Era un passo interno: così
  -- la risposta non compariva nella traccia e i passi interni toccavano le `extqueue`.
  | ld_rq_data_available : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.M →
      cache_msi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst
        }
  -- store servita in `M`: risposta all'esterno (evento `st_rs`)
  | st_rq_M_state : ∀ s1 v rst,
      s1.extqueue.rq = Event.st_rq v :: rst →
      s1.state = Bstate.M →
      cache_msi_step s1 Event.st_rs
        { s1 with value := v,
                  extqueue.rs := s1.extqueue.rs ++ [Event.st_rs]
                  extqueue.rq := rst
        }


/-!
# Parent step
-/

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



/-- Regole del parent (tutte `upd_queue`). Le quattro regole `no_queue` del vecchio file
(`upgrade_to_M_data_not_avilable_rq1/rq2`, `dawngrade_safe_parent_rq1/rq2`) cambiavano solo
stato, tag e memoria del parent: senza indirizzi sarebbero passi identità, e come in
`MI.lean` non ci sono. -/
inductive parent_msi_step : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  -- la cache `i` cede la linea da `M`: il parent prende il dato e la mette a `I`
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) v i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      parent_msi_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i)
        { p1 with value := v,
                  shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip
        }
  -- la cache `i` cede la linea da `S`: il parent la mette a `I`
  | downgrade_from_M_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rsIσ) →
      parent_msi_step p1 (.upd_queue (.downgrade_from_S_rq1S) i)
        { p1 with shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip
        }
  -- grant di `M` a `i`: nessun'altra cache tiene la linea
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rqM) →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)
        { p1 with shared_state := update_Fin i Bstate.M p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsM p1.value]) p1.queue_pci
        }
  -- grant di `S` a `i`: la riga di `i` è a `I` e nessuna cache tiene la linea in `M`
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rqS) →
      p1.shared_state i = Bstate.I →
      (∀ i, ¬(p1.shared_state i = Bstate.M)) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_data_avilable_rq1S) i)
        { p1 with shared_state := update_Fin i Bstate.S p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsS p1.value]) p1.queue_pci
        }
  -- `i` chiede `M` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM) →
      p1.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci
        }
  -- `i` chiede `M` e `i'` tiene la linea in `S`: invalida `i'`
  | upgrade_to_M_invalid_all1 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM) →
      p1.shared_state i' = Bstate.S →
      parent_msi_step p1 (.upd_queue (.invalid_allS) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIσ]) p1.queue_pci
        }
  -- `i` chiede `S` e un'altra cache `i'` tiene la linea in `S`: invalida `i'`
  -- (nel vecchio file serviva a sgomberare la linea del parent; con un solo indirizzo è facoltativa)
  | upgrade_to_M_invalid_all2 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS) →
      ¬(i' = i) →
      p1.shared_state i' = Bstate.S →
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_invalid_2_rq1S i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIσ]) p1.queue_pci
        }
  -- `i` chiede `S` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all3 : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS) →
      p1.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci
        }



inductive cache_msi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  -- (la load servita in `M` è ora il passo esterno `cache_msi_step.ld_rq_data_available`)
  -- rilascio spontaneo da `M` (porta il dato)
  | rq_data_not_available : ∀ s1,
      s1.state = Bstate.M →
      cache_msi_step_internal s1 .rq_data_not_available
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value],
                  state := Bstate.I
        }
  -- rilascio spontaneo da `S`
  | rq_data_not_available1 : ∀ s1,
      s1.state = Bstate.S →
      cache_msi_step_internal s1 .ld_rq_data_not_availableS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIσ],
                  state := Bstate.I
        }
  -- richiesta di `M` da `I`
  | upgrade_from_I_rq : ∀ s1,
      s1.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM ] }
  -- richiesta di `S` da `I`
  | upgrade_from_I_rq1 : ∀ s1,
      s1.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rqS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqS ] }
  -- presa del grant di `M`
  | upgrade_from_I_rs : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsM v) →
      s1.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j
        }
  -- presa del grant di `S`
  | upgrade_from_I_rsS : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsS v) →
      s1.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rsS v)
        { s1 with state := Bstate.S,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j
        }
  -- invalidate ricevuto in `M`: cede la linea con il dato
  | downgrade_from_M_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some (PCEvent.rqIμ) →
      s1.state = Bstate.M →
      cache_msi_step_internal s1 (.downgrade_from_M_rs)
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value]
        }
  -- invalidate ricevuto in `S`: cede la linea
  | downgrade_from_M_rs1 : ∀ s1 j,
      (s1.queue_pc)[j]? = some (PCEvent.rqIσ) →
      s1.state = Bstate.S →
      cache_msi_step_internal s1 (.downgrade_from_S_rsS)
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIσ]
        }





/-!
# MSI step and MSI internal step
-/


inductive msi_step_internal : MSIState n → MSIInternalEvent n → MSIState n → Prop where
  | cache : ∀ m1 cache' i e,
      cache_msi_step_internal (m1.caches i) e cache' →
      @msi_step_internal n m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci
        }
  | parent_upd_queue : ∀ m1 parent' e i,
      parent_msi_step m1.parent (.upd_queue e i) parent' →
      @msi_step_internal n m1 (.parent (.upd_queue e i))
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent'
        }
  | parent_no_queue : ∀ m1 parent' e i,
      parent_msi_step m1.parent (.no_queue e i) parent' →
      @msi_step_internal n m1 (.parent (.no_queue e i))
        { m1 with parent := parent' }

inductive msi_step : MSIState n → Event → MSIState n → Prop where
  | cache : ∀ m1 cache' i e,
      cache_msi_step (m1.caches i) e cache' →
      @msi_step n m1 e
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci
        }


-- define al LTS

structure MSI.LTS (T : Type) where
  S : Type
  transitions : S → T → S → Prop
  init : S → Prop
  --flushed : S → Prop

def MSI.LTS.atrans {T} (l : MSI.LTS T) : l.S → l.S → Prop := fun s s' =>
  ∃ t, l.transitions s t s'

def MSI.LTS.reachable {T} (l : MSI.LTS T) : l.S → Prop := fun s =>
  ∀ s_init, l.init s_init → ReflTransGen l.atrans s_init s

def MSI.LTS.backwards_reachable_from {T} (l : MSI.LTS T) (s s' : l.S) :=
  ReflTransGen (Function.swap l.atrans) s s'

def get {T} (l : MSI.LTS T) (s_init s) :=
  l.backwards_reachable_from s_init s
  ∨ (∃ (P : l.S → Prop), P s ∧ (∀ s', P s' → l.backwards_reachable_from s_init s'))

def MSI {n : Nat}: MSI.LTS (MSIInternalEvent n) where
  S := MSIState n
  transitions := msi_step_internal
  init s := msi_init s
  --flushed s := φ s




/-! ## Vista, invariante e tattica backward su `MSI`

La stessa macchina di `MI.lean`: la *vista* di una coppia di indici, l'invariante `synced`,
l'insieme delle viste cattive `badView` e la tattica `new_backward_tatic`. La vista tiene lo
stato della cache `i`, le righe della directory di `i` e di `j`, i messaggi con token `M`
(`rsM`, `rsIμ`) e con token `S` (`rsS`, `rsIσ`) in volo per `i`, contati e saturati, e il
flag `i = j`: 486 viste in tutto. La tattica chiude grazie alla guardia `shared_state i = I` sul
grant di `S`: senza di essa una cache può ricevere due `rsS` (o un `rsS` con il suo `rsIσ` ancora
in coda) e le viste cattive diventano raggiungibili. -/

open BackwardGen

namespace MSIView

/-- Scritta a mano e non con `deriving`, come in `MI.lean`. -/
instance : DecidableEq Bstate := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)

/-- La vista della coppia `(i, j)`: stato della cache `i`, righe di `i` e di `j`, messaggi con
token `M` e con token `S` in volo per `i` (saturati), e il flag `i = j`. -/
structure View where
  c0 : Bstate
  d0 : Bstate
  d1 : Bstate
  m0 : Cnt
  s0 : Cnt
  /-- `decide (i = j)`: così anche `i = j` è ammesso, e le proprietà su un solo indice
  si esprimono ignorando la seconda componente. -/
  eq : Bool
deriving DecidableEq, Repr

/-- Un messaggio parent → cache porta il token `M` se è la concessione di `M`. -/
def isGrantM : PCEvent → Bool
  | .rsM _ => true
  | .rsS _ => false
  | .rqIμ  => false
  | .rqIσ  => false

/-- Un messaggio parent → cache porta il token `S` se è la concessione di `S`. -/
def isGrantS : PCEvent → Bool
  | .rsM _ => false
  | .rsS _ => true
  | .rqIμ  => false
  | .rqIσ  => false

/-- Un messaggio cache → parent porta il token `M` se è la restituzione da `M`. -/
def isReleaseM : CPEvent → Bool
  | .rsIμ _ => true
  | .rsIσ   => false
  | .rqS    => false
  | .rqM    => false

/-- Un messaggio cache → parent porta il token `S` se è la restituzione da `S`. -/
def isReleaseS : CPEvent → Bool
  | .rsIμ _ => false
  | .rsIσ   => true
  | .rqS    => false
  | .rqM    => false

/-- Messaggi con token `M` per l'indice `k`, contati dal lato parent. -/
def muMsgs {n} (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP isGrantM + (p.queue_cip k).countP isReleaseM

/-- Messaggi con token `S` per l'indice `k`, contati dal lato parent. -/
def sigMsgs {n} (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP isGrantS + (p.queue_cip k).countP isReleaseS

/-- Un passo del parent modifica solo l'indice dell'evento. -/
theorem parent_step_local {n} {p1 p2 : ParentState n} {e i}
    (h : parent_msi_step p1 (.upd_queue e i) p2) :
    ∀ k, ¬(k = i) → p2.queue_cip k = p1.queue_cip k ∧ p2.queue_pci k = p1.queue_pci k
                    ∧ p2.shared_state k = p1.shared_state k := by
  cases h <;> intro k hk <;>
    exact ⟨by simp [update_Fin_gso2 _ _ _ _ hk], by simp [update_Fin_gso2 _ _ _ _ hk],
           by simp [update_Fin_gso2 _ _ _ _ hk]⟩

/-- La vista della coppia `(i, j)`. -/
def msiView {n} (s : MSIState n) (i j : Fin n) : View :=
  ⟨(s.caches i).state,
   s.parent.shared_state i, s.parent.shared_state j,
   Cnt.ofCount (muMsgs s.parent i), Cnt.ofCount (sigMsgs s.parent i),
   decide (i = j)⟩

/-- Le due copie di ogni coda (lato parent e lato cache) coincidono. -/
def synced {n} (s : MSIState n) : Prop :=
  ∀ k, s.parent.queue_cip k = (s.caches k).queue_cp ∧ s.parent.queue_pci k = (s.caches k).queue_pc

theorem synced_step {n} {s s' : MSIState n} {t} (hs : synced s) (h : msi_step_internal s t s') :
    synced s' := by
  cases h with
  | cache cache' p e hc =>
      intro k
      by_cases hk : k = p
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2]
  | parent_upd_queue parent' e q hp =>
      intro k
      by_cases hk : k = q
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        obtain ⟨h3, h4, _⟩ := parent_step_local hp k hk
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2, h3, h4]
  | parent_no_queue parent' e i hp =>
      cases hp

/-- **Le viste cattive**: le violazioni di "un solo proprietario di `M`, registrato dal parent,
che esclude tutto il resto; ogni portatore di `S` registrato dal parent":
1. due messaggi con lo stesso token per lo stesso indice, o un token `M` e uno `S` insieme;
2. un token in volo per un indice la cui riga non lo registra;
3. una cache in `M` (in `S`) con token in volo per sé o con la riga sbagliata;
4. la riga `M` di `i` con la riga di `j ≠ i` non a `I`; la riga `S` di `i` con la riga di `j` a `M`;
5. la cache `i` in `M` (o un token `M` per `i`) con la riga di `j ≠ i` non a `I`;
   la cache `i` in `S` (o un token `S` per `i`) con la riga di `j` a `M`. -/
def badView (v : View) : Prop :=
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

def msiSetup (n : Nat) : SymSetup (MSIState n) (MSIInternalEvent n) (Fin n) View where
  trans := msi_step_internal
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step hs h
  view := msiView
  bad := badView
  s0 := default
  inv0 := fun _ => ⟨rfl, rfl⟩

end MSIView

open MSIView


/-! ### Stati di arrivo espliciti e lemmi di inversione per i passi del parent -/

/-- Lo stato dopo `downgrade_from_M_rq1 v` all'indice `i`, consumando la posizione `j`. -/
def downgradeMSt {n} (s : MSIState n) (v : Value) (i : Fin n) (j : Nat) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with
        value := v,
        shared_state := update_Fin i Bstate.I s.parent.shared_state,
        queue_cip := update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'


/-- Lo stato dopo `downgrade_from_S_rq1S` all'indice `i`, consumando la posizione `j`. -/
def downgradeSSt {n} (s : MSIState n) (i : Fin n) (j : Nat) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with
        shared_state := update_Fin i Bstate.I s.parent.shared_state,
        queue_cip := update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'


/-- Lo stato dopo il grant `upgrade_to_M_data_avilable_rq1` all'indice `i`, consumando `j`. -/
def grantMSt {n} (s : MSIState n) (i : Fin n) (j : Nat) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with
        shared_state := update_Fin i Bstate.M s.parent.shared_state,
        queue_cip := update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip,
        queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rsM s.parent.value]) s.parent.queue_pci }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'


/-- Lo stato dopo il grant `upgrade_to_S_data_avilable_rq1S` all'indice `i`, consumando `j`. -/
def grantSSt {n} (s : MSIState n) (i : Fin n) (j : Nat) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with
        shared_state := update_Fin i Bstate.S s.parent.shared_state,
        queue_cip := update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip,
        queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rsS s.parent.value]) s.parent.queue_pci }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'


/-- Lo stato dopo un invalidate `rqIμ` accodato a `i` (le copie della cache riallineate). -/
def invMSt {n} (s : MSIState n) (i : Fin n) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rqIμ]) s.parent.queue_pci }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'

/-- Lo stato dopo un invalidate `rqIσ` accodato a `i` (le copie della cache riallineate). -/
def invSSt {n} (s : MSIState n) (i : Fin n) : MSIState n :=
  let parent' : ParentState n :=
    { s.parent with queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rqIσ]) s.parent.queue_pci }
  MSIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'


/-! ### Stati di arrivo espliciti per gli effetti di una cache (per gli enunciati "a meno di") -/

/-- La cache `i` accoda `rqM` (copia del parent riallineata). -/
def reqMSt {n} (s : MSIState n) (i : Fin n) : MSIState n :=
  { s with caches := update_Fin i { s.caches i with queue_cp := (s.caches i).queue_cp ++ [CPEvent.rqM] } s.caches,
           parent.queue_cip := update_Fin i ((s.caches i).queue_cp ++ [CPEvent.rqM]) s.parent.queue_cip }

/-- La cache `i` accoda `rqS` (copia del parent riallineata). -/
def reqSSt {n} (s : MSIState n) (i : Fin n) : MSIState n :=
  { s with caches := update_Fin i { s.caches i with queue_cp := (s.caches i).queue_cp ++ [CPEvent.rqS] } s.caches,
           parent.queue_cip := update_Fin i ((s.caches i).queue_cp ++ [CPEvent.rqS]) s.parent.queue_cip }

/-- La cache `i` toglie la posizione `j` dalla sua coda `queue_pc` (copia del parent riallineata):
è l'effetto dello scarto di un invalidate stantio, che il modello non ha come regola. -/
def dropSt {n} (s : MSIState n) (i : Fin n) (j : Nat) : MSIState n :=
  { s with caches := update_Fin i { s.caches i with queue_pc := (s.caches i).queue_pc.eraseIdx j } s.caches,
           parent.queue_pci := update_Fin i ((s.caches i).queue_pc.eraseIdx j) s.parent.queue_pci }


/-! ### Passo esterno di sistema (la cache `i` riceve un evento esterno) -/

/-- Evento esterno etichettato con la cache che lo riceve. -/
inductive MSIExternalEvent (n : Nat) where
  | cache (e : Event) (i : Fin n)

inductive msi_step_external : MSIState n → MSIExternalEvent n → MSIState n → Prop where
  | cache : ∀ m1 e cache' i,
      cache_msi_step (m1.caches i) e cache' →
      @msi_step_external n m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci
        }



/-- Comportamenti dell'implementazione: tracce esterne (`Event`) da uno stato iniziale, con passi
interni liberi. `behaviour_extend` vuole uno *stato* iniziale, non il predicato `msi_init`: l'unico
stato che soddisfa `msi_init` è `default` (vedi il commento a `msi_init`), quindi si parte da lì. -/
def imp_behaviour (n : Nat) := behaviour_extend (default : MSIState n) msi_step_external msi_step_internal
