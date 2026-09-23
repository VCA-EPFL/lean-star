
import Star.BackwardsInvariants.TwoPhaseCommit
import StarExperimental.BackwardGen

open THEORY
open Relation


/-!
# Define Events
-/
inductive Bstate where
  | M -- shared
  | I -- invalid

deriving instance BEq, Repr for Bstate

instance : Inhabited Bstate where
  default := Bstate.I

def maxAddr : Nat := 2^16-1
def Addr := Fin maxAddr
--abbrev Addr := Nat
abbrev Value := Nat
abbrev Ident := Nat
abbrev Tag := Addr



inductive CPEvent where
  | rsIμ (value : Value)
  | rqM
deriving DecidableEq

inductive PCEvent where
  | rqIμ
  | rsM  (val: Value)
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



structure MIState (n : Nat) where
  caches : Fin n -> CacheState
  parent : ParentState n



instance : Inhabited (MIState n) where
  default:= MIState.mk default default --default_connections

/-- Stato iniziale: nessun messaggio in volo, tutte le cache in `I` con le code vuote e
valore `0`, directory del parent tutta a `I` con le code vuote e valore `0`.

I valori vanno fissati: se fossero liberi, nessuno stato sarebbe raggiungibile da *tutti*
gli stati iniziali (i passi interni non possono riallineare tutti i valori), e
`¬ MI.reachable s` tornerebbe vero a vuoto per ogni `s`, come col vecchio
`mi_init = True`. Così invece l'unico stato iniziale è `default`. -/
@[simp]
def mi_init (s : MIState n) : Prop :=
  (∀ k, (s.caches k).state = Bstate.I ∧ (s.caches k).queue_cp = [] ∧ (s.caches k).queue_pc = []
        ∧ (s.caches k).extqueue.rs = [] ∧ (s.caches k).extqueue.rq = [] ∧ (s.caches k).value = 0)
  ∧ (∀ k, s.parent.shared_state k = Bstate.I ∧ s.parent.queue_cip k = [] ∧ s.parent.queue_pci k = [])
  ∧ s.parent.value = 0



inductive CacheInternalEvent where
  | ld_rs (value : Value)
  | st_rs (value : Value)
  | rq_data_not_available
  | upgrade_from_I_rq
  | upgrade_from_I_rs  (v: Value) --(n : Nat)
  | downgrade_from_M_rs --(n : Nat)
  | downgrade_from_M_rs1
  | intro: CacheInternalEvent
  | ld_rq_data_not_availableS
  | upgrade_from_I_rqS
  | upgrade_from_I_rsS  (v: Value) --(n : Nat)
  | downgrade_from_S_rsS --(n : Nat)
  | store_deadlockS
  | mistep_cache
  | sistep_cache

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

inductive MIInternalEvent n where
  | cache (ce : CacheInternalEvent) (p : Fin n)
  | parent (pe : ParentInternalEvent n)
  | intro : MIInternalEvent n
/-!
# MI State
-/


/-!
# Cache step and Cache internal step
-/



inductive cache_mi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ s1 ,
      cache_mi_step s1 Event.ld_rq
        { s1 with extqueue.rq := (s1.extqueue.rq) ++ [Event.ld_rq]
        }
  | st_rq : ∀ s1 v,
      cache_mi_step s1 (Event.st_rq v)
      { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.st_rq v]
      }
  | ld_rs : ∀ s1 v rst,
      s1.extqueue.rs = (Event.ld_rs v) :: rst →
      cache_mi_step s1 (Event.ld_rs v)
      { s1 with extqueue.rs := rst
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



/-- Aggiornare due indici (anche uguali) con la stessa `append` commuta. -/
theorem update_Fin_append_comm {α : Type} {n} (f : Fin n → List α) (a b : Fin n) (x : List α) :
    update_Fin a (update_Fin b (f b ++ x) f a ++ x) (update_Fin b (f b ++ x) f)
      = update_Fin b (update_Fin a (f a ++ x) f b ++ x) (update_Fin a (f a ++ x) f) := by
  funext k
  by_cases hab : a = b
  · subst hab; simp [update_Fin]
  · by_cases hka : k = a
    · subst hka; simp [update_Fin, Ne.symm hab]
    · by_cases hkb : k = b
      · subst hkb; simp [update_Fin, hab]
      · simp [update_Fin, Ne.symm hka, Ne.symm hkb]

/-- Aggiornare due volte lo stesso indice: vince l'ultimo. -/
theorem update_Fin_update_Fin_same {α : Type} {n} (i : Fin n) (e e' : α) (f : Fin n → α) :
    update_Fin i e (update_Fin i e' f) = update_Fin i e f := by
  funext q
  by_cases hq : q = i
  · subst hq; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hq]

/-- Rimettere il valore che c'era non cambia nulla. -/
theorem update_Fin_self {α : Type} {n} (i : Fin n) (f : Fin n → α) :
    update_Fin i (f i) f = f := by
  funext q
  by_cases hq : q = i
  · subst hq; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hq]


inductive parent_mi_step : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) v i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rsIμ v) →
      parent_mi_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i)
        { p1 with value := v,
                  shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip
        }
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) i j,
      (p1.queue_cip i)[j]? = some (CPEvent.rqM) →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_mi_step p1 (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)
        { p1 with shared_state := update_Fin i Bstate.M p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).eraseIdx j) p1.queue_cip,
                  queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rsM p1.value]) p1.queue_pci
        }
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) i i' (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM) →
      ¬(p1.shared_state i' = Bstate.I) →
      parent_mi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i ) i')
        { p1 with queue_pci := update_Fin i' (p1.queue_pci i' ++ [PCEvent.rqIμ]) p1.queue_pci
        }
  | invalid_all : ∀ (p1 : ParentState n)  i,
      p1.shared_state i = Bstate.M →
      parent_mi_step p1 (.upd_queue (.invalid_allM) i)
        { p1 with queue_pci := update_Fin i (p1.queue_pci i ++ [PCEvent.rqIμ]) p1.queue_pci }


/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem parent_mi_step_congr {n} {p1 p2 p2' : ParentState n} {e : ParentInternalEvent n}
    (h : parent_mi_step p1 e p2) (heq : p2 = p2') : parent_mi_step p1 e p2' := heq ▸ h

/-- Estensionalità campo per campo (puntuale sulle funzioni) di `MIState`. -/
theorem MIState.ext_all {n} {a b : MIState n}
    (hc : ∀ k, a.caches k = b.caches k)
    (hv : a.parent.value = b.parent.value)
    (hs : ∀ k, a.parent.shared_state k = b.parent.shared_state k)
    (hq1 : ∀ k, a.parent.queue_cip k = b.parent.queue_cip k)
    (hq2 : ∀ k, a.parent.queue_pci k = b.parent.queue_pci k) : a = b := by
  obtain ⟨ca, pv, ps, pq1, pq2⟩ := a
  obtain ⟨cb, pv', ps', pq1', pq2'⟩ := b
  have e1 : ca = cb := funext hc
  have e2 : pv = pv' := hv
  have e3 : ps = ps' := funext hs
  have e4 : pq1 = pq1' := funext hq1
  have e5 : pq2 = pq2' := funext hq2
  subst e1 e2 e3 e4 e5
  rfl


inductive cache_mi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  | ld_rq_data_available : ∀ s1 rst,
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.M →
      cache_mi_step_internal s1 (CacheInternalEvent.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst
        }
  | st_rq_M_state : ∀ s1 v rst,
      s1.extqueue.rq = Event.st_rq v :: rst →
      s1.state = Bstate.M →
      cache_mi_step_internal s1 (CacheInternalEvent.st_rs v)
        { s1 with value := v,
                  extqueue.rq := rst
        }
  | rq_data_not_available : ∀ s1,
      s1.state = Bstate.M →
      cache_mi_step_internal s1 .rq_data_not_available
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value],
                  state := Bstate.I
        }
  | upgrade_from_I_rq : ∀ s1,
      s1.state = Bstate.I →
      cache_mi_step_internal s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM ] }
  | upgrade_from_I_rs : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsM v) →
      s1.state = Bstate.I →
      cache_mi_step_internal s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M,
                  value := v,
                  queue_pc := s1.queue_pc.eraseIdx j
        }
  | downgrade_from_M_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some (PCEvent.rqIμ) →
      s1.state = Bstate.M →
      cache_mi_step_internal s1 (.downgrade_from_M_rs)
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value]
        }
  | downgrade_from_M_rs1 : ∀ s1 j,
      (s1.queue_pc)[j]? = some (PCEvent.rqIμ) →
      s1.state = Bstate.I →
      cache_mi_step_internal s1 (.downgrade_from_M_rs1)
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j
        }





/-!
# MI step and MI internal step
-/


inductive mi_step_internal : MIState n → MIInternalEvent n → MIState n → Prop where
  | cache : ∀ m1 cache' i e,
      cache_mi_step_internal (m1.caches i) e cache' →
      @mi_step_internal n m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci
        }
  | parent_upd_queue : ∀ m1 parent' e i,
      parent_mi_step m1.parent (.upd_queue e i) parent' →
      @mi_step_internal n m1 (.parent (.upd_queue e i))
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent'
        }
  | parent_no_queue : ∀ m1 parent' e i,
      parent_mi_step m1.parent (.no_queue e i) parent' →
      @mi_step_internal n m1 (.parent (.no_queue e i))
        { m1 with parent := parent' }


/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem mi_step_congr {n} {s s' s'' : MIState n} {t : MIInternalEvent n}
    (h : mi_step_internal s t s') (heq : s' = s'') : mi_step_internal s t s'' := heq ▸ h

-- inductive mi_step_external : MIState n → Event → MIState n → Prop where
--   | cache : ∀ m1 e cache' i,
--       cache_mi_step (m1.caches.fin_at i) e cache' →
--       mi_step_external m1 (Event.tag n i e)
--         { m1 with caches.fin_at i := cache',
--                   parent.queue_cip.fin_at i := cache'.queue_cp,
--                   parent.queue_pci.fin_at i := cache'.queue_pc
--         }


theorem lst_get {α} (l : List α) (a : α) : (l ++ [a])[l.length]? = some a := by simp

theorem lst_erase {α} (l : List α) (a : α) : (l ++ [a]).eraseIdx l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem lst_get2 {α} (l : List α) (a b : α) : ((l ++ [a]) ++ [b])[l.length]? = some a := by
  rw [List.append_assoc]; simp

theorem lst_erase2 {α} (l : List α) (a b : α) :
    ((l ++ [a]) ++ [b]).eraseIdx l.length = l ++ [b] := by
  rw [List.append_assoc]
  show (l ++ [a, b]).eraseIdx l.length = l ++ [b]
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]


/-- Cancellare una posizione valida da `replicate m a` dà `replicate (m - 1) a`. -/
theorem eraseIdx_replicate_of_lt {α : Type} (a : α) : ∀ (m j : Nat), j < m →
    (List.replicate m a).eraseIdx j = List.replicate (m - 1) a := by
  intro m
  induction m with
  | zero => intro j h; omega
  | succ m ih =>
    intro j hj
    cases j with
    | zero => simp [List.replicate_succ]
    | succ j =>
      simp only [List.replicate_succ, List.eraseIdx_cons_succ, ih j (by omega), Nat.add_sub_cancel]
      cases m with
      | zero => omega
      | succ m => simp [List.replicate_succ]

/-- Se la lista è costante, cancellare due posizioni valide dà la stessa lista. -/
theorem eraseIdx_eq_of_all_eq {α : Type} (a : α) : ∀ (l : List α) (j₁ j₂ : Nat),
    (∀ x ∈ l, x = a) → j₁ < l.length → j₂ < l.length → l.eraseIdx j₁ = l.eraseIdx j₂ := by
  intro l j₁ j₂ h h₁ h₂
  generalize hm : l.length = m at h₁ h₂
  have hl : l = List.replicate m a := List.eq_replicate_iff.mpr ⟨hm, h⟩
  subst hl
  rw [eraseIdx_replicate_of_lt a m j₁ h₁, eraseIdx_replicate_of_lt a m j₂ h₂]

-- define al LTS

structure MI.LTS (T : Type) where
  S : Type
  transitions : S → T → S → Prop
  init : S → Prop
  --flushed : S → Prop

def MI.LTS.atrans {T} (l : MI.LTS T) : l.S → l.S → Prop := fun s s' =>
  ∃ t, l.transitions s t s'

def MI.LTS.reachable {T} (l : MI.LTS T) : l.S → Prop := fun s =>
  ∀ s_init, l.init s_init → ReflTransGen l.atrans s_init s

def MI.LTS.backwards_reachable_from {T} (l : MI.LTS T) (s s' : l.S) :=
  ReflTransGen (Function.swap l.atrans) s s'

-- inductive MI.LTS.φ {T} (l : MI.LTS T) : l.S → Prop where
-- | flushed {s} : l.flushed s → l.φ s
-- | back_step {s s'} : l.atrans s s' → l.φ s' → l.φ s

def get {T} (l : MI.LTS T) (s_init s) :=
  l.backwards_reachable_from s_init s
  ∨ (∃ (P : l.S → Prop), P s ∧ (∀ s', P s' → l.backwards_reachable_from s_init s'))

theorem backwards_reachable_not_init {T} {l : MI.LTS T} {s} :
  (∀ s_init, l.init s_init → l.backwards_reachable_from s s_init) ↔ l.reachable s := by
  grind [MI.LTS.reachable, MI.LTS.backwards_reachable_from, Relation.reflTransGen_swap]

theorem backwards_reachable_φ {T} {l : LTS T} {s} :
  l.φ s → ∃ s_init, l.flushed s_init ∧ l.backwards_reachable_from s_init s := by
  intro h; induction h <;> grind [LTS.backwards_reachable_from]

theorem φ_backwards_reachable {T} {l : LTS T} {s} :
  ∀ s_init, l.flushed s_init → l.backwards_reachable_from s_init s → l.φ s := by
  dsimp [LTS.backwards_reachable_from]; intro s_init hinit htrans
  induction htrans
  · apply LTS.φ.flushed; assumption
  · apply LTS.φ.back_step; assumption; assumption




def MI {n : Nat}: MI.LTS (MIInternalEvent n) where
  S := MIState n
  transitions := mi_step_internal
  init s := mi_init s
  --flushed s := φ s




/-! ## Vista, invariante e tattica backward su `MI`

Quello che `backward_search_gen` (BackwardGen.lean) deve sapere di `MI`: la *vista* di una
coppia di indici (stato delle cache, righe della directory, messaggi con token in volo
contati e saturati, e il flag `i = j`), l'invariante `synced` (le due copie di ogni coda
coincidono), l'insieme delle viste cattive `badView` (tutte le violazioni di "un solo
token, registrato dal parent"), e i lemmi sui dati. `new_backward_tatic` è la tattica con
questi parametri già messi. -/

open BackwardGen

namespace MIView

/-- Scritta a mano e non con `deriving`: il gestore di `deriving` genera `Bstate.ofNat`, che
`Tatic.lean` (che deriva a sua volta) ridichiarerebbe. -/
instance : DecidableEq Bstate := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)

/-- La vista di una coppia di indici: stato delle due cache, righe della directory,
messaggi con token in volo (saturati). -/
structure View where
  c0 : Bstate
  c1 : Bstate
  d0 : Bstate
  d1 : Bstate
  m0 : Cnt
  m1 : Cnt
  /-- `decide (i = j)`: così anche `i = j` è ammesso, e le proprietà su un solo indice
  si esprimono ignorando la seconda componente. -/
  eq : Bool
deriving DecidableEq, Repr

/-- Un messaggio parent → cache porta il token se è la concessione della linea. -/
def isGrant : PCEvent → Bool
  | .rsM _ => true
  | .rqIμ  => false

/-- Un messaggio cache → parent porta il token se è la restituzione della linea. -/
def isRelease : CPEvent → Bool
  | .rsIμ _ => true
  | .rqM    => false

/-- Messaggi che portano il token per l'indice `k`, contati dal lato parent. -/
def parentMsgs {n} (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP isGrant + (p.queue_cip k).countP isRelease

/-- Cancellare l'elemento in posizione `j` fa calare di uno il conteggio, se quell'elemento
soddisfa il predicato. -/
theorem countP_eraseIdx {α} (p : α → Bool) : ∀ (l : List α) (j : Nat) (a : α),
    l[j]? = some a → (l.eraseIdx j).countP p + (if p a then 1 else 0) = l.countP p := by
  intro l
  induction l with
  | nil => intro j a h; simp at h
  | cons x xs ih =>
    intro j a h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.eraseIdx_cons_zero, List.countP_cons]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hh := ih j a h
      simp only [List.eraseIdx_cons_succ, List.countP_cons]
      omega

/-- Un passo del parent modifica solo l'indice dell'evento. -/
theorem parent_step_local {n} {p1 p2 : ParentState n} {e i}
    (h : parent_mi_step p1 (.upd_queue e i) p2) :
    ∀ k, ¬(k = i) → p2.queue_cip k = p1.queue_cip k ∧ p2.queue_pci k = p1.queue_pci k
                    ∧ p2.shared_state k = p1.shared_state k := by
  cases h <;> intro k hk <;>
    exact ⟨by simp [update_Fin_gso2 _ _ _ _ hk], by simp [update_Fin_gso2 _ _ _ _ hk],
           by simp [update_Fin_gso2 _ _ _ _ hk]⟩

/-- La vista della coppia `(i, j)`: stato delle due cache, righe della directory,
messaggi con token in volo (saturati), e se `i = j`. -/
def miView {n} (s : MIState n) (i j : Fin n) : View :=
  ⟨(s.caches i).state, (s.caches j).state,
   s.parent.shared_state i, s.parent.shared_state j,
   Cnt.ofCount (parentMsgs s.parent i), Cnt.ofCount (parentMsgs s.parent j),
   decide (i = j)⟩

/-- Le due copie di ogni coda (lato parent e lato cache) coincidono: è
`¬ MIState.desynced` di MI.lean. Il parent legge le sue, la cache le sue: la vista
conta dal lato cache, e per il passo del parent serve questo. -/
def synced {n} (s : MIState n) : Prop :=
  ∀ k, s.parent.queue_cip k = (s.caches k).queue_cp ∧ s.parent.queue_pci k = (s.caches k).queue_pc

theorem synced_step {n} {s s' : MIState n} {t} (hs : synced s) (h : mi_step_internal s t s') :
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

/-- **Le viste cattive**: tutte le violazioni dell'invariante "un solo token, registrato
dal parent":
1. due cache distinte entrambe in `M`;
2. due indici distinti con un messaggio con token in volo ciascuno;
3. due messaggi con token in volo per lo stesso indice;
4. un messaggio con token in volo per un indice che il parent crede a `I`;
5. il parent crede `M` due indici distinti. -/
def badView (v : View) : Prop :=
  (v.eq = false ∧ v.c0 = .M ∧ v.c1 = .M)
  ∨ (v.eq = false ∧ v.m0 ≠ .zero ∧ v.m1 ≠ .zero)
  ∨ v.m0 = .many
  ∨ (v.m0 ≠ .zero ∧ v.d0 = .I)
  ∨ (v.eq = false ∧ v.d0 = .M ∧ v.d1 = .M)

def miSetup (n : Nat) : SymSetup (MIState n) (MIInternalEvent n) (Fin n) View where
  trans := mi_step_internal
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step hs h
  view := miView
  bad := badView
  s0 := default
  inv0 := fun _ => ⟨rfl, rfl⟩

/-- I due lemmi "in avanti" che la tattica istanzia su ogni ipotesi `l[j]? = some a`. -/
theorem countP_eraseIdx_grant {l : List PCEvent} {j : Nat} {a : PCEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isGrant + (if isGrant a then 1 else 0) = l.countP isGrant :=
  countP_eraseIdx _ _ _ _ h

theorem countP_eraseIdx_release {l : List CPEvent} {j : Nat} {a : CPEvent} (h : l[j]? = some a) :
    (l.eraseIdx j).countP isRelease + (if isRelease a then 1 else 0) = l.countP isRelease :=
  countP_eraseIdx _ _ _ _ h


end MIView

open MIView

/-- La tattica con i parametri di `MI` già messi. Senza argomento usa `miSetup`
(due cache in `M`); con un argomento, il `SymSetup` dato. -/
syntax "new_backward_tatic" (ppSpace term:max)? : tactic
syntax "new_backward_tatic?" (ppSpace term:max)? : tactic

macro_rules
  | `(tactic| new_backward_tatic) => `(tactic| new_backward_tatic (miSetup _))
  | `(tactic| new_backward_tatic $st) =>
    `(tactic| backward_search_gen $st
      simp [miView, parentMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrant, isRelease, Cnt.ofCount, Cnt.ofCount_eq_zero, Cnt.ofCount_eq_one,
            Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grant, countP_eraseIdx_release]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [mi_step_internal, cache_mi_step_internal, parent_mi_step])

macro_rules
  | `(tactic| new_backward_tatic?) => `(tactic| new_backward_tatic? (miSetup _))
  | `(tactic| new_backward_tatic? $st) =>
    `(tactic| backward_search_gen? $st
      simp [miView, parentMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, List.countP_append, List.countP_cons, List.countP_nil,
            isGrant, isRelease, Cnt.ofCount, Cnt.ofCount_eq_zero, Cnt.ofCount_eq_one,
            Cnt.ofCount_eq_many]
      fwd [countP_eraseIdx_grant, countP_eraseIdx_release]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [mi_step_internal, cache_mi_step_internal, parent_mi_step])


set_option maxHeartbeats 0 in
/-- **Il risultato della tattica**: nessuno stato con una vista cattiva è raggiungibile da
`default` (186 viste di partenza, chiusura di 206, 913 passi). Da qui discendono tutti
gli altri. -/
theorem badView_unreachable_from_default {n} : (miSetup n).Unreachable := by
  new_backward_tatic

theorem mi_init_default {n} : mi_init (default : MIState n) :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

/-- Ogni stato raggiungibile ha le due copie di ogni coda allineate. -/
theorem synced_of_reachable {n} {s : MIState n} (h : MI.reachable s) : synced s := by
  have key : ∀ x, ReflTransGen MI.atrans (default : MIState n) x → synced x := by
    intro x hx
    induction hx with
    | refl => exact fun _ => ⟨rfl, rfl⟩
    | tail _ hstep ih => obtain ⟨t, ht⟩ := hstep; exact synced_step ih ht
  exact key s (h _ mi_init_default)

/-- `MI.reachable s` quantifica su tutti gli stati iniziali; `default` è uno di essi. -/
theorem badView_unreachable {n} (s : MIState n) (h : ∃ i j, badView (miView s i j)) :
    ¬ MI.reachable s :=
  fun hreach => badView_unreachable_from_default s h (hreach (default : MIState n) mi_init_default)

theorem parentMsgs_ne_zero_of_rsIμ {n} {p : ParentState n} {i : Fin n} {k : Nat} {v : Value}
    (h : (p.queue_cip i)[k]? = some (CPEvent.rsIμ v)) : parentMsgs p i ≠ 0 := by
  have : 0 < (p.queue_cip i).countP isRelease :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? h, rfl⟩
  unfold parentMsgs; omega

/-- Due elementi in posizioni diverse che soddisfano `p` danno `countP p ≥ 2`. -/
theorem two_le_countP_of_ne {α} (p : α → Bool) (l : List α) {j₁ j₂ : Nat} {a b : α}
    (h₁ : l[j₁]? = some a) (h₂ : l[j₂]? = some b) (hne : j₁ ≠ j₂)
    (ha : p a = true) (hb : p b = true) : 2 ≤ l.countP p := by
  have hc := countP_eraseIdx p l j₁ a h₁
  rw [ha] at hc; simp only [if_true] at hc
  have hmem : b ∈ l.eraseIdx j₁ := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- j₁ < j₂: dopo aver tolto j₁, b sta in j₂ - 1
      exact List.mem_of_getElem? (l := l.eraseIdx j₁) (i := j₂ - 1)
        (by rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact h₂)
    · -- j₂ < j₁: b resta in j₂
      exact List.mem_of_getElem? (l := l.eraseIdx j₁) (i := j₂)
        (by rw [List.getElem?_eraseIdx_of_lt (by omega)]; exact h₂)
  have : 0 < (l.eraseIdx j₁).countP p := List.countP_pos_iff.mpr ⟨b, hmem, hb⟩
  omega


/-! ### Seconda vista cattiva: la cache tiene la linea senza che il parent lo sappia

Serve per `comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all` (la cache deve essere in `I`
per scartare l'`rqIμ` stantio) e per i due grant (la cache deve essere in `I` per ricevere
l'`rsM`). Non è coperta da `badView`, quindi un secondo `SymSetup` con la stessa vista e la
stessa tattica (120 viste di partenza, chiusura di 159, 699 passi). -/

/-- La cache `0` è in `M` mentre per l'indice `0` c'è un messaggio con token in volo,
oppure il parent la crede a `I`. -/
def badViewHold (v : View) : Prop := v.c0 = .M ∧ (v.m0 ≠ .zero ∨ v.d0 = .I)

def miSetupHold (n : Nat) : SymSetup (MIState n) (MIInternalEvent n) (Fin n) View where
  trans := mi_step_internal
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step hs h
  view := miView
  bad := badViewHold
  s0 := default
  inv0 := fun _ => ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem badViewHold_unreachable_from_default {n} : (miSetupHold n).Unreachable := by
  new_backward_tatic (miSetupHold _)

theorem badViewHold_unreachable {n} (s : MIState n) (h : ∃ i j, badViewHold (miView s i j)) :
    ¬ MI.reachable s :=
  fun hreach => badViewHold_unreachable_from_default s h (hreach (default : MIState n) mi_init_default)

/-- Un `rsIμ` in volo su `i` mentre la cache `i` è ancora in `M`: irraggiungibile. -/
theorem not_reachable_of_M_and_rsIμ {n} {s : MIState n} {i : Fin n} {j : Nat} {v : Value}
    (hj : (s.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v)) (hM : (s.caches i).state = Bstate.M) :
    ¬ MI.reachable s := by
  refine badViewHold_unreachable s ⟨i, i, hM, Or.inl ?_⟩
  show Cnt.ofCount (parentMsgs s.parent i) ≠ .zero
  rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj

/-- La cache `i` è in `M` mentre la directory la dà a `I`: irraggiungibile. -/
theorem not_reachable_of_M_and_dirI {n} {s : MIState n} {i : Fin n}
    (hM : (s.caches i).state = Bstate.M) (hd : s.parent.shared_state i = Bstate.I) :
    ¬ MI.reachable s :=
  badViewHold_unreachable s ⟨i, i, hM, Or.inr hd⟩


/-- Lo stato dopo `downgrade_from_M_rq1 v` all'indice `i`, consumando la posizione `j`. -/
def downgradeSt {n} (s : MIState n) (v : Value) (i : Fin n) (j : Nat) : MIState n :=
  let parent' : ParentState n :=
    ParentState.mk v (update_Fin i Bstate.I s.parent.shared_state)
      (update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip) s.parent.queue_pci
  MIState.mk
    (update_Fin i (CacheState.mk (s.caches i).state (s.caches i).value
      (parent'.queue_cip i) (parent'.queue_pci i) (s.caches i).extqueue) s.caches)
    parent'

theorem downgrade_inv {n} {s s' : MIState n} {v : Value} {i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) ∧ s' = downgradeSt s v i j := by
  cases h
  rename_i hp
  cases hp
  exact ⟨_, ‹_›, rfl⟩

theorem grant_inv {n} {s s' : MIState n} {i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) s') :
    (∃ j : Nat, (s.parent.queue_cip i)[j]? = some CPEvent.rqM) ∧ ∀ k, s.parent.shared_state k = Bstate.I := by
  cases h
  rename_i hp
  cases hp
  exact ⟨⟨_, ‹_›⟩, ‹_›⟩

/-- Lo stato dopo il grant `upgrade_to_M_data_avilable_rq1` all'indice `i`, consumando `j`. -/
def grantSt {n} (s : MIState n) (i : Fin n) (j : Nat) : MIState n :=
  let parent' : ParentState n :=
    { s.parent with
        shared_state := update_Fin i Bstate.M s.parent.shared_state,
        queue_cip := update_Fin i ((s.parent.queue_cip i).eraseIdx j) s.parent.queue_cip,
        queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rsM s.parent.value]) s.parent.queue_pci }
  MIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'

theorem grant_inv_st {n} {s s' : MIState n} {i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) s') :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some CPEvent.rqM
      ∧ (∀ k, s.parent.shared_state k = Bstate.I) ∧ s' = grantSt s i j := by
  cases h; rename_i hp; cases hp; exact ⟨_, ‹_›, ‹_›, rfl⟩

theorem invalidAll_inv {n} {s s' : MIState n} {k i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) s') :
    s.parent.shared_state i = Bstate.M := by
  cases h
  rename_i hp
  cases hp
  rename_i hne
  cases hs : s.parent.shared_state i
  · rfl
  · exact absurd hs hne

/-- Lo stato dopo `upgrade_to_M_invalid_all k` all'indice `i`: un `rqIμ` in coda a `i`. -/
def invalidateSt {n} (s : MIState n) (i : Fin n) : MIState n :=
  let parent' : ParentState n :=
    { s.parent with queue_pci := update_Fin i (s.parent.queue_pci i ++ [PCEvent.rqIμ]) s.parent.queue_pci }
  MIState.mk
    (update_Fin i { s.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i } s.caches)
    parent'

theorem invalidate_inv {n} {s s' : MIState n} {k i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) s') :
    (∃ j : Nat, (s.parent.queue_cip k)[j]? = some CPEvent.rqM)
      ∧ s.parent.shared_state i = Bstate.M ∧ s' = invalidateSt s i := by
  cases h
  rename_i hp
  cases hp
  rename_i hne
  refine ⟨⟨_, ‹_›⟩, ?_, rfl⟩
  cases hs : s.parent.shared_state i
  · rfl
  · exact absurd hs hne


/-- Inversione di `invalid_allM`: directory `i = M`, e lo stato di arrivo è lo stesso
dell'invalidate mirato (`invalidateSt`). -/
theorem invalidAllM_inv {n} {s s' : MIState n} {i : Fin n}
    (h : mi_step_internal s (.parent (.upd_queue .invalid_allM i)) s') :
    s.parent.shared_state i = Bstate.M ∧ s' = invalidateSt s i := by
  cases h
  rename_i hp
  cases hp
  exact ⟨‹_›, rfl⟩


/-! # Commutazione parent–parent

Due passi del parent (`.parent (.upd_queue e i)`) applicati allo stesso stato `s`. Regole:
`downgrade_from_M_rq1 v`, `upgrade_to_M_data_avilable_rq1`, `upgrade_to_M_invalid_all k`,
`invalid_allM`; una coppia per ognuna delle 10 combinazioni non ordinate. Dove il diamante in
un passo è falso l'enunciato cambia senza cambiare significato: l'invalidate viene assorbito
(`s''' = s'`, dopo il downgrade la cache scarta l'`rqIμ` stantio con `downgrade_from_M_rs1`),
i due grant riconvergono in 7 + 7 passi (`grant_grant_reconverge`), oppure si esce con
`s' = s''` (stesso messaggio consumato) o con `¬ MI.reachable s` (vista cattiva). -/


theorem comm_downgrade_from_M_rq1_downgrade_from_M_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂) ) s'' →
  ∃ s''',
    (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s''')
    ∨
    s' = s''
    ∨
    ¬ MI.reachable s := by
  -- Le due premesse forzano una vista cattiva (quindi `¬ MI.reachable s`, da
  -- `badView_unreachable_from_default`, dimostrato con `new_backward_tatic`), tranne
  -- quando sono lo stesso passo: allora i due stati coincidono.
  intro h₁ h₂
  obtain ⟨j₁, hj₁, rfl⟩ := downgrade_inv h₁
  obtain ⟨j₂, hj₂, rfl⟩ := downgrade_inv h₂
  refine ⟨s, ?_⟩
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases hj : j₁ = j₂
    · -- lo stesso passo: stesso `rsIμ`, quindi `v₁ = v₂` e `s' = s''`
      subst hj
      rw [hj₁] at hj₂
      cases hj₂
      exact Or.inr (Or.inl rfl)
    · -- due `rsIμ` nella stessa coda: due token per lo stesso indice (vista cattiva 3)
      refine Or.inr (Or.inr (badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inl ?_))⟩))
      show Cnt.ofCount (parentMsgs s.parent i₁) = .many
      rw [Cnt.ofCount_eq_many]
      have := two_le_countP_of_ne isRelease (s.parent.queue_cip i₁) hj₁ hj₂ hj rfl rfl
      unfold parentMsgs; omega
  · -- due `rsIμ` su indici distinti: due token in volo (vista cattiva 2)
    refine Or.inr (Or.inr (badView_unreachable s ⟨i₁, i₂, Or.inr (Or.inl ⟨decide_eq_false hi, ?_, ?_⟩)⟩))
    · show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
      rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj₁
    · show Cnt.ofCount (parentMsgs s.parent i₂) ≠ .zero
      rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj₂



theorem comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂) ) s'' →
  ∃ s''',
    (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  -- Un `rsIμ` in volo su `i₁` mentre il parent crede `i₁` a `I`: vista cattiva 4.
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgrade_inv h₁
  obtain ⟨_, hall⟩ := grant_inv h₂
  -- un `rsIμ` in volo su `i₁` mentre il parent crede `i₁` a `I` (vista cattiva 4)
  refine ⟨s, Or.inr (Or.inr (badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hall i₁⟩)))⟩))⟩
  show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
  rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj₁

/-- **Downgrade / invalidate mirato commutano "a meno dell'invalidate".** Con `i₁ = i₂` il
downgrade porta la directory di `i₁` a `I`, quindi da `s'` l'invalidate non può più scattare
(guardia `¬ shared_state i₂ = I`): il cammino a destra è vuoto. Da `s''` invece il parent fa il
downgrade e poi la cache (in `I`) scarta l'`rqIμ` stantio con `downgrade_from_M_rs1`, arrivando
esattamente a `s'`. Se la cache fosse in `M` con il suo rilascio in volo, `s` sarebbe
irraggiungibile (`not_reachable_of_M_and_rsIμ`, dalla tattica backward su `miSetupHold`).
Con `i₁ ≠ i₂` `s` è irraggiungibile (viste cattive 4 e 5), come in `…_of_ne`.
Il cammino originale (invalidate fatto da `s'`) è falso su uno stato raggiungibile (`n = 1`:
la cache rilascia e richiede subito la linea, il parent ha in coda `rsIμ` e `rqM`). -/
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂) ) s'' →
  ∃ s''' s1,
    (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s1 ∧
     mi_step_internal s1 (.cache (.downgrade_from_M_rs1) i₁) s''' ∧
     s''' = s')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  obtain ⟨_, hM, rfl⟩ := invalidate_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    cases hc : (s.caches i₁).state with
    | M =>
      -- la cache tiene la linea con un rilascio in volo: irraggiungibile
      exact ⟨s, s, Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hc))⟩
    | I =>
      -- da `s''`: downgrade del parent, poi la cache scarta l'`rqIμ` stantio
      have hj' : ((invalidateSt s i₁).parent.queue_cip i₁)[j]? = some (CPEvent.rsIμ v) := hj
      refine ⟨_, _, Or.inl
        ⟨mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j hj'),
         mi_step_internal.cache _ _ i₁ _
           (cache_mi_step_internal.downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?_ ?_),
         ?_⟩⟩
      · -- l'`rqIμ` è in fondo alla coda della cache
        simp [invalidateSt, update_Fin_gss]
      · -- la cache è in `I`
        simp [invalidateSt, update_Fin_gss, hc]
      · -- lo stato finale è proprio `s'`
        simp only [downgradeSt, invalidateSt]
        congr 1
        · funext q
          by_cases hq : q = i₁
          · subst hq; simp [update_Fin_gss, lst_erase, hc]
          · simp [update_Fin_gso2 _ _ _ _ hq]
        · congr 1
          · simp [update_Fin_gss, update_Fin_update_Fin_same]
          · simp [update_Fin_gss, lst_erase, update_Fin_update_Fin_same, update_Fin_self]
  · -- `i₁ ≠ i₂`: come in `…_of_ne`
    refine ⟨s, s, Or.inr (Or.inr ?_)⟩
    cases hd : s.parent.shared_state i₁ with
    | I =>
      -- rilascio in volo su `i₁` ma directory `i₁ = I` (vista cattiva 4)
      refine badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hd⟩)))⟩
      show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
      rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj
    | M =>
      -- directory `M` su due indici distinti (vista cattiva 5)
      exact badView_unreachable s ⟨i₁, i₂, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false hne, hd, hM⟩)))⟩

/-- Variante a due passi di `comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all` per `i₁ ≠ i₂`:
il rilascio in volo su `i₁` vale directory `i₁ = M` (altrimenti vista cattiva 4), e con
`i₂ = M` il parent registrerebbe due proprietari (vista cattiva 5). -/
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all_of_ne {n} {s s' s'' : MIState n}
    {v : Value} {k i₁ i₂ : Fin n} (hne : i₁ ≠ i₂) :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂) ) s'' →
  ∃ s''',
    (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, _⟩ := downgrade_inv h₁
  have hM := invalidAll_inv h₂
  refine ⟨s, Or.inr (Or.inr ?_)⟩
  cases hd : s.parent.shared_state i₁ with
  | I =>
    -- rilascio in volo su `i₁` ma directory `i₁ = I` (vista cattiva 4)
    refine badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hd⟩)))⟩
    show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
    rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj₁
  | M =>
    -- directory `M` su due indici distinti (vista cattiva 5)
    exact badView_unreachable s ⟨i₁, i₂, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false hne, hd, hM⟩)))⟩




/-- Con `i₁ = i₂` l'`invalid_allM` non può più scattare da `s'` (la directory di `i₁` è a `I`
dopo il downgrade): il cammino a destra è vuoto. Da `s''` il parent fa il downgrade e la cache
(in `I`) scarta l'`rqIμ` stantio con `downgrade_from_M_rs1`, arrivando esattamente a `s'`.
Cache in `M` con il suo rilascio in volo: irraggiungibile (`not_reachable_of_M_and_rsIμ`).
Con `i₁ ≠ i₂` `s` è irraggiungibile (viste cattive 4 e 5). -/
theorem comm_downgrade_from_M_rq1_invalid_all {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.invalid_allM) i₂) ) s'' →
  ∃ s''' s1,
   (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s1 ∧
    mi_step_internal s1 (.cache (.downgrade_from_M_rs1) i₁) s''' ∧
    s''' = s')
  ∨
    s' = s''
  ∨
  ¬ MI.reachable s := by
  intro h₁ h₂
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    cases hc : (s.caches i₁).state with
    | M =>
      -- la cache tiene la linea con un rilascio in volo: irraggiungibile
      exact ⟨s, s, Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hc))⟩
    | I =>
      -- da `s''`: downgrade del parent, poi la cache scarta l'`rqIμ` stantio
      have hj' : ((invalidateSt s i₁).parent.queue_cip i₁)[j]? = some (CPEvent.rsIμ v) := hj
      refine ⟨_, _, Or.inl
        ⟨mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j hj'),
         mi_step_internal.cache _ _ i₁ _
           (cache_mi_step_internal.downgrade_from_M_rs1 _ (s.parent.queue_pci i₁).length ?_ ?_),
         ?_⟩⟩
      · -- l'`rqIμ` è in fondo alla coda della cache
        simp [invalidateSt, update_Fin_gss]
      · -- la cache è in `I`
        simp [invalidateSt, update_Fin_gss, hc]
      · -- lo stato finale è proprio `s'`
        simp only [downgradeSt, invalidateSt]
        congr 1
        · funext q
          by_cases hq : q = i₁
          · subst hq; simp [update_Fin_gss, lst_erase, hc]
          · simp [update_Fin_gso2 _ _ _ _ hq]
        · congr 1
          · simp [update_Fin_gss, update_Fin_update_Fin_same]
          · simp [update_Fin_gss, lst_erase, update_Fin_update_Fin_same, update_Fin_self]
  · -- `i₁ ≠ i₂`: come in `…_of_ne`
    refine ⟨s, s, Or.inr (Or.inr ?_)⟩
    cases hd : s.parent.shared_state i₁ with
    | I =>
      -- rilascio in volo su `i₁` ma directory `i₁ = I` (vista cattiva 4)
      refine badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hd⟩)))⟩
      show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
      rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hj
    | M =>
      -- directory `M` su due indici distinti (vista cattiva 5)
      exact badView_unreachable s ⟨i₁, i₂, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false hne, hd, hM⟩)))⟩


/-- La riconvergenza dei due grant a indici distinti: da ciascuno dei due stati la cache servita
prende la linea, la rilascia, il parent registra il rilascio e poi serve l'altra richiesta allo
stesso modo. I due cammini (7 passi ciascuno) finiscono nello stesso stato. -/
theorem grant_grant_reconverge {n} {s : MIState n} {i₁ i₂ : Fin n} {j₁ j₂ : Nat} (hne : i₁ ≠ i₂)
    (hj₁ : (s.parent.queue_cip i₁)[j₁]? = some CPEvent.rqM)
    (hj₂ : (s.parent.queue_cip i₂)[j₂]? = some CPEvent.rqM)
    (hall : ∀ k, s.parent.shared_state k = Bstate.I)
    (hI₁ : (s.caches i₁).state = Bstate.I) (hI₂ : (s.caches i₂).state = Bstate.I) :
    ∃ s''' t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆,
      mi_step_internal (grantSt s i₁ j₁) (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
      mi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
      mi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
      mi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
      mi_step_internal t₄ (.cache (.upgrade_from_I_rs s.parent.value) i₂) t₅ ∧
      mi_step_internal t₅ (.cache .rq_data_not_available i₂) t₆ ∧
      mi_step_internal t₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) s''' ∧
      mi_step_internal (grantSt s i₂ j₂) (.cache (.upgrade_from_I_rs s.parent.value) i₂) u₁ ∧
      mi_step_internal u₁ (.cache .rq_data_not_available i₂) u₂ ∧
      mi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) u₃ ∧
      mi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
      mi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
      mi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
      mi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''' := by
  have hne' : i₂ ≠ i₁ := Ne.symm hne
  -- i due cammini: la cache prende la linea, la rilascia, il parent la registra; poi l'altra
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
    mi_step_internal.cache _ _ i₁ _
      (cache_mi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?l1 ?l2),
    mi_step_internal.cache _ _ i₁ _ (cache_mi_step_internal.rq_data_not_available _ ?l3),
    mi_step_internal.parent_upd_queue _ _ _ i₁
      (parent_mi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?l4),
    mi_step_internal.parent_upd_queue _ _ _ i₂
      (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₂ j₂ ?l5 ?l6),
    mi_step_internal.cache _ _ i₂ _
      (cache_mi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₂).length ?l7 ?l8),
    mi_step_internal.cache _ _ i₂ _ (cache_mi_step_internal.rq_data_not_available _ ?l9),
    mi_step_internal.parent_upd_queue _ _ _ i₂
      (parent_mi_step.downgrade_from_M_rq1 _ _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?l10),
    mi_step_internal.cache _ _ i₂ _
      (cache_mi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₂).length ?r1 ?r2),
    mi_step_internal.cache _ _ i₂ _ (cache_mi_step_internal.rq_data_not_available _ ?r3),
    mi_step_internal.parent_upd_queue _ _ _ i₂
      (parent_mi_step.downgrade_from_M_rq1 _ _ i₂ ((s.parent.queue_cip i₂).eraseIdx j₂).length ?r4),
    mi_step_internal.parent_upd_queue _ _ _ i₁
      (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j₁ ?r5 ?r6),
    mi_step_internal.cache _ _ i₁ _
      (cache_mi_step_internal.upgrade_from_I_rs _ _ (s.parent.queue_pci i₁).length ?r7 ?r8),
    mi_step_internal.cache _ _ i₁ _ (cache_mi_step_internal.rq_data_not_available _ ?r9),
    mi_step_congr (mi_step_internal.parent_upd_queue _ _ _ i₁
      (parent_mi_step.downgrade_from_M_rq1 _ _ i₁ ((s.parent.queue_cip i₁).eraseIdx j₁).length ?r10))
      ?eq⟩
  -- cammino sinistro
  case l1 => simp only [grantSt, update_Fin_gss]; exact lst_get _ _
  case l2 => simp only [grantSt, update_Fin_gss]; exact hI₁
  case l3 => simp only [grantSt, update_Fin_gss]
  case l4 => simp only [grantSt, update_Fin_gss]; exact lst_get _ _
  case l5 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hj₂
  case l6 =>
    intro k
    by_cases hk : k = i₁
    · subst hk; simp only [grantSt, update_Fin_gss]
    · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
  case l7 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
  case l8 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact hI₂
  case l9 => simp only [grantSt, update_Fin_gss]
  case l10 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']; exact lst_get _ _
  -- cammino destro
  case r1 => simp only [grantSt, update_Fin_gss]; exact lst_get _ _
  case r2 => simp only [grantSt, update_Fin_gss]; exact hI₂
  case r3 => simp only [grantSt, update_Fin_gss]
  case r4 => simp only [grantSt, update_Fin_gss]; exact lst_get _ _
  case r5 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hj₁
  case r6 =>
    intro k
    by_cases hk : k = i₂
    · subst hk; simp only [grantSt, update_Fin_gss]
    · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk]; exact hall k
  case r7 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
  case r8 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact hI₁
  case r9 => simp only [grantSt, update_Fin_gss]
  case r10 => simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]; exact lst_get _ _
  -- i due stati finali coincidono, campo per campo
  case eq =>
    refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
    · intro k
      by_cases hk₁ : k = i₁
      · subst hk₁
        simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
          update_Fin_gso2 _ _ _ _ hne', lst_erase]
      · by_cases hk₂ : k = i₂
        · subst hk₂
          simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
    · exact rfl
    · intro k
      by_cases hk₁ : k = i₁
      · subst hk₁
        simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
      · by_cases hk₂ : k = i₂
        · subst hk₂
          simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
        · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
    · intro k
      by_cases hk₁ : k = i₁
      · subst hk₁
        simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
          update_Fin_gso2 _ _ _ _ hne', lst_erase]
      · by_cases hk₂ : k = i₂
        · subst hk₂
          simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
    · intro k
      by_cases hk₁ : k = i₁
      · subst hk₁
        simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
          update_Fin_gso2 _ _ _ _ hne', lst_erase]
      · by_cases hk₂ : k = i₂
        · subst hk₂
          simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
            update_Fin_gso2 _ _ _ _ hne', lst_erase]
        · simp only [grantSt, update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]

/-- Due grant non commutano mai: la guardia `∀ i, shared_state i = I` è distrutta dal grant
stesso (mutua esclusione del protocollo). La riconvergenza è servire le due richieste una
dopo l'altra: la cache riceve l'`rsM`, rilascia la linea, il parent consuma il rilascio, e poi
tocca all'altra (7 passi per lato, `grant_grant_reconverge`). Con `i₁ = i₂`: stessa posizione
dà `s' = s''`; posizioni diverse danno o un `rsIμ` in coda (vista cattiva 4: directory tutta
a `I`) o una coda di soli `rqM`, e allora `s' = s''`. Con `i₁ ≠ i₂` le due cache devono essere
in `I`, altrimenti `s` è irraggiungibile (`not_reachable_of_M_and_dirI`). -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂) ) s'' →
  ∃ s''',
    (∃ t₁ t₂ t₃ t₄ t₅ t₆ u₁ u₂ u₃ u₄ u₅ u₆,
      mi_step_internal s'  (.cache (.upgrade_from_I_rs s.parent.value) i₁) t₁ ∧
      mi_step_internal t₁ (.cache .rq_data_not_available i₁) t₂ ∧
      mi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) t₃ ∧
      mi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₂)) t₄ ∧
      mi_step_internal t₄ (.cache (.upgrade_from_I_rs s.parent.value) i₂) t₅ ∧
      mi_step_internal t₅ (.cache .rq_data_not_available i₂) t₆ ∧
      mi_step_internal t₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) s''' ∧
      mi_step_internal s'' (.cache (.upgrade_from_I_rs s.parent.value) i₂) u₁ ∧
      mi_step_internal u₁ (.cache .rq_data_not_available i₂) u₂ ∧
      mi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₂)) u₃ ∧
      mi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) u₄ ∧
      mi_step_internal u₄ (.cache (.upgrade_from_I_rs s.parent.value) i₁) u₅ ∧
      mi_step_internal u₅ (.cache .rq_data_not_available i₁) u₆ ∧
      mi_step_internal u₆ (.parent (.upd_queue (.downgrade_from_M_rq1 s.parent.value) i₁)) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  obtain ⟨j₁, hj₁, hall, rfl⟩ := grant_inv_st h₁
  obtain ⟨j₂, hj₂, -, rfl⟩ := grant_inv_st h₂
  by_cases hne : i₁ = i₂
  · -- stesso indice
    subst hne
    by_cases hj : j₁ = j₂
    · subst hj; exact ⟨s, Or.inr (Or.inl rfl)⟩
    · by_cases hall_rq : ∀ x ∈ s.parent.queue_cip i₁, x = CPEvent.rqM
      · -- coda di soli `rqM`: cancellare `j₁` o `j₂` dà la stessa coda
        have hlen₁ : j₁ < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj₁).1
        have hlen₂ : j₂ < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj₂).1
        have he := eraseIdx_eq_of_all_eq _ _ j₁ j₂ hall_rq hlen₁ hlen₂
        refine ⟨s, Or.inr (Or.inl ?_)⟩
        simp only [grantSt, he]
      · -- un `rsIμ` in coda con directory `i₁ = I` (vista cattiva 4)
        obtain ⟨x, hx⟩ := not_forall.mp hall_rq
        obtain ⟨hx, hxne⟩ := Classical.not_imp.mp hx
        cases x with
        | rqM => exact absurd rfl hxne
        | rsIμ v =>
          obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
          refine ⟨s, Or.inr (Or.inr
            (badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hall i₁⟩)))⟩))⟩
          show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
          rw [Ne, Cnt.ofCount_eq_zero]; exact parentMsgs_ne_zero_of_rsIμ hk
  · -- indici distinti: entrambe le cache in `I`, altrimenti irraggiungibile
    cases hI₁ : (s.caches i₁).state with
    | M => exact ⟨s, Or.inr (Or.inr (not_reachable_of_M_and_dirI hI₁ (hall i₁)))⟩
    | I =>
      cases hI₂ : (s.caches i₂).state with
      | M => exact ⟨s, Or.inr (Or.inr (not_reachable_of_M_and_dirI hI₂ (hall i₂)))⟩
      | I =>
        obtain ⟨s''', t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, h⟩ :=
          grant_grant_reconverge hne hj₁ hj₂ hall hI₁ hI₂
        exact ⟨s''', Or.inl ⟨t₁, t₂, t₃, t₄, t₅, t₆, u₁, u₂, u₃, u₄, u₅, u₆, h⟩⟩

theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_invalid_all {s s' s''} :
  parent_mi_step s (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) s' →
  parent_mi_step s (.upd_queue (.upgrade_to_M_invalid_all k) i₂) s'' →
  ∃ s''',
    parent_mi_step s'' (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) s''' ∧
    parent_mi_step s' (.upd_queue (.upgrade_to_M_invalid_all k) i₂) s''' := by
  intro h1 h2
  cases h1 ; cases h2
  exact absurd (‹∀ i, s.shared_state i = Bstate.I› i₂) ‹¬(s.shared_state i₂ = Bstate.I)›

theorem comm_upgrade_to_M_data_avilable_rq1_invalid_all {s s' s''} :
  parent_mi_step s (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) s' →
  parent_mi_step s (.upd_queue (.invalid_allM) i₂) s'' →
  ∃ s''',
    parent_mi_step s'' (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) s''' ∧
    parent_mi_step s' (.upd_queue (.invalid_allM) i₂) s''' := by
  intro h1 h2
  cases h1 ; cases h2
  cases (‹∀ i, s.shared_state i = Bstate.I› i₂).symm.trans ‹s.shared_state i₂ = Bstate.M›

theorem comm_upgrade_to_M_invalid_all_upgrade_to_M_invalid_all {s s' s''} :
  parent_mi_step s (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁) s' →
  parent_mi_step s (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂) s'' →
  ∃ s''',
    parent_mi_step s'' (.upd_queue (.upgrade_to_M_invalid_all k₁) i₁) s''' ∧
    parent_mi_step s' (.upd_queue (.upgrade_to_M_invalid_all k₂) i₂) s''' := by
  intro h1 h2
  cases h1 ; cases h2
  refine ⟨_, .upgrade_to_M_invalid_all _ _ _ _ (by assumption) (by assumption),
             parent_mi_step_congr
               (.upgrade_to_M_invalid_all _ _ _ _ (by assumption) (by assumption)) ?_⟩
  congr 1
  exact update_Fin_append_comm _ _ _ _

theorem comm_upgrade_to_M_invalid_all_invalid_all {s s' s''} :
  parent_mi_step s (.upd_queue (.upgrade_to_M_invalid_all k) i₁) s' →
  parent_mi_step s (.upd_queue (.invalid_allM) i₂) s'' →
  ∃ s''',
    parent_mi_step s'' (.upd_queue (.upgrade_to_M_invalid_all k) i₁) s''' ∧
    parent_mi_step s' (.upd_queue (.invalid_allM) i₂) s''' := by
  intro h1 h2
  cases h1 ; cases h2
  refine ⟨_, .upgrade_to_M_invalid_all _ _ _ _ (by assumption) (by assumption),
             parent_mi_step_congr (.invalid_all _ _ (by assumption)) ?_⟩
  congr 1
  exact update_Fin_append_comm _ _ _ _

theorem comm_invalid_all_invalid_all {s s' s''} :
  parent_mi_step s (.upd_queue (.invalid_allM) i₁) s' →
  parent_mi_step s (.upd_queue (.invalid_allM) i₂) s'' →
  ∃ s''',
    parent_mi_step s'' (.upd_queue (.invalid_allM) i₁) s''' ∧
    parent_mi_step s' (.upd_queue (.invalid_allM) i₂) s''' := by
  intro h1 h2
  cases h1 ; cases h2
  refine ⟨_, .invalid_all _ _ (by assumption),
             parent_mi_step_congr (.invalid_all _ _ (by assumption)) ?_⟩
  congr 1
  exact update_Fin_append_comm _ _ _ _


/-! # Commutazione cache–cache

Due passi interni della stessa cache (`cache_mi_step_internal`) applicati allo stesso stato.
Regole: `ld_rq_data_available`, `st_rq_M_state`, `rq_data_not_available`, `upgrade_from_I_rq`,
`upgrade_from_I_rs v`, `downgrade_from_M_rs`, `downgrade_from_M_rs1`; una coppia per ognuna
delle 28 combinazioni non ordinate. Le coppie con guardie incompatibili (`M` contro `I`) sono
vuote. Quando la cache ha ceduto la linea e la vuole di nuovo il teorema sale a `MIState` e
riconverge con il percorso richiesta → downgrade del parent → grant → presa → servizio;
altrimenti `s' = s''` (stesso messaggio consumato) o `¬ MI.reachable s`. -/



theorem comm_ld_rq_data_available_ld_rq_data_available {s s' s''} :
  cache_mi_step_internal s (.ld_rs v₁) s' →
  cache_mi_step_internal s (.ld_rs v₂) s'' →
  s' = s'' := by
  intro h1 h2
  cases h1; cases h2; grind


theorem comm_ld_rq_data_available_st_rq_M_state {s s' s''} :
  cache_mi_step_internal s (.ld_rs v₁) s' →
  cache_mi_step_internal s (.st_rs v₂) s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.ld_rs v₁) s''' ∧
    cache_mi_step_internal s' (.st_rs v₂) s''' :=  by
    intro h1 h2;
    cases h1 ; cases h2;
    grind




/-- Dopo il rilascio spontaneo (`rsIμ`) la load aspetta che la linea venga riacquisita:
richiesta `rqM`, il parent registra il rilascio (`value := v`, riga `i` a `I`), concede
(serve tutta la directory a `I`: le altre righe lo sono, oppure `s` è irraggiungibile),
la cache prende `M` con `v` e serve la load. Si confrontano solo le cache. -/
theorem comm_ld_rq_data_available_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.rq_data_not_available) i) s' →
  mi_step_internal s (.cache (.ld_rs v) i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅,
    mi_step_internal s' (.cache (.upgrade_from_I_rq) i) t₁ ∧
    mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)) t₃ ∧
    mi_step_internal t₃ (.cache (.upgrade_from_I_rs v) i) t₄ ∧
    mi_step_internal t₄ (.cache (.ld_rs v) i) t₅ ∧
    s''.caches = t₅.caches)
  ∨
    ¬ MI.reachable s := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available hM =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | ld_rq_data_available rst hrq _ =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · -- tutte le altre righe della directory sono a `I`: il cammino esplicito
            left
            refine ⟨_, _, _, _, _,
              mi_step_internal.cache _ ?c1 _ _ ?p1,
              mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
              mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
              mi_step_internal.cache _ ?c2 _ _ ?p4,
              mi_step_internal.cache _ ?c3 _ _ ?p5,
              ?eq⟩
            -- 1. la cache (ora in `I`) torna a chiedere la linea (rqM)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- 2. il parent consuma l'rsIμ: shared_state i := I, value := v
            case p2 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- 3. il parent consuma l'rqM e risponde con rsM v (directory tutta a `I`)
            case p3 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 4. la cache prende la linea con il valore v
            case p4 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ (s.caches i).queue_pc.length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- 5. ora la load può essere servita
            case p5 =>
              simp only [update_Fin_gss, lst_erase]
              refine .ld_rq_data_available _ rst ?_ ?_
              · assumption
              · rfl
            -- le cache coincidono
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- una riga `k ≠ i` è a `M` mentre la cache `i` è in `M`: `s` è irraggiungibile
            right
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hkM' : s.parent.shared_state k = Bstate.M := by
              cases h : s.parent.shared_state k
              · rfl
              · exact absurd h hkM
            cases hdi : s.parent.shared_state i with
            | I => exact not_reachable_of_M_and_dirI hM hdi
            | M =>
              exact badView_unreachable s
                ⟨i, k, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false (Ne.symm hki), hdi, hkM'⟩)))⟩

theorem comm_ld_rq_data_available_upgrade_from_I_rq {s s' s''} :
  cache_mi_step_internal s (.ld_rs v) s' →
  cache_mi_step_internal s .upgrade_from_I_rq s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.ld_rs v) s''' ∧
    cache_mi_step_internal s' .upgrade_from_I_rq s''' := by
  intro h1 h2; cases h1; cases h2; grind

theorem comm_ld_rq_data_available_upgrade_from_I_rs {s s' s''} :
  cache_mi_step_internal s (.ld_rs v₁) s' →
  cache_mi_step_internal s (.upgrade_from_I_rs v₂) s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.ld_rs v₁) s''' ∧
    cache_mi_step_internal s' (.upgrade_from_I_rs v₂) s''' := by
  intro h1 h2; cases h1; cases h2; grind

/-- **Load / invalidate commutano "a meno di un giro di linea".** Da `s''` (rilasciato `rsIμ v`,
`v = (s.caches i).value`) la cache richiede, il parent registra e riconcede, la cache riprende e serve
la load; da `s'` la cache rilascia allo stesso `j` e fa gli stessi quattro passi: stesso `t₅`. La
concessione vuole la directory tutta a `I`: le altre righe lo sono, oppure `s` è irraggiungibile. -/
theorem comm_ld_rq_data_available_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.ld_rs v) i) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄,
    mi_step_internal s'' (.cache .upgrade_from_I_rq i) t₁ ∧
    mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t₃ ∧
    mi_step_internal t₃ (.cache (.upgrade_from_I_rs v) i) t₄ ∧
    mi_step_internal t₄ (.cache (.ld_rs v) i) t₅ ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i) u₁ ∧
    mi_step_internal u₁ (.cache .upgrade_from_I_rq i) u₂ ∧
    mi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) u₃ ∧
    mi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) u₄ ∧
    mi_step_internal u₄ (.cache (.upgrade_from_I_rs v) i) t₅)
  ∨
    ¬ MI.reachable s := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | ld_rq_data_available rst hrq hM =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs j hj _ =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · left
            refine ⟨_, _, _, _, _, _, _, _, _,
              mi_step_internal.cache _ ?c1 _ _ ?p1,
              mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
              mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
              mi_step_internal.cache _ ?c2 _ _ ?p4,
              mi_step_internal.cache _ ?c3 _ _ ?p5,
              mi_step_internal.cache _ ?c4 _ _ ?p6,
              mi_step_internal.cache _ ?c5 _ _ ?p7,
              mi_step_internal.parent_upd_queue _ ?q3 _ _ ?p8,
              mi_step_internal.parent_upd_queue _ ?q4 _ _ ?p9,
              mi_step_congr (mi_step_internal.cache _ ?c6 _ _ ?p10) ?eq⟩
            -- sinistra 1. la cache (in I) richiede la linea (rqM)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- sinistra 2. il parent consuma l'rsIμ: shared_state i := I, value := v
            case p2 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- sinistra 3. il parent consuma l'rqM e concede la linea (rsM v)
            case p3 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- sinistra 4. la cache prende la linea con v
            case p4 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- sinistra 5. ora la load può essere servita
            case p5 =>
              simp only [update_Fin_gss, lst_erase]
              refine .ld_rq_data_available _ rst ?_ ?_
              · assumption
              · rfl
            -- destra 1. la cache rilascia la linea allo stesso j (rsIμ v)
            case p6 =>
              simp only [update_Fin_gss]
              refine .downgrade_from_M_rs _ j ?_ ?_
              · exact hj
              · exact hM
            -- destra 2. la cache richiede la linea (rqM)
            case p7 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- destra 3. il parent consuma l'rsIμ
            case p8 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- destra 4. il parent concede la linea
            case p9 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- destra 5. la cache riprende la linea: stesso stato del cammino sinistro
            case p10 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- i due stati finali coincidono, campo per campo
            case eq =>
              refine MIState.ext_all ?_ rfl ?_ ?_ ?_
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
                · simp only [update_Fin_gso2 _ _ _ _ hk]
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss, lst_erase, lst_erase2]
                · simp only [update_Fin_gso2 _ _ _ _ hk]
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss, lst_erase]
                · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- un'altra riga della directory è a M: `s` è irraggiungibile
            right
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hkM' : s.parent.shared_state k = Bstate.M := by
              cases h : s.parent.shared_state k with
              | M => rfl
              | I => exact absurd h hkM
            cases hdi : s.parent.shared_state i with
            | I => exact not_reachable_of_M_and_dirI hM hdi
            | M =>
              exact badView_unreachable s
                ⟨i, k, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false (Ne.symm hki), hdi, hkM'⟩)))⟩

/-- Coppia vuota: la load servita richiede `state = M`, lo scarto dello stantio
`downgrade_from_M_rs1` richiede `state = I`; le due guardie sono incompatibili. -/
theorem comm_ld_rq_data_available_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s (.ld_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.ld_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

theorem comm_st_rq_M_state_st_rq_M_state {s s' s''} :
  cache_mi_step_internal s (.st_rs v₁) s' →
  cache_mi_step_internal s (.st_rs v₂) s'' →
  s' = s'' := by
  intro h1 h2; cases h1; cases h2; grind

/-- Store e rilascio spontaneo: il rilascio porta il valore VECCHIO `(s.caches i).value`;
dallo stato rilasciato la cache richiede la linea, il parent registra il rilascio (righe
tutte a `I`, altrimenti `s` è irraggiungibile) e riconcede, la cache riprende `M` con il
valore vecchio e infine serve la store: solo le cache coincidono con lo store diretto. -/
theorem comm_st_rq_M_state_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.st_rs v) i) s' →
  mi_step_internal s (.cache .rq_data_not_available i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅,
    mi_step_internal s'' (.cache .upgrade_from_I_rq i) t₁ ∧
    mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 (s.caches i).value) i)) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t₃ ∧
    mi_step_internal t₃ (.cache (.upgrade_from_I_rs (s.caches i).value) i) t₄ ∧
    mi_step_internal t₄ (.cache (.st_rs v) i) t₅ ∧
    s'.caches = t₅.caches)
  ∨
    ¬ MI.reachable s := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | st_rq_M_state _ rst hrq hM =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | rq_data_not_available _ =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · left
            refine ⟨_, _, _, _, _,
              mi_step_internal.cache _ ?c1 _ _ ?p1,
              mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
              mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
              mi_step_internal.cache _ ?c2 _ _ ?p4,
              mi_step_internal.cache _ ?c3 _ _ ?p5,
              ?eq⟩
            -- 1. la cache (ora in I) richiede di nuovo la linea (rqM)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- 2. il parent consuma l'rsIμ: shared_state i := I, value := valore vecchio
            case p2 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- 3. il parent consuma l'rqM e risponde con rsM (valore vecchio)
            case p3 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 4. la cache riceve l'rsM e torna in M con il valore vecchio
            case p4 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ (s.caches i).queue_pc.length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- 5. ora la store può essere servita: value := v
            case p5 =>
              simp only [update_Fin_gss, lst_erase]
              refine .st_rq_M_state _ _ rst ?_ ?_
              · exact hrq
              · rfl
            -- le cache coincidono: in i entrambe ⟨M, v, cp, pc, ⟨rs, rst⟩⟩, altrove s.caches k
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- fuga: una riga k ≠ i della directory è a M
            right
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hkM' : s.parent.shared_state k = Bstate.M := by
              cases h : s.parent.shared_state k <;> simp_all
            cases hdi : s.parent.shared_state i with
            | I => exact not_reachable_of_M_and_dirI hM hdi
            | M => exact badView_unreachable s ⟨i, k, Or.inr (Or.inr (Or.inr (Or.inr
                     ⟨decide_eq_false (Ne.symm hki), hdi, hkM'⟩)))⟩

theorem comm_st_rq_M_state_upgrade_from_I_rq {s s' s''} :
  cache_mi_step_internal s (.st_rs v) s' →
  cache_mi_step_internal s .upgrade_from_I_rq s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.st_rs v) s''' ∧
    cache_mi_step_internal s' .upgrade_from_I_rq s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

theorem comm_st_rq_M_state_upgrade_from_I_rs {s s' s''} :
  cache_mi_step_internal s (.st_rs v₁) s' →
  cache_mi_step_internal s (.upgrade_from_I_rs v₂) s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.st_rs v₁) s''' ∧
    cache_mi_step_internal s' (.upgrade_from_I_rs v₂) s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

/-- Store e rilascio spontaneo (`downgrade_from_M_rs`) non commutano direttamente: dopo il
rilascio la store aspetta che la linea torni. A sinistra la cache rilascia il valore vecchio,
richiede, il parent registra e concede, la cache riprende `M` e serve la store; a destra la
cache serve la store e poi rilascia `v` (stessa posizione `j`), e rifà gli stessi quattro passi.
Le cache coincidono (i parent no: `value` vecchio contro `v`). La concessione richiede tutte le
righe della directory a `I`: quelle diverse da `i` lo sono, oppure `s` è irraggiungibile. -/
theorem comm_st_rq_M_state_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.st_rs v) i) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄ u₅,
    mi_step_internal s'' (.cache .upgrade_from_I_rq i) t₁ ∧
    mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 (s.caches i).value) i)) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t₃ ∧
    mi_step_internal t₃ (.cache (.upgrade_from_I_rs (s.caches i).value) i) t₄ ∧
    mi_step_internal t₄ (.cache (.st_rs v) i) t₅ ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i) u₁ ∧
    mi_step_internal u₁ (.cache .upgrade_from_I_rq i) u₂ ∧
    mi_step_internal u₂ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) u₃ ∧
    mi_step_internal u₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) u₄ ∧
    mi_step_internal u₄ (.cache (.upgrade_from_I_rs v) i) u₅ ∧
    t₅.caches = u₅.caches)
  ∨
    ¬ MI.reachable s := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | st_rq_M_state _ rst hrq hM =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | downgrade_from_M_rs j hj _ =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · left
            refine ⟨_, _, _, _, _, _, _, _, _, _,
              mi_step_internal.cache _ ?c1 _ _ ?p1,
              mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
              mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
              mi_step_internal.cache _ ?c2 _ _ ?p4,
              mi_step_internal.cache _ ?c3 _ _ ?p5,
              mi_step_internal.cache _ ?c4 _ _ ?r1,
              mi_step_internal.cache _ ?c5 _ _ ?r2,
              mi_step_internal.parent_upd_queue _ ?q3 _ _ ?r3,
              mi_step_internal.parent_upd_queue _ ?q4 _ _ ?r4,
              mi_step_internal.cache _ ?c6 _ _ ?r5,
              ?eq⟩
            -- 1. (sinistra) la cache, ora in `I`, richiede la linea (rqM)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- 2. il parent consuma l'rsIμ col valore vecchio: shared_state i := I
            case p2 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- 3. il parent consuma l'rqM e concede (rsM col valore vecchio)
            case p3 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 4. la cache riprende `M` col valore vecchio
            case p4 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- 5. ora la store può essere servita
            case p5 =>
              simp only [update_Fin_gss]
              refine .st_rq_M_state _ _ rst ?_ ?_
              · exact hrq
              · rfl
            -- 1. (destra) dopo la store la cache rilascia `v` alla stessa posizione `j`
            case r1 =>
              simp only [update_Fin_gss]
              refine .downgrade_from_M_rs _ j ?_ ?_
              · exact hj
              · exact hM
            -- 2. la cache richiede la linea (rqM)
            case r2 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rq _ ?_
              rfl
            -- 3. il parent consuma l'rsIμ v: value := v, shared_state i := I
            case r3 =>
              refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
              simp only [update_Fin_gss]
              exact lst_get2 _ _ _
            -- 4. il parent consuma l'rqM e concede (rsM v)
            case r4 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase2]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 5. la cache riprende `M` con `v`
            case r5 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- le cache coincidono: `⟨M, v, cp, pc.eraseIdx j, ⟨rs, rst⟩⟩` in `i`, invariate altrove
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase, lst_erase2]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · -- una riga della directory diversa da `i` è a `M`: `s` è irraggiungibile
            right
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hkM' : s.parent.shared_state k = Bstate.M := by
              cases h : s.parent.shared_state k
              · rfl
              · exact absurd h hkM
            cases hdi : s.parent.shared_state i with
            | I => exact not_reachable_of_M_and_dirI hM hdi
            | M =>
              exact badView_unreachable s
                ⟨i, k, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false (Ne.symm hki), hdi, hkM'⟩)))⟩

/-- Coppia vuota: la store servita richiede `state = M`, lo scarto dello stantio
`downgrade_from_M_rs1` richiede `state = I`. -/
theorem comm_st_rq_M_state_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s (.st_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.st_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

theorem comm_rq_data_not_available_rq_data_not_available {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s .rq_data_not_available s'' →
  s' = s'' := by
  intro h1 h2; cases h1; cases h2; grind


theorem comm_rq_data_not_available_upgrade_from_I_rq {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s .upgrade_from_I_rq s'' →
  ∃ s''',
    cache_mi_step_internal s'' .rq_data_not_available s''' ∧
    cache_mi_step_internal s' .upgrade_from_I_rq s''' := by
  intro hs hs';
  cases hs ; cases hs' ; grind

theorem comm_rq_data_not_available_upgrade_from_I_rs {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s (.upgrade_from_I_rs v) s'' →
  ∃ s''',
    cache_mi_step_internal s'' .rq_data_not_available s''' ∧
    cache_mi_step_internal s' (.upgrade_from_I_rs v) s''' := by
  intro h₁ h₂; cases h₁; cases h₂;
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›


/-- Entrambe le azioni portano la cache in `I` accodando `rsIμ value`; il rilascio
spontaneo lascia però l'`rqIμ` in `queue_pc`, che la cache (ormai in `I`) scarta con
`downgrade_from_M_rs1` nella stessa posizione `j`, atterrando esattamente su `s''`.
Dall'altro lato non c'è nulla da fare. -/
theorem comm_rq_data_not_available_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' ∧
    s''' = s'' := by
  intro h₁ h₂
  cases h₁ with
  | rq_data_not_available hM =>
    cases h₂ with
    | downgrade_from_M_rs j hj _ =>
      -- 1. la cache (ora in `I`) scarta l'`rqIμ` stantio nella stessa posizione `j`
      refine ⟨_, .downgrade_from_M_rs1 _ j hj rfl, ?eq⟩
      -- 2. i due stati coincidono campo per campo
      case eq => rfl

/-- Coppia vuota: il rilascio spontaneo richiede `state = M`, lo scarto dello stantio
`downgrade_from_M_rs1` richiede `state = I`. -/
theorem comm_rq_data_not_available_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''',
    cache_mi_step_internal s'' .rq_data_not_available s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

theorem comm_upgrade_from_I_rq_upgrade_from_I_rq {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s .upgrade_from_I_rq s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' .upgrade_from_I_rq s''' := by
  rintro ⟨ h₁, h₂ ⟩ ⟨ h₃, h₄ ⟩;
  exact ⟨ _, cache_mi_step_internal.upgrade_from_I_rq _ ‹_›, cache_mi_step_internal.upgrade_from_I_rq _ ‹_› ⟩


/-- Il secondo `rqM` (spedito con un grant già in volo) è una richiesta doppia: da `s'` la cache
prende il grant pendente (stessa posizione `j`), rilascia (`rsIμ v`), il parent registra il rilascio
e concede il duplicato, la cache riprende la linea: le cache sono come dopo la presa diretta. Se
un'altra riga della directory è a `M`, `s` è irraggiungibile (vista cattiva 5 o, con riga `i` a `I`, 4). -/
theorem comm_upgrade_from_I_rq_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.cache .upgrade_from_I_rq i) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs v) i) s'' →
  (∃ t₁ t₂ t₃ t₄ t₅,
    mi_step_internal s' (.cache (.upgrade_from_I_rs v) i) t₁ ∧
    mi_step_internal t₁ (.cache .rq_data_not_available i) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₃ ∧
    mi_step_internal t₃ (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t₄ ∧
    mi_step_internal t₄ (.cache (.upgrade_from_I_rs v) i) t₅ ∧
    s''.caches = t₅.caches)
  ∨
    ¬ MI.reachable s := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | upgrade_from_I_rq hI =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | upgrade_from_I_rs _ j hj hI' =>
          by_cases hall : ∀ k, k ≠ i → s.parent.shared_state k = Bstate.I
          · left
            refine ⟨_, _, _, _, _,
              mi_step_internal.cache _ ?c1 _ _ ?p1,
              mi_step_internal.cache _ ?c2 _ _ ?p2,
              mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p3,
              mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p4,
              mi_step_internal.cache _ ?c3 _ _ ?p5,
              ?eq⟩
            -- 1. la cache prende il grant pendente (posizione j)
            case p1 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ j ?_ ?_
              · exact hj
              · exact hI
            -- 2. rilascio spontaneo: rsIμ v in coda dopo il duplicato rqM
            case p2 =>
              simp only [update_Fin_gss]
              refine .rq_data_not_available _ ?_
              rfl
            -- 3. il parent consuma l'rsIμ (posizione (cp ++ [rqM]).length): riga i := I, value := v
            case p3 =>
              refine .downgrade_from_M_rq1 _ _ _ ((s.caches i).queue_cp ++ [CPEvent.rqM]).length ?_
              simp only [update_Fin_gss]
              exact lst_get _ _
            -- 4. il parent concede il duplicato rqM (posizione cp.length): rsM v in coda
            case p4 =>
              refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
              · simp only [update_Fin_gss, lst_erase]
                exact lst_get _ _
              · intro k
                by_cases hk : k = i
                · subst hk; simp only [update_Fin_gss]
                · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hall k hk
            -- 5. la cache riprende la linea (posizione (pc.eraseIdx j).length)
            case p5 =>
              simp only [update_Fin_gss]
              refine .upgrade_from_I_rs _ _ ((s.caches i).queue_pc.eraseIdx j).length ?_ ?_
              · exact lst_get _ _
              · rfl
            -- le cache coincidono: ⟨M, v, cp, pc.eraseIdx j, ext⟩ da entrambi i lati
            case eq =>
              funext k
              by_cases hk : k = i
              · subst hk
                simp only [update_Fin_gss, lst_erase]
              · simp only [update_Fin_gso2 _ _ _ _ hk]
          · right
            obtain ⟨k, hk⟩ := not_forall.mp hall
            obtain ⟨hki, hkM⟩ := Classical.not_imp.mp hk
            have hkM' : s.parent.shared_state k = Bstate.M := by
              cases h : s.parent.shared_state k with
              | M => rfl
              | I => exact absurd h hkM
            cases hdi : s.parent.shared_state i with
            | M =>
              -- due righe della directory a M (vista cattiva 5)
              exact badView_unreachable s
                ⟨i, k, Or.inr (Or.inr (Or.inr (Or.inr ⟨decide_eq_false (Ne.symm hki), hdi, hkM'⟩)))⟩
            | I =>
              -- il grant rsM v è in volo su i mentre la directory dà i a I (vista cattiva 4)
              intro hreach
              have hsync : synced s := by
                have key : ∀ x, ReflTransGen MI.atrans (default : MIState n) x → synced x := by
                  intro x hx
                  induction hx with
                  | refl => exact fun _ => ⟨rfl, rfl⟩
                  | tail _ hstep ih => obtain ⟨t, ht⟩ := hstep; exact synced_step ih ht
                exact key s (hreach _ mi_init_default)
              have hj' : (s.parent.queue_pci i)[j]? = some (PCEvent.rsM v) := by
                rw [(hsync i).2]; exact hj
              have hpos : 0 < (s.parent.queue_pci i).countP isGrant :=
                List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj', rfl⟩
              refine badView_unreachable s
                ⟨i, i, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hdi⟩)))⟩ hreach
              show Cnt.ofCount (parentMsgs s.parent i) ≠ .zero
              rw [Ne, Cnt.ofCount_eq_zero]; unfold parentMsgs; omega

theorem comm_upgrade_from_I_rq_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  intro h1 h2
  cases h1 ; cases h2
  cases ‹s.state = Bstate.I›.symm.trans ‹s.state = Bstate.M›

/-- Diamante vero: la richiesta `rqM` accoda in `queue_cp`, lo scarto dello stantio toglie
da `queue_pc` (posizione `j`); entrambi lasciano la cache in `I`, quindi le due azioni si
scambiano e atterrano sullo stesso record. -/
theorem comm_upgrade_from_I_rq_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' := by
  intro h1 h2
  cases h1 with
  | upgrade_from_I_rq hI =>
    cases h2 with
    | downgrade_from_M_rs1 j hj _ =>
      -- da s'' (tolto lo stantio in j, stato I per costruzione): si spedisce l'rqM;
      -- da s' (rqM accodato, stato ancora s.state = I per hI): si scarta lo stantio in j
      exact ⟨_, .upgrade_from_I_rq _ rfl, .downgrade_from_M_rs1 _ j hj hI⟩

/-- **Due grant presi dalla stessa cache.** Stessa posizione `j`: è lo stesso `rsM`, quindi
`v₁ = v₂` e `s' = s''`. Posizioni diverse: due `rsM` in volo per lo stesso indice; con
`synced` (dimostrato inline lungo il cammino da `default`) la coda della cache è quella del
parent, `countP isGrant ≥ 2`, vista cattiva 3: `s` irraggiungibile. -/
theorem comm_upgrade_from_I_rs_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.upgrade_from_I_rs v₁) i) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs v₂) i) s'' →
  (∃ s''',
    mi_step_internal s'' (.cache (.upgrade_from_I_rs v₁) i) s''' ∧
    mi_step_internal s' (.cache (.upgrade_from_I_rs v₂) i) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  cases h₁ with
  | cache c1 _ _ hc1 =>
    cases hc1
    rename_i j₁ hI₁ hj₁
    cases h₂ with
    | cache c2 _ _ hc2 =>
      cases hc2
      rename_i j₂ hI₂ hj₂
      by_cases hj : j₁ = j₂
      · -- stessa posizione: stesso `rsM`, quindi `v₁ = v₂` e i due stati coincidono
        subst hj
        rw [hj₁] at hj₂
        cases hj₂
        exact Or.inr (Or.inl rfl)
      · -- posizioni diverse: due `rsM` in volo per `i` (vista cattiva 3)
        refine Or.inr (Or.inr ?_)
        intro hreach
        -- le code lato cache e lato parent coincidono lungo ogni cammino da `default`
        have hsync : synced s := by
          have key : ∀ x, ReflTransGen MI.atrans (default : MIState n) x → synced x := by
            intro x hx
            induction hx with
            | refl => exact fun _ => ⟨rfl, rfl⟩
            | tail _ hstep ih => obtain ⟨t, ht⟩ := hstep; exact synced_step ih ht
          exact key s (hreach _ mi_init_default)
        -- i due `rsM` stanno in `s.parent.queue_pci i`
        have hpc := (hsync i).2
        rw [← hpc] at hj₁ hj₂
        have h2 := two_le_countP_of_ne isGrant _ hj₁ hj₂ hj rfl rfl
        refine badView_unreachable s ⟨i, i, Or.inr (Or.inr (Or.inl ?_))⟩ hreach
        show Cnt.ofCount (parentMsgs s.parent i) = .many
        rw [Cnt.ofCount_eq_many]
        unfold parentMsgs; omega

theorem comm_upgrade_from_I_rs_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s (.upgrade_from_I_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.upgrade_from_I_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  intro  h1 h2;
  cases h1 ; cases h2 ; grind

/-- Grant `rsM v` in `j₁` e `rqIμ` in `j₂` (`j₁ ≠ j₂`: messaggi diversi). Se la cache prima scarta
l'`rqIμ` (stantio in `I`) e poi prende il grant, l'invalidazione va comunque onorata: rilascia con
`rq_data_not_available`. Se prima prende il grant, l'`rqIμ` è reale e lo onora con `downgrade_from_M_rs`
nella posizione scalata; le due doppie cancellazioni coincidono (lemma `key`). -/
theorem comm_upgrade_from_I_rs_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s (.upgrade_from_I_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''' t,
    cache_mi_step_internal s'' (.upgrade_from_I_rs v) t ∧
    cache_mi_step_internal t .rq_data_not_available s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List PCEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  cases h₁ with
  | upgrade_from_I_rs _ j₁ hj₁ _ =>
    cases h₂ with
    | downgrade_from_M_rs1 j₂ hj₂ _ =>
      -- posizioni diverse: in j₁ c'è un `rsM v`, in j₂ un `rqIμ`
      have hj : j₁ ≠ j₂ := by intro h; subst h; rw [hj₁] at hj₂; cases hj₂
      rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
      · -- j₁ < j₂: il grant resta in j₁ dopo aver tolto j₂, l'`rqIμ` scala in j₂ - 1 dopo aver tolto j₁
        refine ⟨{ s with state := Bstate.I, value := v,
                         queue_cp := s.queue_cp ++ [CPEvent.rsIμ v],
                         queue_pc := (s.queue_pc.eraseIdx j₂).eraseIdx j₁ },
                { s with state := Bstate.M, value := v,
                         queue_pc := (s.queue_pc.eraseIdx j₂).eraseIdx j₁ }, ?g1, ?g2, ?g3⟩
        -- da s'' (tolto j₂): la cache in I prende il grant in j₁
        case g1 =>
          refine .upgrade_from_I_rs _ v j₁ ?_ rfl
          show (s.queue_pc.eraseIdx j₂)[j₁]? = some (PCEvent.rsM v)
          rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
        -- da t (in M con v): rilascio spontaneo, accoda `rsIμ v`
        case g2 => exact .rq_data_not_available _ rfl
        -- da s' (tolto j₁, in M): onora l'`rqIμ` scalato in j₂ - 1
        case g3 =>
          rw [key _ _ _ hlt]
          refine .downgrade_from_M_rs _ (j₂ - 1) ?_ rfl
          show (s.queue_pc.eraseIdx j₁)[j₂ - 1]? = some PCEvent.rqIμ
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
      · -- j₂ < j₁: il grant scala in j₁ - 1 dopo aver tolto j₂, l'`rqIμ` resta in j₂ dopo aver tolto j₁
        refine ⟨{ s with state := Bstate.I, value := v,
                         queue_cp := s.queue_cp ++ [CPEvent.rsIμ v],
                         queue_pc := (s.queue_pc.eraseIdx j₁).eraseIdx j₂ },
                { s with state := Bstate.M, value := v,
                         queue_pc := (s.queue_pc.eraseIdx j₁).eraseIdx j₂ }, ?g1, ?g2, ?g3⟩
        -- da s'' (tolto j₂): la cache in I prende il grant scalato in j₁ - 1
        case g1 =>
          rw [key _ _ _ hgt]
          refine .upgrade_from_I_rs _ v (j₁ - 1) ?_ rfl
          show (s.queue_pc.eraseIdx j₂)[j₁ - 1]? = some (PCEvent.rsM v)
          rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
        -- da t (in M con v): rilascio spontaneo, accoda `rsIμ v`
        case g2 => exact .rq_data_not_available _ rfl
        -- da s' (tolto j₁, in M): onora l'`rqIμ` in j₂
        case g3 =>
          refine .downgrade_from_M_rs _ j₂ ?_ rfl
          show (s.queue_pc.eraseIdx j₁)[j₂]? = some PCEvent.rqIμ
          rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂

/-- Due `rqIμ` in coda: qualunque sia quello onorato per primo, l'altro è stantio e la cache
(ormai in `I`) lo scarta con `downgrade_from_M_rs1`; i due ordini finiscono nello stesso stato.
Stessa posizione: `s' = s''`. Posizioni diverse: lo stantio sta in `min j₁ j₂` nella coda da cui
è stato tolto il maggiore, e in `max j₁ j₂ - 1` nell'altra; le due doppie cancellazioni coincidono. -/
theorem comm_downgrade_from_M_rs_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .downgrade_from_M_rs s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  (∃ s''',
    cache_mi_step_internal s'' .downgrade_from_M_rs1 s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List PCEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  cases h₁ with
  | downgrade_from_M_rs j₁ hj₁ hM =>
    cases h₂ with
    | downgrade_from_M_rs j₂ hj₂ _ =>
      by_cases hj : j₁ = j₂
      · -- stessa posizione: stesso messaggio consumato, stesso stato
        right; subst hj; rfl
      · left
        rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · -- j₁ < j₂: lo stantio resta in j₁ dopo aver tolto j₂, e scala in j₂ - 1 dopo aver tolto j₁
          refine ⟨{ s with state := Bstate.I,
                           queue_pc := (s.queue_pc.eraseIdx j₂).eraseIdx j₁,
                           queue_cp := s.queue_cp ++ [CPEvent.rsIμ s.value] }, ?g1, ?g2⟩
          -- da s'' (tolto j₂): la cache in I scarta lo stantio in j₁
          case g1 =>
            refine .downgrade_from_M_rs1 _ j₁ ?_ rfl
            show (s.queue_pc.eraseIdx j₂)[j₁]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
          -- da s' (tolto j₁): la cache in I scarta lo stantio in j₂ - 1
          case g2 =>
            rw [key _ _ _ hlt]
            refine .downgrade_from_M_rs1 _ (j₂ - 1) ?_ rfl
            show (s.queue_pc.eraseIdx j₁)[j₂ - 1]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
        · -- j₂ < j₁: simmetrico, lo stantio è quello in j₁
          refine ⟨{ s with state := Bstate.I,
                           queue_pc := (s.queue_pc.eraseIdx j₁).eraseIdx j₂,
                           queue_cp := s.queue_cp ++ [CPEvent.rsIμ s.value] }, ?g1, ?g2⟩
          -- da s'' (tolto j₂): la cache in I scarta lo stantio in j₁ - 1
          case g1 =>
            rw [key _ _ _ hgt]
            refine .downgrade_from_M_rs1 _ (j₁ - 1) ?_ rfl
            show (s.queue_pc.eraseIdx j₂)[j₁ - 1]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
          -- da s' (tolto j₁): la cache in I scarta lo stantio in j₂
          case g2 =>
            refine .downgrade_from_M_rs1 _ j₂ ?_ rfl
            show (s.queue_pc.eraseIdx j₁)[j₂]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂

/-- Coppia vuota: il downgrade onorato richiede `state = M`, lo scarto dello stantio
`downgrade_from_M_rs1` richiede `state = I`. -/
theorem comm_downgrade_from_M_rs_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s .downgrade_from_M_rs s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  ∃ s''',
    cache_mi_step_internal s'' .downgrade_from_M_rs s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''' := by
  intro hs hs';
  cases hs ; cases hs';
  cases ‹s.state = Bstate.M›.symm.trans ‹s.state = Bstate.I›

/-- Due `rqIμ` stantii in coda (cache in `I`): qualunque sia quello scartato per primo, l'altro
si scarta dopo con `downgrade_from_M_rs1`. Stessa posizione: `s' = s''`. Posizioni diverse: l'altro
sta in `min j₁ j₂` nella coda da cui è stato tolto il maggiore, e in `max j₁ j₂ - 1` nell'altra;
le due doppie cancellazioni coincidono (lemma `key`). -/
theorem comm_downgrade_from_M_rs1_downgrade_from_M_rs1 {s s' s''} :
  cache_mi_step_internal s .downgrade_from_M_rs1 s' →
  cache_mi_step_internal s .downgrade_from_M_rs1 s'' →
  (∃ s''',
    cache_mi_step_internal s'' .downgrade_from_M_rs1 s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs1 s''')
  ∨
    s' = s'' := by
  intro h₁ h₂
  -- togliere prima b e poi a (con a < b) è come togliere prima a e poi b - 1
  have key : ∀ (l : List PCEvent) (a b : Nat), a < b →
      (l.eraseIdx b).eraseIdx a = (l.eraseIdx a).eraseIdx (b - 1) := by
    intro l
    induction l with
    | nil => intro a b _; simp
    | cons x xs ih =>
      intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b => simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Nat.add_one_sub_one]
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one]
            rw [ih a (b + 1) (by omega), Nat.add_one_sub_one]
  cases h₁ with
  | downgrade_from_M_rs1 j₁ hj₁ _ =>
    cases h₂ with
    | downgrade_from_M_rs1 j₂ hj₂ _ =>
      by_cases hj : j₁ = j₂
      · -- stessa posizione: stesso messaggio scartato, stesso stato
        right; subst hj; rfl
      · left
        rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · -- j₁ < j₂: lo stantio resta in j₁ dopo aver tolto j₂, e scala in j₂ - 1 dopo aver tolto j₁
          refine ⟨{ s with state := Bstate.I,
                           queue_pc := (s.queue_pc.eraseIdx j₂).eraseIdx j₁ }, ?g1, ?g2⟩
          -- da s'' (tolto j₂): la cache in I scarta lo stantio in j₁
          case g1 =>
            refine .downgrade_from_M_rs1 _ j₁ ?_ rfl
            show (s.queue_pc.eraseIdx j₂)[j₁]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_lt hlt]; exact hj₁
          -- da s' (tolto j₁): la cache in I scarta lo stantio in j₂ - 1
          case g2 =>
            rw [key _ _ _ hlt]
            refine .downgrade_from_M_rs1 _ (j₂ - 1) ?_ rfl
            show (s.queue_pc.eraseIdx j₁)[j₂ - 1]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j₂ - 1 + 1 = j₂ by omega]; exact hj₂
        · -- j₂ < j₁: simmetrico, lo stantio da scartare dopo è quello in j₁
          refine ⟨{ s with state := Bstate.I,
                           queue_pc := (s.queue_pc.eraseIdx j₁).eraseIdx j₂ }, ?g1, ?g2⟩
          -- da s'' (tolto j₂): la cache in I scarta lo stantio in j₁ - 1
          case g1 =>
            rw [key _ _ _ hgt]
            refine .downgrade_from_M_rs1 _ (j₁ - 1) ?_ rfl
            show (s.queue_pc.eraseIdx j₂)[j₁ - 1]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_ge (by omega), show j₁ - 1 + 1 = j₁ by omega]; exact hj₁
          -- da s' (tolto j₁): la cache in I scarta lo stantio in j₂
          case g2 =>
            refine .downgrade_from_M_rs1 _ j₂ ?_ rfl
            show (s.queue_pc.eraseIdx j₁)[j₂]? = some PCEvent.rqIμ
            rw [List.getElem?_eraseIdx_of_lt hgt]; exact hj₂


/-! # Commutazione parent–cache

Un passo del parent (`.parent (.upd_queue e i₁)`) e un passo interno di una cache
(`.cache e' i₂`) applicati allo stesso stato; 4 × 7 = 28 coppie, ordinate per regola del
parent e poi per regola della cache. Enunciato uniforme: diamante, oppure `s' = s''`, oppure
`¬ MI.reachable s`. Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano sempre; con
`i₁ = i₂` il diamante vale quando le due regole scrivono su code diverse, altrimenti lo stato
è irraggiungibile (cache in `M` con il proprio rilascio in volo, cache in `M` con la directory
a `I`, o due messaggi con token in volo). Negli stati con le due copie delle code non
allineate si esce con `¬ MI.reachable s` tramite `synced_of_reachable`. -/

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e load servita
dalla cache `i₂` (che è in `M`). Con `i₁ = i₂` la cache tiene la linea in `M` mentre il suo
rilascio è già in volo: stato irraggiungibile (`not_reachable_of_M_and_rsIμ`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_ld_rq_data_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache (.ld_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache (.ld_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | ld_rq_data_available rst hrq hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hM))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- la load si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            (.ld_rs (s.caches i₂).value)
            { s.caches i₂ with
                extqueue.rs := (s.caches i₂).extqueue.rs ++ [Event.ld_rs (s.caches i₂).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e store servita
dalla cache `i₂` (che è in `M`). Con `i₁ = i₂` la cache tiene la linea in `M` mentre il suo
rilascio è già in volo: stato irraggiungibile (`not_reachable_of_M_and_rsIμ`). Con `i₁ ≠ i₂`
i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_st_rq_M_state {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache (.st_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache (.st_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | st_rq_M_state _ rst hrq hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hM))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- la store si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂) (.st_rs w)
            { s.caches i₂ with value := w, extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.st_rq_M_state _ w rst hrq hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio spontaneo
della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂` la cache è in `M`
mentre il suo rilascio è già in volo: stato irraggiungibile (`not_reachable_of_M_and_rsIμ`).
Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: è il diamante. -/
theorem comm_downgrade_from_M_rq1_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hM))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            .rq_data_not_available
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value],
                state := Bstate.I } := by
          rw [hci]; exact cache_mi_step_internal.rq_data_not_available _ hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in posizione `j` di `queue_cip i₁`) e
richiesta della cache `i₂` (in `I`, accoda un `rqM` a `queue_cp`). Con `i₁ = i₂` l'`rqM`
accodato non sposta la posizione `j` e il downgrade riallinea le copie della cache: diamante.
Con `i₁ ≠ i₂` i due passi toccano indici diversi: ancora il diamante. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rq {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent consuma la posizione `j`, la cache accoda in fondo
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rsIμ v` in posizione `j` sopravvive all'`rqM` accodato dalla cache
        case gp =>
          simp only [update_Fin_gss, ← hs1, List.getElem?_append_left hlt]; exact hj
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc => simp only [downgradeSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSt, update_Fin_gss, ← hs1, ← hs2,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [downgradeSt, update_Fin_gss, ← hs1,
                List.eraseIdx_append_of_lt_length hlt]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- la richiesta si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            .upgrade_from_I_rq
            { s.caches i₂ with queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rqM] } := by
          rw [hci]; exact cache_mi_step_internal.upgrade_from_I_rq _ hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e concessione ricevuta
dalla cache `i₂` (in `I`, consuma un `rsM w` da `queue_pc`). Con `i₁ = i₂` ci sono due messaggi
con token in volo per lo stesso indice (`rsM` in `queue_pci`, `rsIμ` in `queue_cip`): vista
cattiva 3, stato irraggiungibile. Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq1_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache (.upgrade_from_I_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM w` in `queue_pci i₁` e `rsIμ v` in `queue_cip i₁` (vista cattiva 3)
        subst hne
        obtain ⟨_, hs2⟩ := hsync i₁
        refine Or.inr (Or.inr (badView_unreachable s ⟨i₁, i₁, Or.inr (Or.inr (Or.inl ?_))⟩))
        show Cnt.ofCount (parentMsgs s.parent i₁) = .many
        rw [Cnt.ofCount_eq_many]
        -- un rilascio in `queue_cip i₁`
        have h1 : 0 < (s.parent.queue_cip i₁).countP isRelease :=
          List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩
        -- una concessione in `queue_pci i₁` (copia della cache, via `hsync`)
        have h2 : 0 < (s.parent.queue_pci i₁).countP isGrant := by
          rw [hs2]; exact List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj', rfl⟩
        unfold parentMsgs; omega
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- la concessione si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            (.upgrade_from_I_rs w)
            { s.caches i₂ with
                state := Bstate.M, value := w,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.upgrade_from_I_rs _ w j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in `queue_cip i₁`) e rilascio su richiesta
della cache `i₂` (in `M`, consuma un `rqIμ` da `queue_pc` e accoda un `rsIμ`). Con `i₁ = i₂`
la cache è in `M` mentre il suo rilascio è già in volo: stato irraggiungibile
(`not_reachable_of_M_and_rsIμ`). Con `i₁ ≠ i₂` i passi toccano indici diversi: diamante. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con il proprio `rsIμ` in volo
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_rsIμ hj hM))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs _ j' hj' hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Downgrade del parent su `i₁` (consuma un `rsIμ v` in posizione `j` di `queue_cip i₁`) e
scarto di un `rqIμ` stantio da parte della cache `i₂` (in `I`, cancella la posizione `j'` di
`queue_pc`). Con `i₁ = i₂` i due passi cancellano da code diverse e il downgrade riallinea le
copie della cache: diamante. Con `i₁ ≠ i₂` toccano indici diversi: ancora il diamante. -/
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rs1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs1 i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs1 i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `downgradeSt s v i₁ j`
  obtain ⟨j, hj, rfl⟩ := downgrade_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent cancella da `queue_cip`, la cache da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs1 _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache (che scrive solo `queue_pc`)
        case gp => simp only [update_Fin_gss, ← hs1]; exact hj
        -- l'`rqIμ` in posizione `j'` è ancora nella copia riallineata di `queue_pc`
        case gc1 => simp only [downgradeSt, update_Fin_gss, hs2]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il downgrade
        case gc2 => simp only [downgradeSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (copie riallineate via `hsync`)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSt, update_Fin_gss, ← hs1, ← hs2]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSt, update_Fin_gss, ← hs1]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [downgradeSt, update_Fin_gss, ← hs2]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il downgrade non tocca la cache `i₂`
        have hci : (downgradeSt s v i₁ j).caches i₂ = s.caches i₂ := by
          simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hne']
        -- lo scarto si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((downgradeSt s v i₁ j).caches i₂)
            .downgrade_from_M_rs1
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs1 _ j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.downgrade_from_M_rq1 _ v i₁ j ?g),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rsIμ v` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · simp only [downgradeSt]
          · intro q
            simp only [downgradeSt]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [downgradeSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₂ : q = i₂
            · subst hq₂
              simp only [downgradeSt, update_Fin_gss]
            · simp only [downgradeSt, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`) e load
servita dalla cache `i₂` (che è in `M`). Con `i₁ = i₂` la cache è in `M` mentre la directory
la dà a `I`: stato irraggiungibile (`not_reachable_of_M_and_dirI`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_ld_rq_data_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache (.ld_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache (.ld_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | ld_rq_data_available rst hrq hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con directory a `I`
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_dirI hM (hall i₁)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- la load si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂)
            (.ld_rs (s.caches i₂).value)
            { s.caches i₂ with
                extqueue.rs := (s.caches i₂).extqueue.rs ++ [Event.ld_rs (s.caches i₂).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`) e store
servita dalla cache `i₂` (che è in `M`). Con `i₁ = i₂` la cache è in `M` mentre la directory
la dà a `I`: stato irraggiungibile (`not_reachable_of_M_and_dirI`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: è il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_st_rq_M_state {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache (.st_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache (.st_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | st_rq_M_state _ rst hrq hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con directory a `I`
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_dirI hM (hall i₁)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- la store si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂) (.st_rs w)
            { s.caches i₂ with value := w, extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.st_rq_M_state _ w rst hrq hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`) e
rilascio spontaneo della cache `i₂` (in `M`, accoda un `rsIμ` e passa a `I`). Con `i₁ = i₂`
la cache è in `M` mentre la directory la dà a `I`: stato irraggiungibile
(`not_reachable_of_M_and_dirI`). Con `i₁ ≠ i₂` i due passi toccano indici diversi: diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con directory a `I`
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_dirI hM (hall i₁)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂) .rq_data_not_available
            { s.caches i₂ with
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value],
                state := Bstate.I } := by
          rw [hci]; exact cache_mi_step_internal.rq_data_not_available _ hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma l'`rqM` in posizione `j` di `queue_cip i₁`, directory tutta
a `I`) e richiesta `upgrade_from_I_rq` della cache `i₂` (in `I`, accoda un `rqM`). Commutano
sempre: con `i₁ = i₂` l'`rqM` accodato in fondo non sposta la posizione `j` (le copie sono
allineate, `hsync`); con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rq {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: l'`rqM` accodato in fondo non disturba la posizione `j`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- `j` è una posizione valida della coda (copia lato cache)
        have hb : j < (s.caches i₁).queue_cp.length := by
          rw [← hs1]; exact (List.getElem?_eq_some_iff.mp hj).1
        -- cancellare `j` commuta con l'append in fondo
        have herase : ((s.caches i₁).queue_cp ++ [CPEvent.rqM]).eraseIdx j
            = (s.caches i₁).queue_cp.eraseIdx j ++ [CPEvent.rqM] :=
          List.eraseIdx_append_of_lt_length hb _
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` in posizione `j` sopravvive all'append della cache
        case g1 =>
          simp only [update_Fin_gss]
          rw [List.getElem?_append_left hb, ← hs1]
          exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₁` è ancora in `I` dopo il grant
        case gc => simp only [grantSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSt, update_Fin_gss, hs1, herase]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSt, update_Fin_gss, hs2]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- la cache `i₂` non è toccata dal grant su `i₁`
        case gc => simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma un `rqM` in `queue_cip i₁`, directory tutta a `I`) e
`upgrade_from_I_rs` della cache `i₂` (che consuma un `rsM w` da `queue_pc`). Con `i₁ = i₂`
c'è un `rsM` in volo verso `i₁` mentre la directory dà `i₁ = I`: vista cattiva 4, stato
irraggiungibile. Con `i₁ ≠ i₂` i due passi toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache (.upgrade_from_I_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: `rsM w` in volo verso `i₁` con directory `i₁ = I` (vista cattiva 4)
        subst hne
        have hg : (s.parent.queue_pci i₁)[j']? = some (PCEvent.rsM w) := by
          rw [(hsync i₁).2]; exact hj'
        refine Or.inr (Or.inr (badView_unreachable s
          ⟨i₁, i₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hall i₁⟩)))⟩))
        show Cnt.ofCount (parentMsgs s.parent i₁) ≠ .zero
        rw [Ne, Cnt.ofCount_eq_zero]
        have hpos : 0 < (s.parent.queue_pci i₁).countP isGrant :=
          List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hg, rfl⟩
        unfold parentMsgs; omega
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- la ricezione dell'`rsM` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂) (.upgrade_from_I_rs w)
            { s.caches i₂ with
                state := Bstate.M,
                value := w,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.upgrade_from_I_rs _ w j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (directory tutta a `I`) e `downgrade_from_M_rs` della cache `i₂`
(che è in `M` e rilascia la linea). Con `i₁ = i₂` la cache è in `M` mentre la directory la dà
a `I`: stato irraggiungibile (`not_reachable_of_M_and_dirI`). Con `i₁ ≠ i₂` i due passi
toccano indici diversi e commutano: il diamante. -/
theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: cache in `M` con directory `i₁ = I`
        subst hne
        exact Or.inr (Or.inr (not_reachable_of_M_and_dirI hM (hall i₁)))
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂) .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs _ j' hj' hM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Grant del parent su `i₁` (consuma l'`rqM` in `queue_cip i₁`, accoda `rsM` a `queue_pci i₁`)
e `downgrade_from_M_rs1` della cache `i₂` (in `I`, scarta un `rqIμ` stantio da `queue_pc`).
Commutano sempre: con `i₁ = i₂` il parent scrive in fondo alla coda da cui la cache cancella
(`(l ++ [rsM _]).eraseIdx j' = l.eraseIdx j' ++ [rsM _]`); con `i₁ ≠ i₂` toccano indici diversi. -/
theorem comm_upgrade_to_M_data_avilable_rq1_downgrade_from_M_rs1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs1 i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs1 i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `grantSt s i₁ j`
  obtain ⟨j, hj, hall, rfl⟩ := grant_inv_st h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci i₁`, la cache cancella da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la posizione `j'` è dentro la coda: sopravvive all'append dell'`rsM`
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj'
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs1 _ j' ?c1 ?c2)) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` (= `queue_cp`, per `hs1`) non è toccato
        case g1 => simp only [update_Fin_gss]; rw [← hs1]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- lato destro: l'`rqIμ` è ancora in posizione `j'` dopo l'append dell'`rsM`
        case c1 =>
          simp only [grantSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il grant
        case c2 => simp only [grantSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSt, update_Fin_gss, hs1, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [grantSt, update_Fin_gss, hs1]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [grantSt, update_Fin_gss, hs2, List.eraseIdx_append_of_lt_length hlt]
            · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: il diamante
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il grant non tocca la cache `i₂`
        have hci : (grantSt s i₁ j).caches i₂ = s.caches i₂ := by
          simp only [grantSt, update_Fin_gso2 _ _ _ _ hne']
        -- lo scarto dell'`rqIμ` si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_mi_step_internal ((grantSt s i₁ j).caches i₂) .downgrade_from_M_rs1
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs1 _ j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- lato sinistro: l'`rqM` in `queue_cip i₁` non è toccato dalla cache `i₂`
        case g1 => simp only [update_Fin_gso2 _ _ _ _ hne]; exact hj
        -- la directory non è toccata dal passo di cache
        case g2 => exact hall
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [grantSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [grantSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato del parent su `i₁` (un `rqM` in `queue_cip k`, directory `i₁ = M`:
accoda un `rqIμ` a `queue_pci i₁`) e load servita dalla cache `i₂` (in `M`). Con `i₁ = i₂`
il parent tocca solo `queue_pci`, la cache solo `extqueue`, e le copie delle code vengono
riallineate (`hsync`); con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_ld_rq_data_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache (.ld_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache (.ld_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `invalidateSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | ld_rq_data_available rst hrq hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `extqueue`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: code riallineate, il resto invariato
        have hci : (invalidateSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ] } := by
          simp only [invalidateSt, update_Fin_gss]
        -- la load si applica ancora da `s'`
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₁)
            (.ld_rs (s.caches i₁).value)
            { s.caches i₁ with
                queue_cp := s.parent.queue_cip i₁,
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ],
                extqueue.rs := (s.caches i₁).extqueue.rs ++ [Event.ld_rs (s.caches i₁).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- l'`rqM` in `queue_cip k` non è toccato dalla load
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: `queue_cp` è la copia di `queue_cip i₁`
            subst hk
            simp only [update_Fin_gss, ← hs1]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case g2 => intro h; cases hM.symm.trans h
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la load si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂)
            (.ld_rs (s.caches i₂).value)
            { s.caches i₂ with
                extqueue.rs := (s.caches i₂).extqueue.rs ++ [Event.ld_rs (s.caches i₂).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- l'`rqM` in `queue_cip k` non è toccato dalla load su `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: `queue_cp` è la copia di `queue_cip i₂`
            subst hk
            simp only [update_Fin_gss, ← (hsync i₂).1]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case g2 => intro h; cases hM.symm.trans h
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`) e store servita
dalla cache `i₂` (in `M`: aggiorna `value` ed `extqueue`). Con `i₁ = i₂` le due regole scrivono
su campi diversi e il passo del parent riallinea le copie delle code (`hsync`); con `i₁ ≠ i₂`
toccano indici diversi. In entrambi i casi si chiude il diamante. -/
theorem comm_upgrade_to_M_invalid_all_st_rq_M_state {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache (.st_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache (.st_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `invalidateSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | st_rq_M_state _ rst hrq hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `value` ed `extqueue`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.st_rq_M_state _ _ rst ?c1 ?c2)) ?eq⟩
        -- l'`rqM` in `queue_cip k` non è toccato dalla store
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: `queue_cp` è la copia di `queue_cip i₁`
            subst hk
            simp only [update_Fin_gss, ← hs1]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case g2 => intro h; cases hM.symm.trans h
        -- la store è ancora in testa a `extqueue.rq` dopo il passo del parent
        case c1 => simp only [invalidateSt, update_Fin_gss]; exact hrq
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case c2 => simp only [invalidateSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.st_rq_M_state _ _ rst ?c1 ?c2)) ?eq⟩
        -- l'`rqM` in `queue_cip k` non è toccato dalla store su `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: `queue_cp` è la copia di `queue_cip i₂`
            subst hk
            simp only [update_Fin_gss, ← (hsync i₂).1]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case g2 => intro h; cases hM.symm.trans h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hrq
        case c2 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hcM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`) e rilascio
spontaneo della cache `i₂` (in `M`: passa a `I` e accoda un `rsIμ` a `queue_cp`). Con `i₁ = i₂`
le due regole scrivono su code diverse e il passo del parent riallinea le copie (`hsync`);
se il richiedente `k` è `i₂`, l'`rqM` in posizione `j` sopravvive all'append. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `invalidateSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp` e `state`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- l'`rqM` in `queue_cip k` sopravvive all'append dell'`rsIμ`
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case g2 => intro h; cases hM.symm.trans h
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case c1 => simp only [invalidateSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.rq_data_not_available _ ?c1)) ?eq⟩
        -- l'`rqM` in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rsIμ` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case g2 => intro h; cases hM.symm.trans h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hcM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato del parent su `i₁` (accoda un `rqIμ` a `queue_pci i₁`) e richiesta
della cache `i₂` (in `I`: accoda un `rqM` a `queue_cp`). Con `i₁ = i₂` le due regole scrivono
su code diverse e il passo del parent riallinea le copie (`hsync`); se il richiedente `k` è
`i₂`, l'`rqM` in posizione `j` sopravvive all'append. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rq {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- code non allineate: `s` non è raggiungibile
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  -- `s'` è il record esplicito `invalidateSt s i₁`
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  -- `s''` è il record esplicito del passo di cache
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?c1)) ?eq⟩
        -- l'`rqM` in `queue_cip k` sopravvive all'append del nuovo `rqM`
        case g1 =>
          by_cases hk : i₁ = k
          · -- il richiedente è `i₁`: la posizione `j` è prima dell'`rqM` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← hs1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₁`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case g2 => intro h; cases hM.symm.trans h
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case c1 => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?g1 ?g2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?c1)) ?eq⟩
        -- l'`rqM` in `queue_cip k` sopravvive al passo della cache `i₂`
        case g1 =>
          by_cases hk : i₂ = k
          · -- il richiedente è `i₂`: la posizione `j` è prima dell'`rqM` accodato
            subst hk
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
            simp only [update_Fin_gss, ← (hsync i₂).1]
            rw [List.getElem?_append_left hlt]; exact hj
          · -- il richiedente non è `i₂`: coda invariata
            simp only [update_Fin_gso2 _ _ _ _ (Ne.symm hk)]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case g2 => intro h; cases hM.symm.trans h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case c1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato (`upgrade_to_M_invalid_all k`: il parent accoda un `rqIμ` a
`queue_pci i₁`) e `upgrade_from_I_rs` (la cache `i₂`, in `I`, consuma l'`rsM w` in posizione
`j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` l'`rqIμ` finisce in fondo alla coda e non
sposta la posizione `j'`; con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache (.upgrade_from_I_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      -- l'`rsM w` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rs _ w j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k` è ancora al suo posto dopo il passo della cache
        case gp1 =>
          by_cases hk : k = i₁
          · rw [hk] at hj ⊢
            simp only [update_Fin_gss]
            rw [← hs1]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- l'`rsM w` è ancora in posizione `j'`: l'`rqIμ` è stato appeso in fondo
        case gc1 =>
          simp only [invalidateSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc2 => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.upgrade_from_I_rs _ w j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k`: la cache `i₂` non tocca `queue_cp`
        case gp1 =>
          by_cases hk : k = i₂
          · rw [hk] at hj ⊢
            simp only [update_Fin_gss]
            rw [← hs1]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case gc2 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato (`upgrade_to_M_invalid_all k`: il parent accoda un `rqIμ` a
`queue_pci i₁`) e `downgrade_from_M_rs` (la cache `i₂`, in `M`, consuma l'`rqIμ` in posizione
`j'` di `queue_pc` e accoda un `rsIμ` a `queue_cp`) commutano sempre. Con `i₁ = i₂` il nuovo
`rqIμ` finisce in fondo e non sposta `j'`, e l'`rqM` del richiedente `k` resta prima
dell'`rsIμ` appeso; con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hMc =>
      -- l'`rqIμ` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache consuma da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k` è ancora al suo posto: l'`rsIμ` è appeso in fondo
        case gp1 =>
          by_cases hk : k = i₁
          · rw [hk] at hj ⊢
            have hlt : j < (s.parent.queue_cip i₁).length := (List.getElem?_eq_some_iff.mp hj).1
            simp only [update_Fin_gss]
            rw [← hs1, List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- l'`rqIμ` consumato è ancora in posizione `j'`: il nuovo è stato appeso in fondo
        case gc1 =>
          simp only [invalidateSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case gc2 => simp only [invalidateSt, update_Fin_gss]; exact hMc
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.downgrade_from_M_rs _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k`: se `k = i₂` sta prima dell'`rsIμ` appeso
        case gp1 =>
          by_cases hk : k = i₂
          · rw [hk] at hj ⊢
            have hlt : j < (s.parent.queue_cip i₂).length := (List.getElem?_eq_some_iff.mp hj).1
            simp only [update_Fin_gss]
            rw [← hs1, List.getElem?_append_left hlt]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case gc2 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hMc
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- Invalidate mirato (`upgrade_to_M_invalid_all k`: il parent accoda un `rqIμ` a
`queue_pci i₁`) e `downgrade_from_M_rs1` (la cache `i₂`, già in `I`, scarta l'`rqIμ` in
posizione `j'` di `queue_pc`) commutano sempre. Con `i₁ = i₂` il nuovo `rqIμ` finisce in fondo
e non sposta `j'`; con `i₁ ≠ i₂` i due passi toccano indici diversi. Sempre il diamante. -/
theorem comm_upgrade_to_M_invalid_all_downgrade_from_M_rs1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs1 i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs1 i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨⟨j, hj⟩, hM, rfl⟩ := invalidate_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hI =>
      -- l'`rqIμ` sta in una posizione valida della coda della cache
      have hlt' : j' < (s.caches i₂).queue_pc.length := (List.getElem?_eq_some_iff.mp hj').1
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache scarta da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs1 _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k` è ancora al suo posto: la cache non tocca `queue_cp`
        case gp1 =>
          by_cases hk : k = i₁
          · rw [hk] at hj ⊢
            simp only [update_Fin_gss]
            rw [← hs1]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- l'`rqIμ` scartato è ancora in posizione `j'`: il nuovo è stato appeso in fondo
        case gc1 =>
          simp only [invalidateSt, update_Fin_gss]
          rw [hs2, List.getElem?_append_left hlt']; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc2 => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs1, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq
              simp only [invalidateSt, update_Fin_gss, hs2,
                List.eraseIdx_append_of_lt_length hlt']
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        obtain ⟨hs1, hs2⟩ := hsync i₂
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁
            (parent_mi_step.upgrade_to_M_invalid_all _ k i₁ j ?gp1 ?gp2),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.downgrade_from_M_rs1 _ j' ?gc1 ?gc2)) ?eq⟩
        -- l'`rqM` del richiedente `k`: la cache `i₂` non tocca `queue_cp`
        case gp1 =>
          by_cases hk : k = i₂
          · rw [hk] at hj ⊢
            simp only [update_Fin_gss]
            rw [← hs1]; exact hj
          · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hj
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp2 =>
          show ¬ s.parent.shared_state i₁ = Bstate.I
          rw [hM]; intro h; cases h
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc1 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hj'
        case gc2 => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e la load servita dalla
cache `i₂` (in `M`: tocca solo `extqueue`) commutano sempre. Con `i₁ = i₂` le due regole
scrivono su campi diversi e il passo del parent riallinea le copie della cache alle sue
(`hsync`); con `i₁ ≠ i₂` toccano indici diversi. In entrambi i casi si chiude il diamante. -/
theorem comm_invalid_all_ld_rq_data_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache (.ld_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache (.ld_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | ld_rq_data_available rst hrq hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `extqueue`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: stato e `extqueue` intatti, code riallineate
        have hci : (invalidateSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ] } := by
          simp only [invalidateSt, update_Fin_gss]
        -- la load si applica ancora da `s'`
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₁)
            (.ld_rs (s.caches i₁).value)
            { s.caches i₁ with
                queue_cp := s.parent.queue_cip i₁,
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ],
                extqueue.rs := (s.caches i₁).extqueue.rs ++ [Event.ld_rs (s.caches i₁).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il passo del parent su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la load si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂)
            (.ld_rs (s.caches i₂).value)
            { s.caches i₂ with
                extqueue.rs := (s.caches i₂).extqueue.rs ++ [Event.ld_rs (s.caches i₂).value],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.ld_rq_data_available _ rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e la store servita dalla
cache `i₂` (in `M`: aggiorna `value` ed `extqueue`) commutano sempre. Con `i₁ = i₂` le due
regole scrivono su campi diversi e il passo del parent riallinea le copie della cache alle
sue (`hsync`); con `i₁ ≠ i₂` toccano indici diversi. In entrambi i casi si chiude il diamante. -/
theorem comm_invalid_all_st_rq_M_state {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache (.st_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache (.st_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | st_rq_M_state _ rst hrq hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `value` ed `extqueue`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: stato e `extqueue` intatti, code riallineate
        have hci : (invalidateSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ] } := by
          simp only [invalidateSt, update_Fin_gss]
        -- la store si applica ancora da `s'`
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₁) (.st_rs w)
            { s.caches i₁ with
                value := w,
                queue_cp := s.parent.queue_cip i₁,
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ],
                extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.st_rq_M_state _ w rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il passo del parent su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la store si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂) (.st_rs w)
            { s.caches i₂ with value := w, extqueue.rq := rst } := by
          rw [hci]; exact cache_mi_step_internal.st_rq_M_state _ w rst hrq hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e `rq_data_not_available`
(la cache `i₂`, in `M`, rilascia la linea accodando un `rsIμ` a `queue_cp`) commutano sempre.
Con `i₁ = i₂` le due regole scrivono su code diverse e il passo del parent riallinea le copie
della cache alle sue (`hsync`); con `i₁ ≠ i₂` toccano indici diversi: sempre il diamante. -/
theorem comm_invalid_all_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache .rq_data_not_available i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache .rq_data_not_available i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | rq_data_not_available hcM =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `state` e `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        -- la cache `i₁` dopo il passo del parent: stato intatto, code riallineate
        have hci : (invalidateSt s i₁).caches i₁ =
            { s.caches i₁ with queue_cp := s.parent.queue_cip i₁,
                               queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ] } := by
          simp only [invalidateSt, update_Fin_gss]
        -- il rilascio si applica ancora da `s'`
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₁) .rq_data_not_available
            { s.caches i₁ with
                state := Bstate.I,
                queue_cp := s.parent.queue_cip i₁ ++ [CPEvent.rsIμ (s.caches i₁).value],
                queue_pc := s.parent.queue_pci i₁ ++ [PCEvent.rqIμ] } := by
          rw [hci]; exact cache_mi_step_internal.rq_data_not_available _ hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _ hstep) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- il passo del parent su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- il rilascio si applica ancora da `s'`: stessa cache, stesso stato di arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂) .rq_data_not_available
            { s.caches i₂ with
                state := Bstate.I,
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_mi_step_internal.rq_data_not_available _ hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e `upgrade_from_I_rq`
(la cache `i₂`, in `I`, accoda un `rqM` a `queue_cp`) commutano sempre. Con `i₁ = i₂` le due
regole scrivono su code diverse e il passo del parent riallinea le copie della cache alle
sue (`hsync`); con `i₁ ≠ i₂` toccano indici diversi. In entrambi i casi si chiude il diamante. -/
theorem comm_invalid_all_upgrade_from_I_rq {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache .upgrade_from_I_rq i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache .upgrade_from_I_rq i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rq hI =>
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent tocca `queue_pci`, la cache `queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _
            (cache_mi_step_internal.upgrade_from_I_rq _ ?gc)) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- la cache `i₂` non è toccata dal passo del parent su `i₁`
        case gc => simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']; exact hI
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                update_Fin_gso2 _ _ _ _ hne']
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e `upgrade_from_I_rs`
(la cache `i₂`, in `I`, consuma l'`rsM w` in posizione `j'` di `queue_pc`) commutano sempre.
Con `i₁ = i₂` l'append in fondo non sposta la posizione `j'` e il passo del parent riallinea
le copie della cache alle sue (`hsync`); con `i₁ ≠ i₂` toccano indici diversi. Diamante. -/
theorem comm_invalid_all_upgrade_from_I_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache (.upgrade_from_I_rs w) i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache (.upgrade_from_I_rs w) i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | upgrade_from_I_rs _ j' hj' hI =>
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIμ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIμ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIμ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache cancella da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.upgrade_from_I_rs _ w j' ?gj ?gc)) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- l'`rsM w` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invalidateSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂)
            (.upgrade_from_I_rs w)
            { s.caches i₂ with
                state := Bstate.M,
                value := w,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.upgrade_from_I_rs _ w j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e `downgrade_from_M_rs`
(la cache `i₂`, in `M`, consuma l'`rqIμ` in posizione `j'` di `queue_pc`, passa a `I` e
accoda il rilascio a `queue_cp`) commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta
`j'` e il parent riallinea le copie (`hsync`); con `i₁ ≠ i₂` indici diversi. Diamante. -/
theorem comm_invalid_all_downgrade_from_M_rs {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs j' hj' hcM =>
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIμ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIμ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIμ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache tocca `queue_pc`/`queue_cp`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs _ j' ?gj ?gc)) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- l'`rqIμ` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invalidateSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `M` dopo il passo del parent
        case gc => simp only [invalidateSt, update_Fin_gss]; exact hcM
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂)
            .downgrade_from_M_rs
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j',
                queue_cp := (s.caches i₂).queue_cp ++ [CPEvent.rsIμ (s.caches i₂).value] } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs _ j' hj' hcM
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]

/-- `invalid_allM` (il parent accoda un `rqIμ` a `queue_pci i₁`) e `downgrade_from_M_rs1`
(la cache `i₂`, già in `I`, scarta l'`rqIμ` stantio in posizione `j'` di `queue_pc`)
commutano sempre. Con `i₁ = i₂` l'append in fondo non sposta `j'` e il parent riallinea le
copie (`hsync`); con `i₁ ≠ i₂` toccano indici diversi. Diamante. -/
theorem comm_invalid_all_downgrade_from_M_rs1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue .invalid_allM i₁)) s' →
  mi_step_internal s (.cache .downgrade_from_M_rs1 i₂) s'' →
  (∃ s''',
    mi_step_internal s'' (.parent (.upd_queue .invalid_allM i₁)) s''' ∧
    mi_step_internal s' (.cache .downgrade_from_M_rs1 i₂) s''')
  ∨
    s' = s''
  ∨
    ¬ MI.reachable s := by
  intro h₁ h₂
  by_cases hsync : synced s
  swap
  · -- stati con le code non allineate: irraggiungibili
    exact Or.inr (Or.inr (fun hr => hsync (synced_of_reachable hr)))
  obtain ⟨hM, rfl⟩ := invalidAllM_inv h₁
  cases h₂ with
  | cache c _ _ hc =>
    cases hc with
    | downgrade_from_M_rs1 j' hj' hI =>
      -- la posizione `j'` è valida in `queue_pc`: l'append di `rqIμ` non la sposta
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj'
      have herase : ((s.caches i₂).queue_pc ++ [PCEvent.rqIμ]).eraseIdx j'
          = (s.caches i₂).queue_pc.eraseIdx j' ++ [PCEvent.rqIμ] :=
        List.eraseIdx_append_of_lt_length hlt _
      by_cases hne : i₁ = i₂
      · -- stesso indice: il parent accoda a `queue_pci`, la cache cancella da `queue_pc`
        subst hne
        obtain ⟨hs1, hs2⟩ := hsync i₁
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₁ _
            (cache_mi_step_internal.downgrade_from_M_rs1 _ j' ?gj ?gc)) ?eq⟩
        -- la directory `i₁` è ancora `M` dopo il passo della cache
        case gp => exact hM
        -- l'`rqIμ` è ancora in posizione `j'` dopo l'append del parent
        case gj =>
          simp only [invalidateSt, update_Fin_gss, hs2]
          rw [List.getElem?_append_left hlt]; exact hj'
        -- la cache `i₁` è ancora in `I` dopo il passo del parent
        case gc => simp only [invalidateSt, update_Fin_gss]; exact hI
        -- i due stati finali coincidono, campo per campo (con le copie riallineate)
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs1]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
          · intro q
            by_cases hq : q = i₁
            · subst hq; simp only [invalidateSt, update_Fin_gss, hs2, herase]
            · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq]
      · -- indici distinti: i due passi lavorano su righe diverse
        have hne' : i₂ ≠ i₁ := Ne.symm hne
        -- l'invalidate su `i₁` non tocca la cache `i₂`
        have hci : (invalidateSt s i₁).caches i₂ = s.caches i₂ := by
          simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hne']
        -- la regola di cache si applica ancora da `s'`: stessa cache, stesso arrivo
        have hstep : cache_mi_step_internal ((invalidateSt s i₁).caches i₂)
            .downgrade_from_M_rs1
            { s.caches i₂ with
                state := Bstate.I,
                queue_pc := (s.caches i₂).queue_pc.eraseIdx j' } := by
          rw [hci]; exact cache_mi_step_internal.downgrade_from_M_rs1 _ j' hj' hI
        refine Or.inl ⟨_,
          mi_step_internal.parent_upd_queue _ _ _ i₁ (parent_mi_step.invalid_all _ i₁ ?gp),
          mi_step_congr (mi_step_internal.cache _ _ i₂ _ hstep) ?eq⟩
        -- la directory `i₁` non è toccata dal passo della cache `i₂`
        case gp => exact hM
        -- i due stati finali coincidono, campo per campo
        case eq =>
          refine MIState.ext_all ?_ ?_ ?_ ?_ ?_
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
          · exact rfl
          · intro q; exact rfl
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss]
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₂]
          · intro q
            by_cases hq₁ : q = i₁
            · subst hq₁
              simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
            · by_cases hq₂ : q = i₂
              · subst hq₂
                simp only [invalidateSt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hne,
                  update_Fin_gso2 _ _ _ _ hne']
              · simp only [invalidateSt, update_Fin_gso2 _ _ _ _ hq₁, update_Fin_gso2 _ _ _ _ hq₂]
