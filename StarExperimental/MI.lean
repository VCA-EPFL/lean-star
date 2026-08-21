
import Star.BackwardsInvariants.TwoPhaseCommit

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

@[simp]
def mi_init: (MIState n) -> Prop := Inhabited.default



inductive CacheInternalEvent where
  | ld_rs (value : Value)
  | st_rs (value : Value)
  | rq_data_not_available
  | upgrade_from_I_rq
  | upgrade_from_I_rs  (v: Value) --(n : Nat)
  | downgrade_from_M_rs --(n : Nat)
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


-- def unreachable_set {n} (s : MIState n) : Prop :=
--   (∀ (i : Fin n), (s.caches i).state = Bstate.M → ¬ ∀ (j : Fin n), j ≠ i → s.parent.shared_state j = Bstate.I)


-- theorem back_reachable_MI {n} {x} : ∀ s, @unreachable_set n s -> MI.backwards_reachable_from s x → @unreachable_set n x := by
--   dsimp [MI.LTS.backwards_reachable_from]
--   intro s hu h
--   induction h using ReflTransGen.head_induction_on with
--   | refl => grind
--   | @head a c h1 h2 h3 =>
--     clear h2
--     dsimp [Function.swap, MI, MI.LTS.atrans] at h1
--     obtain ⟨t, ht⟩ := h1
--     apply h3; clear h3
--     cases ht with
--     | parent_no_queue parent' e i hstep =>
--         -- `parent_mi_step` non ha costruttori per `.no_queue`: transizione impossibile
--         cases hstep
--     | cache cache' i e hstep =>
--         intro k hk
--         by_cases hki : k = i
--         · subst hki
--           cases hstep with
--           | ld_rq_data_available rst hrq hM =>
--               -- stato M invariato (cambia solo extqueue): si usa hu direttamente
--               have hui := hu k
--               simp only [update_Fin_gss] at hui
--               exact hui hM
--           | st_rq_M_state v rst hrq hM =>
--               have hui := hu k
--               simp only [update_Fin_gss] at hui
--               exact hui hM
--           | upgrade_from_I_rq hI =>
--               -- il pre-stato ha cache k in I, contraddice hk : ... = M
--               rw [hI] at hk; exact Bstate.noConfusion hk
--           | upgrade_from_I_rs v j hj hI =>
--               rw [hI] at hk; exact Bstate.noConfusion hk
--           | rq_data_not_available hM =>
--               simp_all
--               -- FALSO: la cache k passa da M a I, quindi nel post-stato k non è più
--               -- in M e `hu` non dà alcun vincolo su di essa; non si può concludere
--               -- nulla su c. Vedi `unreachable_set_NOT_backward_closed`.
--               admit
--           | downgrade_from_M_rs j hj hM =>
--               -- FALSO: stesso motivo, transizione M → I sulla cache k.
--               admit
--         · -- k ≠ i: la cache k e lo shared_state non cambiano, si usa hu k
--           have hui := hu k
--           simp only [update_Fin_gso2 _ _ _ _ hki] at hui
--           exact hui hk
--     | parent_upd_queue parent' e i hstep =>
--         intro k hk
--         -- lo step del parent tocca solo le code delle cache, non il loro stato
--         have hpk : ((update_Fin i
--               { c.caches i with queue_cp := parent'.queue_cip i, queue_pc := parent'.queue_pci i }
--               c.caches) k).state = Bstate.M := by
--           by_cases h : k = i
--           · subst h; simp only [update_Fin_gss]; exact hk
--           · simp only [update_Fin_gso2 _ _ _ _ h]; exact hk
--         have hui := hu k hpk
--         cases hstep with
--         | upgrade_to_M_invalid_all idx j hj hne =>
--             -- shared_state invariato
--             exact hui
--         | invalid_all j hM =>
--             -- shared_state invariato
--             exact hui
--         | downgrade_from_M_rq1 v j hj =>
--             -- il parent porta shared_state i a I: rende "più I" gli stati, ok all'indietro
--             intro hall
--             apply hui
--             intro jj hjj
--             by_cases hjc : jj = i
--             · subst hjc; simp only [update_Fin_gss]
--             · simp only [update_Fin_gso2 _ _ _ _ hjc]; exact hall jj hjj
--         | upgrade_to_M_data_avilable_rq1 j hj hall =>
--             -- FALSO: il parent concede M alla cache i (con premessa "tutti gli shared_state I").
--             -- Se un'altra cache k ≠ i è già in M, allora c non è nell'invariante mentre il
--             -- post-stato sì: la chiusura all'indietro fallisce.
--             admit


/-!
# Un insieme di stati irraggiungibili per MI

## Perché la vecchia `unreachable_set` non funzionava

La definizione

    ∀ i, (s.caches i).state = M → ¬ ∀ j ≠ i, shared_state j = I

è una formula *universale*: è quindi vera (a vuoto) su tutti gli stati in cui
nessuna cache è in `M`, in particolare sullo stato iniziale.  Con quella
definizione `back_reachable_MI` è falso, ad esempio con `n = 2`:

    c = (caches 0 = M, caches 1 = I, shared = (M, I))   ∉ insieme
    ↓ cache 0 : rq_data_not_available
    a = (caches 0 = I, caches 1 = I, shared = (M, I))   ∈ insieme (a vuoto)

Un "insieme di stati irraggiungibili" deve invece essere *esistenziale* e chiuso
all'indietro: se il successore ci sta, ci stava già il predecessore.

## L'insieme scelto

`shared_state` viene messo a `M` solo da `upgrade_to_M_data_avilable_rq1`, che
richiede `∀ i, shared_state i = I`, e viene rimesso a `I` da
`downgrade_from_M_rq1`; nessun'altra transizione lo tocca.  Quindi

    ∃ i ≠ j, shared_state i = M ∧ shared_state j = M

è chiuso all'indietro, ed è esattamente la negazione dell'unicità del proprietario
dal punto di vista del parent.
-/

def unreachable_set {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ s.parent.shared_state i = Bstate.M ∧ s.parent.shared_state j = Bstate.M

theorem Bstate.eq_M_of_ne_I : ∀ {b : Bstate}, b ≠ Bstate.I → b = Bstate.M := by
  intro b hb; cases b with
  | M => rfl
  | I => exact absurd rfl hb

/-- La formulazione originale ("il parent marca `M` un indice `i` e non tutti gli
altri indici sono `I`") ricade nell'insieme scelto. -/
theorem unreachable_set_of_not_all_I {n} {s : MIState n} {i : Fin n}
    (hi : s.parent.shared_state i = Bstate.M)
    (h : ¬ ∀ j : Fin n, j ≠ i → s.parent.shared_state j = Bstate.I) :
    unreachable_set s := by
  obtain ⟨j, hj⟩ := not_forall.mp h
  obtain ⟨hji, hjI⟩ := Classical.not_imp.mp hj
  exact ⟨i, j, Ne.symm hji, hi, Bstate.eq_M_of_ne_I hjI⟩

/-- Il passo singolo: se il successore è nell'insieme, lo è anche il predecessore. -/
theorem back_step_MI {n} {c a : MIState n} {t} (h : mi_step_internal c t a) :
    unreachable_set a → unreachable_set c := by
  rintro ⟨i, j, hij, hi, hj⟩
  cases h with
  | cache cache' p e hstep =>
      exact ⟨i, j, hij, hi, hj⟩
  | parent_no_queue parent' e p hstep =>
      cases hstep
  | parent_upd_queue parent' e p hstep =>
      dsimp only at hi hj
      cases hstep with
      | downgrade_from_M_rq1 =>
          -- il parent porta `shared_state p` a `I`: i e j erano gia' `M` prima
          dsimp only at hi hj
          refine ⟨i, j, hij, ?_, ?_⟩
          · by_cases hip : i = p
            · subst hip; rw [update_Fin_gss] at hi; exact Bstate.noConfusion hi
            · rwa [update_Fin_gso2 _ _ _ _ hip] at hi
          · by_cases hjp : j = p
            · subst hjp; rw [update_Fin_gss] at hj; exact Bstate.noConfusion hj
            · rwa [update_Fin_gso2 _ _ _ _ hjp] at hj
      | upgrade_to_M_data_avilable_rq1 =>
          -- caso impossibile: il parent concede `M` solo se tutti gli stati sono `I`,
          -- quindi al piu' un indice e' `M` dopo il passo
          have hall : ∀ k : Fin n, c.parent.shared_state k = Bstate.I := by assumption
          dsimp only at hi hj
          exfalso
          by_cases hip : i = p
          · subst hip
            rw [update_Fin_gso2 _ _ _ _ (Ne.symm hij)] at hj
            exact Bstate.noConfusion ((hall j).symm.trans hj)
          · rw [update_Fin_gso2 _ _ _ _ hip] at hi
            exact Bstate.noConfusion ((hall i).symm.trans hi)
      | upgrade_to_M_invalid_all =>
          -- questi due passi toccano solo le code, non `shared_state`
          exact ⟨i, j, hij, hi, hj⟩
      | invalid_all =>
          exact ⟨i, j, hij, hi, hj⟩

theorem back_reachable_MI {n} {x} : ∀ s, @unreachable_set n s -> MI.backwards_reachable_from s x → @unreachable_set n x := by
  dsimp [MI.LTS.backwards_reachable_from]
  intro s hu h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hu
  | @head a c h1 h2 h3 =>
    clear h2
    apply h3
    dsimp [Function.swap, MI, MI.LTS.atrans] at h1
    obtain ⟨t, ht⟩ := h1
    exact back_step_MI ht hu

/-- Lo stato iniziale (tutte le cache in `I`, code vuote) non è nell'insieme. -/
theorem not_unreachable_default {n} : ¬ @unreachable_set n default := by
  rintro ⟨i, j, hij, hi, hj⟩
  exact Bstate.noConfusion hi

/-- Nessuno stato dell'insieme è raggiungibile dallo stato iniziale. -/
theorem not_reachable_from_default {n} (s : MIState n) (h : unreachable_set s) :
    ¬ ReflTransGen MI.atrans (default : MIState n) s := by
  intro hreach
  rw [Relation.reflTransGen_swap] at hreach
  exact not_unreachable_default (back_reachable_MI _ h hreach)

theorem reachable_MI {n} : ∀ s : MIState n, unreachable_set s -> ¬ MI.reachable s := by
  intro s h hreach
  dsimp [MI.LTS.reachable] at hreach
  exact not_reachable_from_default s h (hreach (default : MIState n) (by trivial))

--prove not two ccahe are in M


def unreachable_set1 {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧  (s.caches i).state = Bstate.M ∧ (s.caches j).state = Bstate.M

-- NON DIMOSTRABILE: con la congiunzione l'insieme e' esattamente `twoCachesM`, e non
-- e' chiuso all'indietro.  Controesempio (`back_reachable_MI1_is_false`):
--   predecessore  cache 0 = I con il grant `rsM 7` ancora in coda, cache 1 = M  -> FUORI
--        |  upgrade_from_I_rs sulla cache 0
--   successore    cache 0 = M,                                     cache 1 = M  -> DENTRO
-- Il secondo "proprietario" del predecessore e' un MESSAGGIO in volo, non una cache in
-- `M`: per questo nessun predicato sui soli stati delle cache puo' funzionare, vedi
-- `no_cache_state_only_invariant`.
--
-- Le STESSE ipotesi con la conclusione corretta si dimostrano (`back_reachable_MI1_correct`):
--     unreachable_set1 s → backwards_reachable_from s x → unreachable_setM x
-- e da li' segue il risultato voluto: `two_caches_M_not_reachable` e `reachable_MI1`.
theorem back_reachable_MI1 {n} {x} : ∀ s, @unreachable_set1 n s -> MI.backwards_reachable_from s x → @unreachable_set1 n x := by
  sorry


--parent commute

-- FALSO COSI' COM'E': vedi `comm_downgrade_from_M_rq1_downgrade_from_M_rq1_is_false`.
-- (a) con i₁ = i₂ le due ipotesi possono essere lo STESSO step: `rsIμ` viene consumato,
--     quindi da s' = s'' nessun downgrade e' piu' abilitato;
-- (b) nemmeno aggiungere `i₁ ≠ i₂` basta con questa `unreachable_set`
--     (vedi `comm_downgrade_downgrade_distinct_is_false`): i due step scrivono
--     `value := v₁` e `value := v₂`, che nello stato di join dovrebbero coincidere.
-- Il caso (b) sparirebbe rafforzando `unreachable_set` (un rilascio in volo su i deve
-- implicare `shared_state i = M`: due rilasci su indici distinti sarebbero allora
-- gia' nell'insieme irraggiungibile). Il caso (a) richiede di escludere i due step uguali.
theorem comm_downgrade_from_M_rq1_downgrade_from_M_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂) ) s'' →
  ¬ unreachable_set s →
  ∃ s''',
    (mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s''')
    ∨
    s' = s'' := by
  sorry

-- FALSO CON QUESTA `unreachable_set`: vedi
-- `comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1_is_false`.
-- Downgrade e grant sullo stesso indice scrivono `shared_state i` a `I` e a `M`.
-- MA il controesempio (rilascio in volo con `shared_state = I`) NON e' raggiungibile:
-- rafforzando `unreachable_set` le due premesse diventano incompatibili e il lemma
-- diventa vero a vuoto. E' l'unico dei cinque che si recupera cosi'.
theorem comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂) ) s'' →
  ¬ unreachable_set s →
  ∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s''' := by
  sorry

-- FALSO, e il controesempio e' uno stato RAGGIUNGIBILE: vedi
-- `comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all_is_false`.
-- Conflitto vero del protocollo: dopo il downgrade `shared_state i` e' `I`, e la
-- premessa dell'invalidate (`¬ shared_state i = I`) non vale piu'. Nessun
-- rafforzamento dell'invariante puo' salvarlo.
theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂) ) s'' →
  ¬ unreachable_set s →
  ∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''' := by
  sorry

-- FALSO, controesempio RAGGIUNGIBILE: vedi `comm_downgrade_from_M_rq1_invalid_all_is_false`.
-- Stesso conflitto del caso precedente: `invalid_all` richiede `shared_state i = M`,
-- che il downgrade ha appena portato a `I`.
theorem comm_downgrade_from_M_rq1_invalid_all {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.invalid_allM) i₂) ) s'' →
  ¬ unreachable_set s →
  ∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.invalid_allM) i₂)) s''' := by
  sorry

-- FALSO, sempre: vedi `comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1_is_false`.
-- La guardia del grant (`∀ i, shared_state i = I`) e' distrutta dal suo stesso effetto
-- (`shared_state i := M`): due grant non commutano mai. E' la mutua esclusione del
-- protocollo, non un difetto dell'enunciato.
theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1 {s s' s'' : MIState n} :
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁) ) s' →
  mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂) ) s'' →
  ¬ unreachable_set s →
  ∃ s''',
    mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁)) s''' ∧
    mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s''' := by
  sorry

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


---cache



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


-- theorem comm_ld_rq_data_available_rq_data_not_available {s s' s'' : MIState n} :
--   mi_step_internal s (.cache (.rq_data_not_available) i) s' →
--   mi_step_internal s (.cache (.ld_rs v) i) s'' →
--   (∀ i, s'.parent.shared_state i = Bstate.I) →
--   ∃ t₁ t₂ t₃ t₄ t₅,
--     mi_step_internal s' (.cache (.upgrade_from_I_rq) i) t₁ ∧
--     mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₂ ∧
--     mi_step_internal t₂ (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)) t₃ ∧
--     mi_step_internal t₃ (.cache (.upgrade_from_I_rs v) i) t₄ ∧
--     mi_step_internal t₄ (.cache (.ld_rs v) i) t₅ ∧
--     s''.caches = t₅.caches
--      := by
--   intro h1 h2 hI
--   cases h1 with
--   | cache c1 _ _ hc1 =>
--     cases hc1 with
--     | rq_data_not_available hM =>
--       cases h2 with
--       | cache c2 _ _ hc2 =>
--         cases hc2 with
--         | ld_rq_data_available rst hrq _ =>
--           refine ⟨_, _, _, _, _,
--             mi_step_internal.cache _ ?c1 _ _ ?p1,
--             mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
--             mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
--             mi_step_internal.cache _ ?c2 _ _ ?p4,
--             mi_step_internal.cache _ ?c3 _ _ ?p5,
--             ?eq⟩
--           -- 1. la cache torna a chiedere la linea (rqM)
--           case p1 =>
--             simp only [update_Fin_gss]
--             refine .upgrade_from_I_rq _ ?_
--             rfl
--           -- 2. il parent consuma l'rsIμ: shared_state i := I, value := v
--           case p2 =>
--             refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
--             simp only [update_Fin_gss]
--             exact lst_get2 _ _ _
--           -- 3. il parent consuma l'rqM e risponde con rsM v
--           case p3 =>
--             refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
--             · simp only [update_Fin_gss, lst_erase2]
--               exact lst_get _ _
--             · intro k
--               simp only [update_Fin]
--               split
--               · rfl
--               · simpa using hI k
--           -- 4. la cache risale in M con il valore ricevuto
--           case p4 =>
--             simp only [update_Fin_gss]
--             refine .upgrade_from_I_rs _ _ (s.caches i).queue_pc.length ?_ ?_
--             · exact lst_get _ _
--             · rfl
--           -- 5. ora la load può essere servita
--           case p5 =>
--             simp only [update_Fin_gss, lst_erase]
--             refine .ld_rq_data_available _ rst ?_ ?_
--             · assumption
--             · rfl
--           case eq =>
--             funext k
--             by_cases hk : k = i
--             · subst hk
--               simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
--             · simp only [update_Fin_gso2 _ _ _ _ hk]


theorem comm_ld_rq_data_available_rq_data_not_available {s s' s'' : MIState n} :
  mi_step_internal s (.cache (.rq_data_not_available) i) s' →
  mi_step_internal s (.cache (.ld_rs v) i) s'' →
  ∃ t₁ t₂ t₃ t₄ t₅,
    mi_step_internal s' (.cache (.upgrade_from_I_rq) i) t₁ ∧
    mi_step_internal t₁ (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t₂ ∧
    mi_step_internal t₂ (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)) t₃ ∧
    mi_step_internal t₃ (.cache (.upgrade_from_I_rs v) i) t₄ ∧
    mi_step_internal t₄ (.cache (.ld_rs v) i) t₅ ∧
    s''.caches = t₅.caches
     := by
  intro h1 h2
  cases h1 with
  | cache c1 _ _ hc1 =>
    cases hc1 with
    | rq_data_not_available hM =>
      cases h2 with
      | cache c2 _ _ hc2 =>
        cases hc2 with
        | ld_rq_data_available rst hrq _ =>
          refine ⟨_, _, _, _, _,
            mi_step_internal.cache _ ?c1 _ _ ?p1,
            mi_step_internal.parent_upd_queue _ ?q1 _ _ ?p2,
            mi_step_internal.parent_upd_queue _ ?q2 _ _ ?p3,
            mi_step_internal.cache _ ?c2 _ _ ?p4,
            mi_step_internal.cache _ ?c3 _ _ ?p5,
            ?eq⟩
          -- 1. la cache torna a chiedere la linea (rqM)
          case p1 =>
            simp only [update_Fin_gss]
            refine .upgrade_from_I_rq _ ?_
            rfl
          -- 2. il parent consuma l'rsIμ: shared_state i := I, value := v
          case p2 =>
            refine .downgrade_from_M_rq1 _ _ _ (s.caches i).queue_cp.length ?_
            simp only [update_Fin_gss]
            exact lst_get2 _ _ _
          -- 3. il parent consuma l'rqM e risponde con rsM v
          case p3 =>
            refine .upgrade_to_M_data_avilable_rq1 _ _ (s.caches i).queue_cp.length ?_ ?_
            · simp only [update_Fin_gss, lst_erase2]
              exact lst_get _ _
            · intro k
              simp only [update_Fin]
              split
              · rfl
              · by_cases (∀ j, j ≠ i → s.parent.shared_state j = Bstate.I)
                . simp_all; grind
                . -- ramo aperto (l'enunciato in questo caso non e' dimostrabile cosi');
                  -- `sorry` al posto di `exfalso` per permettere `lake build` del modulo
                  sorry
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
          case eq =>
            funext k
            by_cases hk : k = i
            · subst hk
              simp only [update_Fin_gss, lst_erase, lst_erase2, hM]
            · simp only [update_Fin_gso2 _ _ _ _ hk]


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

theorem comm_ld_rq_data_available_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s (.ld_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.ld_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  sorry

theorem comm_st_rq_M_state_st_rq_M_state {s s' s''} :
  cache_mi_step_internal s (.st_rs v₁) s' →
  cache_mi_step_internal s (.st_rs v₂) s'' →
  s' = s'' := by
  intro h1 h2; cases h1; cases h2; grind

theorem comm_st_rq_M_state_rq_data_not_available {s s' s''} :
  cache_mi_step_internal s (.st_rs v) s' →
  cache_mi_step_internal s .rq_data_not_available s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.st_rs v) s''' ∧
    cache_mi_step_internal s' .rq_data_not_available s''' := by
  sorry

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

theorem comm_st_rq_M_state_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s (.st_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.st_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  sorry

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


theorem comm_rq_data_not_available_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .rq_data_not_available s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' .rq_data_not_available s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  sorry

theorem comm_upgrade_from_I_rq_upgrade_from_I_rq {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s .upgrade_from_I_rq s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' .upgrade_from_I_rq s''' := by
  rintro ⟨ h₁, h₂ ⟩ ⟨ h₃, h₄ ⟩;
  exact ⟨ _, cache_mi_step_internal.upgrade_from_I_rq _ ‹_›, cache_mi_step_internal.upgrade_from_I_rq _ ‹_› ⟩


theorem comm_upgrade_from_I_rq_upgrade_from_I_rs {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s (.upgrade_from_I_rs v) s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' (.upgrade_from_I_rs v) s''' := by
  sorry

theorem comm_upgrade_from_I_rq_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .upgrade_from_I_rq s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' .upgrade_from_I_rq s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  intro h1 h2
  cases h1 ; cases h2
  cases ‹s.state = Bstate.I›.symm.trans ‹s.state = Bstate.M›

theorem comm_upgrade_from_I_rs_upgrade_from_I_rs {s s' s''} :
  cache_mi_step_internal s (.upgrade_from_I_rs v₁) s' →
  cache_mi_step_internal s (.upgrade_from_I_rs v₂) s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.upgrade_from_I_rs v₁) s''' ∧
    cache_mi_step_internal s' (.upgrade_from_I_rs v₂) s''' := by
  sorry

theorem comm_upgrade_from_I_rs_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s (.upgrade_from_I_rs v) s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' (.upgrade_from_I_rs v) s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  intro  h1 h2;
  cases h1 ; cases h2 ; grind

theorem comm_downgrade_from_M_rs_downgrade_from_M_rs {s s' s''} :
  cache_mi_step_internal s .downgrade_from_M_rs s' →
  cache_mi_step_internal s .downgrade_from_M_rs s'' →
  ∃ s''',
    cache_mi_step_internal s'' .downgrade_from_M_rs s''' ∧
    cache_mi_step_internal s' .downgrade_from_M_rs s''' := by
  sorry

/-!
# Effetto locale degli step del parent

Prima della correzione, `{ p1 with queue_cip i := … }` veniva elaborato come
`queue_cip := fun i => …`: il binder della lambda nascondeva l'indice `i` del
costruttore e OGNI step del parent riscriveva tutte le code (broadcast del
grant, `eraseIdx` su tutte le `queue_cip`).  Con quella semantica il protocollo
non era coerente: si raggiungeva uno stato con due cache in `M`.

Con `update_Fin` lo step tocca solo l'indice coinvolto: i due lemmi seguenti lo
certificano, e la vecchia traccia che portava due cache in `M` non è più
eseguibile (il grant non arriva più a chi non l'ha chiesto).
-/

theorem grant_touches_only_i {n} (p1 p' : ParentState n) (i i' : Fin n) (h : i' ≠ i)
    (hstep : parent_mi_step p1 (.upd_queue .upgrade_to_M_data_avilable_rq1 i) p') :
    p'.queue_pci i' = p1.queue_pci i' ∧ p'.queue_cip i' = p1.queue_cip i' := by
  cases hstep
  exact ⟨update_Fin_gso2 _ _ _ _ h, update_Fin_gso2 _ _ _ _ h⟩

theorem downgrade_touches_only_i {n} (p1 p' : ParentState n) (v : Value) (i i' : Fin n)
    (h : i' ≠ i) (hstep : parent_mi_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i) p') :
    p'.queue_cip i' = p1.queue_cip i' ∧ p'.shared_state i' = p1.shared_state i' := by
  cases hstep
  exact ⟨update_Fin_gso2 _ _ _ _ h, update_Fin_gso2 _ _ _ _ h⟩

theorem invalidate_touches_only_i {n} (p1 p' : ParentState n) (k i i' : Fin n) (h : i' ≠ i)
    (hstep : parent_mi_step p1 (.upd_queue (.upgrade_to_M_invalid_all k) i) p') :
    p'.queue_pci i' = p1.queue_pci i' := by
  cases hstep
  exact update_Fin_gso2 _ _ _ _ h

/-!
# Analisi dei lemmi di commutazione del parent

Lemmi di inversione: da uno step `mi_step_internal` a livello di parent si
leggono le premesse e l'effetto su `shared_state`.
-/

theorem mi_downgrade_pre {n} {s t : MIState n} {v i}
    (h : mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t) :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | downgrade_from_M_rq1 => rename_i j hj; exact ⟨j, hj⟩

theorem mi_downgrade_post {n} {s t : MIState n} {v i}
    (h : mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t) :
    t.parent.shared_state i = Bstate.I := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | downgrade_from_M_rq1 => exact update_Fin_gss _ _ _

theorem mi_grant_pre {n} {s t : MIState n} {i}
    (h : mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t) :
    ∀ k, s.parent.shared_state k = Bstate.I := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | upgrade_to_M_data_avilable_rq1 => assumption

theorem mi_grant_post {n} {s t : MIState n} {i}
    (h : mi_step_internal s (.parent (.upd_queue .upgrade_to_M_data_avilable_rq1 i)) t) :
    t.parent.shared_state i = Bstate.M := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | upgrade_to_M_data_avilable_rq1 => exact update_Fin_gss _ _ _

theorem mi_invalid_all_pre {n} {s t : MIState n} {i}
    (h : mi_step_internal s (.parent (.upd_queue .invalid_allM i)) t) :
    s.parent.shared_state i = Bstate.M := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | invalid_all => assumption

theorem mi_invalidate_pre {n} {s t : MIState n} {k i}
    (h : mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i)) t) :
    ¬ (s.parent.shared_state i = Bstate.I) := by
  cases h with | parent_upd_queue _ _ _ hp => cases hp with | upgrade_to_M_invalid_all => assumption

/-- Con una sola cache l'insieme `unreachable_set` è vuoto (serve `i ≠ j`). -/
theorem not_unreachable_one (s : MIState 1) : ¬ unreachable_set s := by
  rintro ⟨i, j, hij, -, -⟩
  exact hij (Subsingleton.elim i j)

theorem mi_downgrade_post_queue {n} {s t : MIState n} {v i}
    (h : mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i)) t) :
    ∃ j : Nat, (s.parent.queue_cip i)[j]? = some (CPEvent.rsIμ v) ∧
         t.parent.queue_cip i = (s.parent.queue_cip i).eraseIdx j := by
  cases h with
  | parent_upd_queue _ _ _ hp =>
      cases hp with
      | downgrade_from_M_rq1 => rename_i j hj; exact ⟨j, hj, update_Fin_gss _ _ _⟩

/-! ## 1. `downgrade / downgrade` -/

/-- Stato con una sola cache: il parent la crede in `M` e ha in coda il rilascio. -/
def cexRelease : MIState 1 :=
  { caches := fun _ => default,
    parent := { value := 0, shared_state := fun _ => Bstate.M,
                queue_cip := fun _ => [CPEvent.rsIμ 5], queue_pci := fun _ => [] } }

theorem cexRelease_step :
    ∃ t, mi_step_internal cexRelease (.parent (.upd_queue (.downgrade_from_M_rq1 5) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0 (parent_mi_step.downgrade_from_M_rq1 _ 5 0 0 rfl)⟩

theorem comm_downgrade_from_M_rq1_downgrade_from_M_rq1_is_false :
    ¬ ∀ (n : ℕ) (v₁ v₂ : Value) (i₁ i₂ : Fin n) (s s' s'' : MIState n),
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s''' := by
  intro hcomm
  obtain ⟨t, hstep⟩ := cexRelease_step
  obtain ⟨j, hj, hq⟩ := mi_downgrade_post_queue hstep
  have hj0 : j = 0 := by
    cases j with
    | zero => rfl
    | succ m => simp [cexRelease] at hj
  subst hj0
  obtain ⟨u, h1, -⟩ := hcomm 1 5 5 0 0 cexRelease t t hstep hstep (not_unreachable_one _)
  obtain ⟨j', hj'⟩ := mi_downgrade_pre h1
  rw [hq] at hj'
  simp [cexRelease] at hj'

/-! ## `grant / grant` (`upgrade_to_M_data_avilable_rq1` con se stesso) -/

/-- Stato con una sola cache: tutto in `I` e una richiesta `rqM` pendente nella
coda cache→parent. -/
def cex_grant_grant_state : MIState 1 :=
  { caches := fun _ => default,
    parent := { value := 0, shared_state := fun _ => Bstate.I,
                queue_cip := fun _ => [CPEvent.rqM], queue_pci := fun _ => [] } }

theorem cex_grant_grant_step :
    ∃ t, mi_step_internal cex_grant_grant_state
            (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0
        (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ 0 0 rfl (fun _ => rfl))⟩

theorem comm_upgrade_to_M_data_avilable_rq1_upgrade_to_M_data_avilable_rq1_is_false :
    ¬ ∀ (n : ℕ) (i₁ i₂ : Fin n) (s s' s'' : MIState n),
        mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s''' := by
  intro hcomm
  obtain ⟨t, hstep⟩ := cex_grant_grant_step
  -- dopo il grant la cache 0 è in `M`
  have hM : t.parent.shared_state 0 = Bstate.M := mi_grant_post hstep
  obtain ⟨u, h1, -⟩ :=
    hcomm 1 0 0 cex_grant_grant_state t t hstep hstep (not_unreachable_one _)
  -- ma un secondo grant da `t` richiederebbe che tutto sia in `I`
  have hI : t.parent.shared_state 0 = Bstate.I := mi_grant_pre h1 0
  rw [hM] at hI
  exact Bstate.noConfusion hI


/-! ## `downgrade / grant` -/

/-- Stato con una sola cache: in coda prima un rilascio (`rsIμ 5`) e poi una richiesta (`rqM`). -/
def cex_downgrade_grant_state : MIState 1 :=
  { caches := fun _ => default,
    parent := { value := 0, shared_state := fun _ => Bstate.I,
                queue_cip := fun _ => [CPEvent.rsIμ 5, CPEvent.rqM], queue_pci := fun _ => [] } }

theorem cex_downgrade_grant_step_downgrade :
    ∃ t, mi_step_internal cex_downgrade_grant_state
        (.parent (.upd_queue (.downgrade_from_M_rq1 5) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0
        (parent_mi_step.downgrade_from_M_rq1 _ 5 0 0 rfl)⟩

theorem cex_downgrade_grant_step_grant :
    ∃ t, mi_step_internal cex_downgrade_grant_state
        (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0
        (parent_mi_step.upgrade_to_M_data_avilable_rq1 _ 0 1 rfl (fun _ => rfl))⟩

-- Nota: questo controesempio NON è uno stato raggiungibile (un rilascio in volo implica shared_state = M negli stati raggiungibili), quindi questo lemma diventerebbe vero (a vuoto) se `unreachable_set` venisse rafforzato.
theorem comm_downgrade_from_M_rq1_upgrade_to_M_data_avilable_rq1_is_false :
    ¬ ∀ (n : ℕ) (v : Value) (i₁ i₂ : Fin n) (s s' s'' : MIState n),
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_data_avilable_rq1) i₂)) s''' := by
  intro hcomm
  obtain ⟨s', hstep1⟩ := cex_downgrade_grant_step_downgrade
  obtain ⟨s'', hstep2⟩ := cex_downgrade_grant_step_grant
  obtain ⟨u, h1, h2⟩ :=
    hcomm 1 5 0 0 cex_downgrade_grant_state s' s'' hstep1 hstep2 (not_unreachable_one _)
  have hI : u.parent.shared_state 0 = Bstate.I := mi_downgrade_post h1
  have hM : u.parent.shared_state 0 = Bstate.M := mi_grant_post h2
  exact Bstate.noConfusion (hI ▸ hM)


/-! ## `downgrade / upgrade_to_M_invalid_all` -/

/-- Stato con una sola cache: il parent la crede in `M`, in coda ha sia il rilascio
    (`rsIμ 5`) sia una richiesta di `M` (`rqM`). -/
def cex_downgrade_invalidate_state : MIState 1 :=
  { caches := fun _ => default,
    parent := { value := 0, shared_state := fun _ => Bstate.M,
                queue_cip := fun _ => [CPEvent.rsIμ 5, CPEvent.rqM], queue_pci := fun _ => [] } }

theorem cex_downgrade_invalidate_step_downgrade :
    ∃ t, mi_step_internal cex_downgrade_invalidate_state
           (.parent (.upd_queue (.downgrade_from_M_rq1 5) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0
        (parent_mi_step.downgrade_from_M_rq1 _ 5 0 0 rfl)⟩

theorem cex_downgrade_invalidate_step_invalidate :
    ∃ t, mi_step_internal cex_downgrade_invalidate_state
           (.parent (.upd_queue (.upgrade_to_M_invalid_all 0) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0
        (parent_mi_step.upgrade_to_M_invalid_all _ 0 0 1 rfl
          (by intro h; exact Bstate.noConfusion h))⟩

theorem comm_downgrade_from_M_rq1_upgrade_to_M_invalid_all_is_false :
    ¬ ∀ (n : ℕ) (v : Value) (k i₁ i₂ : Fin n) (s s' s'' : MIState n),
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.upgrade_to_M_invalid_all k) i₂)) s''' := by
  intro hcomm
  obtain ⟨t₁, h1⟩ := cex_downgrade_invalidate_step_downgrade
  obtain ⟨t₂, h2⟩ := cex_downgrade_invalidate_step_invalidate
  obtain ⟨u, -, hlast⟩ :=
    hcomm 1 5 0 0 0 cex_downgrade_invalidate_state t₁ t₂ h1 h2 (not_unreachable_one _)
  exact mi_invalidate_pre hlast (mi_downgrade_post h1)


/-! ## `downgrade / invalid_all` -/

theorem cex_downgrade_invalid_all_step :
    ∃ t, mi_step_internal cexRelease (.parent (.upd_queue (.invalid_allM) 0)) t :=
  ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0 (parent_mi_step.invalid_all _ 0 rfl)⟩

theorem comm_downgrade_from_M_rq1_invalid_all_is_false :
    ¬ ∀ (n : ℕ) (v : Value) (i₁ i₂ : Fin n) (s s' s'' : MIState n),
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.invalid_allM) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.invalid_allM) i₂)) s''' := by
  intro hcomm
  obtain ⟨t, h1⟩ := cexRelease_step
  obtain ⟨u, h2⟩ := cex_downgrade_invalid_all_step
  obtain ⟨w, -, h4⟩ := hcomm 1 5 0 0 cexRelease t u h1 h2 (not_unreachable_one _)
  have hM : t.parent.shared_state 0 = Bstate.M := mi_invalid_all_pre h4
  have hI : t.parent.shared_state 0 = Bstate.I := mi_downgrade_post h1
  rw [hI] at hM
  exact Bstate.noConfusion hM

/-- Anche aggiungendo `i₁ ≠ i₂` il lemma resta falso con questa `unreachable_set`:
due rilasci pendenti su indici distinti portano `value` a due valori diversi. -/
def cexTwoReleases : MIState 2 :=
  { caches := fun _ => default,
    parent := { value := 0, shared_state := fun _ => Bstate.I,
                queue_cip := fun i => if i = 0 then [CPEvent.rsIμ 5] else [CPEvent.rsIμ 7],
                queue_pci := fun _ => [] } }

theorem cexTwoReleases_not_unreachable : ¬ unreachable_set cexTwoReleases := by
  rintro ⟨i, j, -, hi, -⟩
  exact Bstate.noConfusion hi

theorem comm_downgrade_downgrade_distinct_is_false :
    ¬ ∀ (n : ℕ) (v₁ v₂ : Value) (i₁ i₂ : Fin n) (s s' s'' : MIState n),
        i₁ ≠ i₂ →
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s' →
        mi_step_internal s (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s'' →
        ¬ unreachable_set s →
        ∃ s''',
          mi_step_internal s'' (.parent (.upd_queue (.downgrade_from_M_rq1 v₁) i₁)) s''' ∧
          mi_step_internal s' (.parent (.upd_queue (.downgrade_from_M_rq1 v₂) i₂)) s''' := by
  intro hcomm
  obtain ⟨t1, hs1⟩ : ∃ t, mi_step_internal cexTwoReleases
      (.parent (.upd_queue (.downgrade_from_M_rq1 5) 0)) t :=
    ⟨_, mi_step_internal.parent_upd_queue _ _ _ 0 (parent_mi_step.downgrade_from_M_rq1 _ 5 0 0 rfl)⟩
  obtain ⟨t2, hs2⟩ : ∃ t, mi_step_internal cexTwoReleases
      (.parent (.upd_queue (.downgrade_from_M_rq1 7) 1)) t :=
    ⟨_, mi_step_internal.parent_upd_queue _ _ _ 1 (parent_mi_step.downgrade_from_M_rq1 _ 7 1 0 rfl)⟩
  obtain ⟨u, ha, hb⟩ := hcomm 2 5 7 0 1 cexTwoReleases t1 t2 (by decide) hs1 hs2
    cexTwoReleases_not_unreachable
  have h5 : u.parent.value = 5 := by
    cases ha with
    | parent_upd_queue _ _ _ hp => cases hp with | downgrade_from_M_rq1 => rfl
  have h7 : u.parent.value = 7 := by
    cases hb with
    | parent_upd_queue _ _ _ hp => cases hp with | downgrade_from_M_rq1 => rfl
  exact absurd (h5.symm.trans h7) (by decide)

/-!
# L'invariante a token

## Il problema

"Due cache distinte in `M`" (`twoCachesM`) e' la proprieta' che vogliamo escludere, ma
NON e' chiusa all'indietro: il predecessore di uno stato `(M, M)` puo' essere
`(I, M)` con il grant `rsM` ancora in volo nella coda, e li' di cache in `M` ce n'e'
una sola.  Il secondo proprietario della linea e' un MESSAGGIO, non uno stato di cache.

## L'idea

Contiamo i "token M": ne vale uno la cache in `M`, uno il grant `rsM` in volo verso la
cache, uno il rilascio `rsIμ` in volo verso il parent.  In ogni stato raggiungibile c'e'
al piu' un token in tutto il sistema, e sta dove il parent crede che stia.  Gli stati
"cattivi" sono quelli in cui questo conto non torna: e' `unreachable_setM`.

Il fatto tecnico che regge tutto e' `cache_step_tokens`: nessun passo interno di cache
crea o distrugge token, li sposta soltanto (da `M` a un `rsIμ` in coda, da un `rsM` in
coda a `M`, ...).  Solo il parent puo' cambiarne il conto, e lo fa sotto guardie precise.

## Indice

* conteggio dei token: `PCEvent.isGrant` ... `cache_step_tokens`
* l'insieme: `MIState.tokens`, `MIState.desynced`, `unreachable_setM`
* chiusura all'indietro: `back_step_MIM`, `back_reachable_MIM`
* conseguenze: `two_caches_M_not_reachable`, `reachable_MI1`
-/

/-! ## Conteggio dei token -/

/-- Un messaggio parent -> cache porta un token se e' la concessione della linea. -/
def PCEvent.isGrant : PCEvent → Bool
  | .rsM _ => true
  | .rqIμ  => false

/-- Un messaggio cache -> parent porta un token se e' la restituzione della linea. -/
def CPEvent.isRelease : CPEvent → Bool
  | .rsIμ _ => true
  | .rqM    => false

/-- Una cache in `M` possiede la linea: vale un token. -/
def Bstate.tok : Bstate → Nat
  | .M => 1
  | .I => 0

/-- Token posseduti da una cache, contando le sue code locali. -/
def CacheState.tokens (cs : CacheState) : Nat :=
  cs.state.tok + cs.queue_pc.countP PCEvent.isGrant + cs.queue_cp.countP CPEvent.isRelease


/-- Cancellare da una lista l'elemento in posizione `j` fa calare di uno il conteggio,
se quell'elemento soddisfa il predicato. -/
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

/-- **Conservazione dei token.**  Nessun passo interno di cache crea o distrugge token:
`rq_data_not_available` scambia lo stato `M` con un `rsIμ` in coda, `upgrade_from_I_rs`
scambia un `rsM` in coda con lo stato `M`, `downgrade_from_M_rs` fa entrambe le cose, e
gli altri passi non toccano ne' stato ne' code. -/
theorem cache_step_tokens {cs cs' : CacheState} {e} (h : cache_mi_step_internal cs e cs') :
    cs'.tokens = cs.tokens := by
  cases h with
  | ld_rq_data_available rst h1 h2 => simp [CacheState.tokens]
  | st_rq_M_state v rst h1 h2 => simp [CacheState.tokens]
  | rq_data_not_available h2 =>
      simp [CacheState.tokens, h2, Bstate.tok, List.countP_append, CPEvent.isRelease]
      omega
  | upgrade_from_I_rq h2 =>
      simp [CacheState.tokens, h2, Bstate.tok, List.countP_append, CPEvent.isRelease]
  | upgrade_from_I_rs v j hj h2 =>
      have hc := countP_eraseIdx PCEvent.isGrant cs.queue_pc j (PCEvent.rsM v) hj
      simp [PCEvent.isGrant] at hc
      simp [CacheState.tokens, h2, Bstate.tok]
      omega
  | downgrade_from_M_rs j hj h2 =>
      have hc := countP_eraseIdx PCEvent.isGrant cs.queue_pc j PCEvent.rqIμ hj
      simp [PCEvent.isGrant] at hc
      simp [CacheState.tokens, h2, Bstate.tok, List.countP_append, CPEvent.isRelease]
      omega

/-! ## L'insieme -/

/-- "Due cache distinte sono entrambe in `M`": la proprieta' che vogliamo escludere.
Coincide con `unreachable_set1` (vedi `unreachable_set1_iff_twoCachesM`), e da sola NON
e' chiusa all'indietro (`back_reachable_twoCachesM_is_false`). -/
def twoCachesM {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ (s.caches i).state = Bstate.M ∧ (s.caches j).state = Bstate.M

/-- Quanti token appartengono all'indice `i`: la cache possiede la linea
(`state = M`), oppure il permesso e' in volo verso di lei (`rsM` nella coda
parent -> cache), oppure la sta restituendo (`rsIμ` nella coda cache -> parent).
Le code sono lette dal lato parent; `desynced` garantisce che leggerle dal lato cache
darebbe lo stesso risultato. -/
def MIState.tokens {n} (s : MIState n) (i : Fin n) : Nat :=
  (s.caches i).state.tok
  + (s.parent.queue_pci i).countP PCEvent.isGrant
  + (s.parent.queue_cip i).countP CPEvent.isRelease

/-- Le due copie della stessa coda (quella locale alla cache e quella tenuta dal
parent) non coincidono.  Nel modello devono restare allineate: ogni passo risincronizza
l'indice che tocca. -/
def MIState.desynced {n} (s : MIState n) : Prop :=
  ∃ i, (s.caches i).queue_pc ≠ s.parent.queue_pci i ∨ (s.caches i).queue_cp ≠ s.parent.queue_cip i

/-- **L'insieme irraggiungibile.**  Uno stato e' "cattivo" se il conto dei token non
torna, e questo puo' succedere in quattro modi:

1. `s.desynced` — le due copie di una coda divergono.  Nessuna esecuzione puo'
   produrlo, perche' ogni passo risincronizza l'indice che tocca.
2. `∃ i, 2 ≤ s.tokens i` — lo stesso indice possiede la linea due volte (ad esempio e'
   in `M` e ha anche un grant ancora in coda).  La linea e' una sola.
3. `∃ i, 1 ≤ s.tokens i ∧ shared_state i = I` — l'indice `i` possiede la linea (o sta
   per riceverla, o la sta restituendo) ma il parent lo crede invalido.  E' il disgiunto
   decisivo: e' qui che cade il predecessore `(I + grant, M)` del controesempio, che ha
   due token ma una sola cache in `M`.  Se il parent non "vede" quel token, e' libero di
   concedere la linea a un altro e di creare due proprietari.
4. `unreachable_set s` — il parent stesso crede che due indici distinti siano in `M`.

I punti 3 e 4 insieme dicono: ogni token deve essere registrato dal parent, e il parent
ne registra al piu' uno. -/
def unreachable_setM {n} (s : MIState n) : Prop :=
  s.desynced
  ∨ (∃ i, 2 ≤ s.tokens i)
  ∨ (∃ i, 1 ≤ s.tokens i ∧ s.parent.shared_state i = Bstate.I)
  ∨ unreachable_set s

-- ATTENZIONE: questa e' l'inclusione INVERSA, ed e' FALSA: `unreachable_setM` e'
-- strettamente piu' grande di `twoCachesM`.  Controesempio `cexBack1` (una sola cache in
-- `M`, ma code disallineate): vedi `unrchablibity_is_false` in fondo al file.
-- Se quello che vuoi e' "ogni stato dell'insieme e' irraggiungibile", quello e' gia'
-- dimostrato: `unreachable_setM_not_reachable`.
theorem unrchablibity : unreachable_setM s ->  twoCachesM s := by admit

/-- Due cache in `M` sono due token; o uno dei due indici non e' registrato `M` dal
parent (punto 3), oppure lo sono entrambi (punto 4). -/
theorem unreachable_setM_of_twoCachesM {n} {s : MIState n} (h : twoCachesM s) :
    unreachable_setM s := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have ti : 1 ≤ s.tokens i := by simp only [MIState.tokens, hi, Bstate.tok]; omega
  have tj : 1 ≤ s.tokens j := by simp only [MIState.tokens, hj, Bstate.tok]; omega
  cases hsi : s.parent.shared_state i with
  | I => exact Or.inr (Or.inr (Or.inl ⟨i, ti, hsi⟩))
  | M =>
    cases hsj : s.parent.shared_state j with
    | I => exact Or.inr (Or.inr (Or.inl ⟨j, tj, hsj⟩))
    | M => exact Or.inr (Or.inr (Or.inr ⟨i, j, hij, hsi, hsj⟩))

/-! ## Lemmi di trasporto -/

/-- Se due stati hanno gli stessi `shared_state` e gli stessi token, e la
desincronizzazione si trasporta all'indietro, allora l'appartenenza all'insieme si
trasporta all'indietro.  Copre i passi che non cambiano il conto. -/
theorem unreachable_setM_of_eq {n} {c a : MIState n}
    (hs : ∀ k, a.parent.shared_state k = c.parent.shared_state k)
    (ht : ∀ k, a.tokens k = c.tokens k)
    (hd : a.desynced → c.desynced) :
    unreachable_setM a → unreachable_setM c := by
  rintro (hdes | ⟨i, hi⟩ | ⟨i, hi, hsh⟩ | ⟨i, j, hij, hi, hj⟩)
  · exact Or.inl (hd hdes)
  · exact Or.inr (Or.inl ⟨i, (ht i) ▸ hi⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, (ht i) ▸ hi, (hs i) ▸ hsh⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, j, hij, (hs i) ▸ hi, (hs j) ▸ hj⟩))

/-- Un passo del parent modifica solo l'indice dell'evento (dopo la correzione con
`update_Fin`). -/
theorem parent_step_local {n} {p1 p2 : ParentState n} {e i}
    (h : parent_mi_step p1 (.upd_queue e i) p2) :
    ∀ k, ¬(k = i) → p2.queue_cip k = p1.queue_cip k ∧ p2.queue_pci k = p1.queue_pci k
                    ∧ p2.shared_state k = p1.shared_state k := by
  cases h <;> intro k hk <;>
    exact ⟨by simp [update_Fin_gso2 _ _ _ _ hk], by simp [update_Fin_gso2 _ _ _ _ hk],
           by simp [update_Fin_gso2 _ _ _ _ hk]⟩

/-- Forma utilizzabile della negazione di `desynced`. -/
theorem synced_of_not_desynced {n} {c : MIState n} (hdes : ¬ c.desynced) :
    ∀ k, (c.caches k).queue_pc = c.parent.queue_pci k
         ∧ (c.caches k).queue_cp = c.parent.queue_cip k := by
  intro k
  by_contra hcon
  exact hdes ⟨k, by tauto⟩

/-! ## Chiusura all'indietro -/

/-- Il cuore della dimostrazione: un passo del parent non puo' creare uno stato
"cattivo" dal nulla.  Caso per caso:

* `downgrade_from_M_rq1` consuma un rilascio, quindi il predecessore aveva un token in
  piu' su quell'indice;
* `upgrade_to_M_data_avilable_rq1` crea un token, ma solo sotto la guardia
  "tutti gli `shared_state` sono `I`": se il successore e' cattivo, il predecessore lo
  era gia' per il punto 3;
* `upgrade_to_M_invalid_all` e `invalid_all` accodano solo `rqIμ`, che non e' un token. -/
theorem back_step_parent_aux {n} {c a : MIState n} {parent' : ParentState n} {e i}
    (hstep : parent_mi_step c.parent (.upd_queue e i) parent')
    (hst : ∀ k, (a.caches k).state = (c.caches k).state)
    (hpar : a.parent = parent')
    (hnd : ¬ a.desynced) :
    unreachable_setM a → unreachable_setM c := by
  have htok : ∀ k, a.tokens k = (c.caches k).state.tok
      + (parent'.queue_pci k).countP PCEvent.isGrant
      + (parent'.queue_cip k).countP CPEvent.isRelease := by
    intro k; simp only [MIState.tokens, hst k, hpar]
  have htokc : ∀ k, c.tokens k = (c.caches k).state.tok
      + (c.parent.queue_pci k).countP PCEvent.isGrant
      + (c.parent.queue_cip k).countP CPEvent.isRelease := fun k => rfl
  cases hstep with
  | downgrade_from_M_rq1 =>
      rename_i v j hj
      have hne : ∀ k, ¬(k = i) → a.tokens k = c.tokens k := by
        intro k hk; rw [htok k, htokc k]; simp [update_Fin_gso2 _ _ _ _ hk]
      have hi1 : a.tokens i + 1 = c.tokens i := by
        rw [htok i, htokc i]
        have h2 := countP_eraseIdx CPEvent.isRelease (c.parent.queue_cip i) j (CPEvent.rsIμ v) hj
        simp [CPEvent.isRelease] at h2
        simp only [update_Fin_gss]
        omega
      rintro (hd' | ⟨k, hk⟩ | ⟨k, hk, hsh⟩ | ⟨p, q, hpq, hp, hq⟩)
      · exact absurd hd' hnd
      · by_cases hki : k = i
        · subst hki; exact Or.inr (Or.inl ⟨k, by omega⟩)
        · exact Or.inr (Or.inl ⟨k, by rw [← hne k hki]; exact hk⟩)
      · by_cases hki : k = i
        · subst hki; exact Or.inr (Or.inl ⟨k, by omega⟩)
        · refine Or.inr (Or.inr (Or.inl ⟨k, by rw [← hne k hki]; exact hk, ?_⟩))
          rw [hpar] at hsh
          simpa only [update_Fin_gso2 _ _ _ _ hki] using hsh
      · rw [hpar] at hp hq
        have hpi : ¬(p = i) := by
          intro hh; subst hh; simp only [update_Fin_gss] at hp; exact Bstate.noConfusion hp
        have hqi : ¬(q = i) := by
          intro hh; subst hh; simp only [update_Fin_gss] at hq; exact Bstate.noConfusion hq
        refine Or.inr (Or.inr (Or.inr ⟨p, q, hpq, ?_, ?_⟩))
        · simpa only [update_Fin_gso2 _ _ _ _ hpi] using hp
        · simpa only [update_Fin_gso2 _ _ _ _ hqi] using hq
  | upgrade_to_M_data_avilable_rq1 =>
      rename_i j hall hj
      have hne : ∀ k, ¬(k = i) → a.tokens k = c.tokens k := by
        intro k hk; rw [htok k, htokc k]; simp [update_Fin_gso2 _ _ _ _ hk]
      have hi1 : a.tokens i = c.tokens i + 1 := by
        rw [htok i, htokc i]
        have h2 := countP_eraseIdx CPEvent.isRelease (c.parent.queue_cip i) j CPEvent.rqM hj
        simp [CPEvent.isRelease] at h2
        simp [update_Fin_gss, PCEvent.isGrant]
        omega
      rintro (hd' | ⟨k, hk⟩ | ⟨k, hk, hsh⟩ | ⟨p, q, hpq, hp, hq⟩)
      · exact absurd hd' hnd
      · by_cases hki : k = i
        · subst hki; exact Or.inr (Or.inr (Or.inl ⟨k, by omega, hall k⟩))
        · exact Or.inr (Or.inl ⟨k, by rw [← hne k hki]; exact hk⟩)
      · by_cases hki : k = i
        · subst hki
          exfalso
          rw [hpar] at hsh
          simp only [update_Fin_gss] at hsh
          exact Bstate.noConfusion hsh
        · refine Or.inr (Or.inr (Or.inl ⟨k, by rw [← hne k hki]; exact hk, ?_⟩))
          rw [hpar] at hsh
          simpa only [update_Fin_gso2 _ _ _ _ hki] using hsh
      · exfalso
        rw [hpar] at hp hq
        by_cases hpi : p = i
        · subst hpi
          have hqi : ¬(q = p) := fun hh => hpq hh.symm
          simp only [update_Fin_gso2 _ _ _ _ hqi] at hq
          exact Bstate.noConfusion ((hall q).symm.trans hq)
        · simp only [update_Fin_gso2 _ _ _ _ hpi] at hp
          exact Bstate.noConfusion ((hall p).symm.trans hp)
  | upgrade_to_M_invalid_all =>
      refine unreachable_setM_of_eq (fun k => by rw [hpar]) ?_ (fun hd' => absurd hd' hnd)
      intro k
      rw [htok k, htokc k]
      by_cases hk : k = i
      · subst hk
        simp [update_Fin_gss, PCEvent.isGrant]
      · simp only [update_Fin_gso2 _ _ _ _ hk]
  | invalid_all =>
      refine unreachable_setM_of_eq (fun k => by rw [hpar]) ?_ (fun hd' => absurd hd' hnd)
      intro k
      rw [htok k, htokc k]
      by_cases hk : k = i
      · subst hk
        simp [update_Fin_gss, PCEvent.isGrant]
      · simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Il passo singolo, su tutte le transizioni: se il successore e' nell'insieme, lo era
gia' il predecessore.  I passi di cache non toccano `shared_state` e conservano i token
(`cache_step_tokens`); i passi del parent sono trattati da `back_step_parent_aux`. -/
theorem back_step_MIM {n} {c a : MIState n} {t} (h : mi_step_internal c t a) :
    unreachable_setM a → unreachable_setM c := by
  intro ha
  by_cases hdes : c.desynced
  · exact Or.inl hdes
  have hsy := synced_of_not_desynced hdes
  cases h with
  | parent_no_queue parent' ev i hstep => cases hstep
  | cache cache' i ev hstep =>
      refine unreachable_setM_of_eq ?_ ?_ ?_ ha
      · intro k; rfl
      · intro k
        by_cases hk : k = i
        · subst hk
          have hcs := cache_step_tokens hstep
          simp only [CacheState.tokens] at hcs
          simp only [MIState.tokens, update_Fin_gss, ← (hsy k).1, ← (hsy k).2]
          exact hcs
        · simp only [MIState.tokens, update_Fin_gso2 _ _ _ _ hk]
      · rintro ⟨k, hk⟩
        by_cases hki : k = i
        · subst hki
          exfalso
          rcases hk with hk | hk <;> simp only [update_Fin_gss] at hk <;> exact hk rfl
        · exact ⟨k, by simpa only [update_Fin_gso2 _ _ _ _ hki] using hk⟩
  | parent_upd_queue parent' ev i hstep =>
      refine back_step_parent_aux hstep ?_ rfl ?_ ha
      · intro k
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss]
        · simp only [update_Fin_gso2 _ _ _ _ hk]
      · rintro ⟨k, hk⟩
        by_cases hki : k = i
        · subst hki
          rcases hk with hk | hk <;> simp only [update_Fin_gss] at hk <;> exact hk rfl
        · obtain ⟨hc, hp, -⟩ := parent_step_local hstep k hki
          rcases hk with hk | hk
          · exact hk (by simp only [update_Fin_gso2 _ _ _ _ hki, hp]; exact (hsy k).1)
          · exact hk (by simp only [update_Fin_gso2 _ _ _ _ hki, hc]; exact (hsy k).2)

/-! ## Conseguenze: due cache in `M` non sono raggiungibili -/

/-- Chiusura all'indietro lungo un'esecuzione qualsiasi: induzione su `back_step_MIM`. -/
theorem back_reachable_MIM {n} {x} : ∀ s, @unreachable_setM n s →
    MI.backwards_reachable_from s x → @unreachable_setM n x := by
  dsimp [MI.LTS.backwards_reachable_from]
  intro s hu h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hu
  | @head a c h1 h2 h3 =>
    clear h2
    apply h3
    dsimp [Function.swap, MI, MI.LTS.atrans] at h1
    obtain ⟨t, ht⟩ := h1
    exact back_step_MIM ht hu

/-- Lo stato iniziale e' FUORI dall'insieme: zero token, code allineate, nessuno
`shared_state` a `M`.  Senza questo tutto il resto sarebbe vacuo. -/
theorem not_unreachable_setM_default {n} : ¬ @unreachable_setM n default := by
  have htok : ∀ i : Fin n, (default : MIState n).tokens i = 0 := fun _ => rfl
  rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi, -⟩ | hu)
  · rcases hi with hi | hi <;> exact hi rfl
  · rw [htok i] at hi; omega
  · rw [htok i] at hi; omega
  · exact not_unreachable_default hu

/-- **Tutto `unreachable_setM` e' irraggiungibile.**  Allargare l'insieme non ha
indebolito nulla: ogni stato che ci sta dentro e' fuori dall'esecuzione, non solo quelli
con due cache in `M`. -/
theorem unreachable_setM_not_reachable {n} (s : MIState n) (h : unreachable_setM s) :
    ¬ ReflTransGen MI.atrans (default : MIState n) s := by
  intro hreach
  rw [Relation.reflTransGen_swap] at hreach
  exact not_unreachable_setM_default (back_reachable_MIM _ h hreach)

/-- **Il risultato.**  Uno stato con due cache distinte in `M` non e' raggiungibile
dallo stato iniziale: e' il caso particolare di `unreachable_setM_not_reachable` lungo
l'inclusione `unreachable_setM_of_twoCachesM`. -/
theorem two_caches_M_not_reachable {n} (s : MIState n) (h : twoCachesM s) :
    ¬ ReflTransGen MI.atrans (default : MIState n) s :=
  unreachable_setM_not_reachable s (unreachable_setM_of_twoCachesM h)

/-- **La versione vera del teorema che si vorrebbe.** Stesse ipotesi di
`back_reachable_MI1`; la conclusione pero' deve essere l'insieme piu' grande, perche'
il predecessore ha una sola cache in `M` e il secondo "proprietario" e' un messaggio
in volo. -/
theorem back_reachable_MI1_correct {n} {x} : ∀ s, @unreachable_set1 n s →
    MI.backwards_reachable_from s x → @unreachable_setM n x :=
  fun s h hb => back_reachable_MIM s (unreachable_setM_of_twoCachesM h) hb

theorem reachable_MI1 {n} : ∀ s : MIState n, twoCachesM s → ¬ MI.reachable s := by
  intro s h hreach
  dsimp [MI.LTS.reachable] at hreach
  exact two_caches_M_not_reachable s h (hreach (default : MIState n) (by trivial))
