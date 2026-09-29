import Mathlib.Data.Multiset.AddSub
import StarExperimental.MSI_def
import Star.Commute.ARS

/-! # `MSI_bag_def`: il protocollo MSI con le code come *bag*

Stesso protocollo di `MSI_def.lean` (stessi eventi, stesse regole, stesse guardie), ma le code
`queue_cp`/`queue_pc` (lato cache) e `queue_cip`/`queue_pci` (lato parent) sono `Multiset`: un
messaggio si riceve se `m ∈ coda` e si toglie con `erase`, l'ordine non esiste. Così due stati che
differiscono solo per l'ordine dei messaggi sono *uguali*, e il diamante di ARS (uguaglianza di
stati) non è più disturbato dall'ordine. Le `extqueue` restano liste: sono l'interfaccia esterna.

Gli eventi (`CPEvent`, `PCEvent`, `Event`, `CacheInternalEvent`, `ParentInternalEvent`,
`MSIInternalEvent`, `MSIExternalEvent`) e la vista `MSIView.View` sono quelli di `MSI_def.lean`.
Le viste cattive sono i 13 pattern di `MSIView.badView` più i due "riga registrata senza
portatore"; la tattica backward gira sui passi interni *ed esterni* (`msi_step_any`), quindi
`Reach` (raggiungibilità di ARS, con passi esterni) dà direttamente `¬ badView`. -/

open THEORY Relation BackwardGen

namespace MSIBag

/-! ## Stati -/

structure CacheState where
  state : Bstate
  value : Value
  queue_cp : Multiset CPEvent
  queue_pc : Multiset PCEvent
  extqueue : RsRqEvent

instance : Inhabited CacheState := ⟨⟨Bstate.I, 0, 0, 0, ⟨[], []⟩⟩⟩

structure ParentState (n : Nat) where
  value : Value
  shared_state : Fin n → Bstate
  queue_cip : Fin n → Multiset CPEvent
  queue_pci : Fin n → Multiset PCEvent

instance : Inhabited (ParentState n) := ⟨⟨0, fun _ => Bstate.I, fun _ => 0, fun _ => 0⟩⟩

structure MSIState (n : Nat) where
  caches : Fin n → CacheState
  parent : ParentState n

instance : Inhabited (MSIState n) := ⟨⟨fun _ => default, default⟩⟩

/-- Stato iniziale: come `msi_init` di `MSI_def`; l'unico stato che lo soddisfa è `default`. -/
@[simp]
def msi_init (s : MSIState n) : Prop :=
  (∀ k, (s.caches k).state = Bstate.I ∧ (s.caches k).queue_cp = 0 ∧ (s.caches k).queue_pc = 0
        ∧ (s.caches k).extqueue.rs = [] ∧ (s.caches k).extqueue.rq = [] ∧ (s.caches k).value = 0)
  ∧ (∀ k, s.parent.shared_state k = Bstate.I ∧ s.parent.queue_cip k = 0 ∧ s.parent.queue_pci k = 0)
  ∧ s.parent.value = 0

theorem msi_init_default : msi_init (default : MSIState n) := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

/-! ## Passi esterni della cache (identici a `MSI_def.cache_msi_step`) -/

inductive cache_msi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ (s1 : CacheState),
      cache_msi_step s1 Event.ld_rq
        { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.ld_rq] }
  | st_rq : ∀ (s1 : CacheState) (v : Value),
      cache_msi_step s1 (Event.st_rq v)
        { s1 with extqueue.rq := s1.extqueue.rq ++ [Event.st_rq v] }
  -- load servita in `S`
  | ld_rq_data_available1 : ∀ (s1 : CacheState) (rst : List Event),
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.S →
      cache_msi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst }
  -- load servita in `M`
  | ld_rq_data_available : ∀ (s1 : CacheState) (rst : List Event),
      s1.extqueue.rq = Event.ld_rq :: rst →
      s1.state = Bstate.M →
      cache_msi_step s1 (Event.ld_rs s1.value)
        { s1 with extqueue.rs := s1.extqueue.rs ++ [Event.ld_rs s1.value],
                  extqueue.rq := rst }
  -- store servita in `M`
  | st_rq_M_state : ∀ (s1 : CacheState) (v : Value) (rst : List Event),
      s1.extqueue.rq = Event.st_rq v :: rst →
      s1.state = Bstate.M →
      cache_msi_step s1 Event.st_rs
        { s1 with value := v,
                  extqueue.rs := s1.extqueue.rs ++ [Event.st_rs],
                  extqueue.rq := rst }

/-! ## Regole del parent (bag: `m ∈ coda`, `erase`) -/

inductive parent_msi_step : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  -- la cache `i` cede la linea da `M`: il parent prende il dato e la mette a `I`
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) v i,
      CPEvent.rsIμ v ∈ p1.queue_cip i →
      parent_msi_step p1 (.upd_queue (.downgrade_from_M_rq1 v) i)
        { p1 with value := v,
                  shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).erase (CPEvent.rsIμ v)) p1.queue_cip }
  -- la cache `i` cede la linea da `S`: il parent la mette a `I`
  | downgrade_from_M_rq2 : ∀ (p1 : ParentState n) i,
      CPEvent.rsIσ ∈ p1.queue_cip i →
      parent_msi_step p1 (.upd_queue (.downgrade_from_S_rq1S) i)
        { p1 with shared_state := update_Fin i Bstate.I p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).erase CPEvent.rsIσ) p1.queue_cip }
  -- grant di `M` a `i`: nessun'altra cache tiene la linea
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) i,
      CPEvent.rqM ∈ p1.queue_cip i →
      (∀ i, p1.shared_state i = Bstate.I) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_data_avilable_rq1) i)
        { p1 with shared_state := update_Fin i Bstate.M p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).erase CPEvent.rqM) p1.queue_cip,
                  queue_pci := update_Fin i (PCEvent.rsM p1.value ::ₘ p1.queue_pci i) p1.queue_pci }
  -- grant di `S` a `i`: la riga di `i` è a `I` e nessuna cache tiene la linea in `M`
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1 : ParentState n) i,
      CPEvent.rqS ∈ p1.queue_cip i →
      p1.shared_state i = Bstate.I →
      (∀ i, ¬(p1.shared_state i = Bstate.M)) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_data_avilable_rq1S) i)
        { p1 with shared_state := update_Fin i Bstate.S p1.shared_state,
                  queue_cip := update_Fin i ((p1.queue_cip i).erase CPEvent.rqS) p1.queue_cip,
                  queue_pci := update_Fin i (PCEvent.rsS p1.value ::ₘ p1.queue_pci i) p1.queue_pci }
  -- `i` chiede `M` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) i i',
      CPEvent.rqM ∈ p1.queue_cip i →
      p1.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (PCEvent.rqIμ ::ₘ p1.queue_pci i') p1.queue_pci }
  -- `i` chiede `M` e `i'` tiene la linea in `S`: invalida `i'`
  | upgrade_to_M_invalid_all1 : ∀ (p1 : ParentState n) i i',
      CPEvent.rqM ∈ p1.queue_cip i →
      p1.shared_state i' = Bstate.S →
      parent_msi_step p1 (.upd_queue (.invalid_allS) i')
        { p1 with queue_pci := update_Fin i' (PCEvent.rqIσ ::ₘ p1.queue_pci i') p1.queue_pci }
  -- `i` chiede `S` e un'altra cache `i'` tiene la linea in `S`: invalida `i'`
  | upgrade_to_M_invalid_all2 : ∀ (p1 : ParentState n) i i',
      CPEvent.rqS ∈ p1.queue_cip i →
      ¬(i' = i) →
      p1.shared_state i' = Bstate.S →
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_invalid_2_rq1S i) i')
        { p1 with queue_pci := update_Fin i' (PCEvent.rqIσ ::ₘ p1.queue_pci i') p1.queue_pci }
  -- `i` chiede `S` e `i'` tiene la linea in `M`: invalida `i'`
  | upgrade_to_M_invalid_all3 : ∀ (p1 : ParentState n) i i',
      CPEvent.rqS ∈ p1.queue_cip i →
      p1.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all i) i')
        { p1 with queue_pci := update_Fin i' (PCEvent.rqIμ ::ₘ p1.queue_pci i') p1.queue_pci }

/-! ## Regole interne della cache (bag) -/

inductive cache_msi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  -- rilascio spontaneo da `M` (porta il dato)
  | rq_data_not_available : ∀ (s1 : CacheState),
      s1.state = Bstate.M →
      cache_msi_step_internal s1 .rq_data_not_available
        { s1 with queue_cp := CPEvent.rsIμ s1.value ::ₘ s1.queue_cp, state := Bstate.I }
  -- rilascio spontaneo da `S`
  | rq_data_not_available1 : ∀ (s1 : CacheState),
      s1.state = Bstate.S →
      cache_msi_step_internal s1 .ld_rq_data_not_availableS
        { s1 with queue_cp := CPEvent.rsIσ ::ₘ s1.queue_cp, state := Bstate.I }
  -- richiesta di `M` da `I`
  | upgrade_from_I_rq : ∀ (s1 : CacheState),
      s1.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rq
        { s1 with queue_cp := CPEvent.rqM ::ₘ s1.queue_cp }
  -- richiesta di `S` da `I`
  | upgrade_from_I_rq1 : ∀ (s1 : CacheState),
      s1.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rqS
        { s1 with queue_cp := CPEvent.rqS ::ₘ s1.queue_cp }
  -- presa del grant di `M`
  | upgrade_from_I_rs : ∀ (s1 : CacheState) (v : Value),
      PCEvent.rsM v ∈ s1.queue_pc →
      s1.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M, value := v, queue_pc := s1.queue_pc.erase (PCEvent.rsM v) }
  -- presa del grant di `S`
  | upgrade_from_I_rsS : ∀ (s1 : CacheState) (v : Value),
      PCEvent.rsS v ∈ s1.queue_pc →
      s1.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rsS v)
        { s1 with state := Bstate.S, value := v, queue_pc := s1.queue_pc.erase (PCEvent.rsS v) }
  -- invalidate ricevuto in `M`: cede la linea con il dato
  | downgrade_from_M_rs : ∀ (s1 : CacheState),
      PCEvent.rqIμ ∈ s1.queue_pc →
      s1.state = Bstate.M →
      cache_msi_step_internal s1 .downgrade_from_M_rs
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.erase PCEvent.rqIμ,
                  queue_cp := CPEvent.rsIμ s1.value ::ₘ s1.queue_cp }
  -- invalidate ricevuto in `S`: cede la linea
  | downgrade_from_M_rs1 : ∀ (s1 : CacheState),
      PCEvent.rqIσ ∈ s1.queue_pc →
      s1.state = Bstate.S →
      cache_msi_step_internal s1 .downgrade_from_S_rsS
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.erase PCEvent.rqIσ,
                  queue_cp := CPEvent.rsIσ ::ₘ s1.queue_cp }

/-! ## Passi di sistema -/

inductive msi_step_internal : MSIState n → MSIInternalEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (cache' : CacheState) (i : Fin n) (e : CacheInternalEvent),
      cache_msi_step_internal (m1.caches i) e cache' →
      msi_step_internal m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }
  | parent_upd_queue : ∀ (m1 : MSIState n) (parent' : ParentState n) (e : ParentUpdQueueInternalEvent n) (i : Fin n),
      parent_msi_step m1.parent (.upd_queue e i) parent' →
      msi_step_internal m1 (.parent (.upd_queue e i))
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i,
                                                             queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent' }

inductive msi_step_external : MSIState n → MSIExternalEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (e : Event) (cache' : CacheState) (i : Fin n),
      cache_msi_step (m1.caches i) e cache' →
      msi_step_external m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }

/-- Un passo qualunque, interno o esterno: è la transizione su cui gira la tattica backward. -/
inductive msi_step_any : MSIState n → (MSIInternalEvent n ⊕ MSIExternalEvent n) → MSIState n → Prop where
  | int : ∀ (m1 : MSIState n) (e : MSIInternalEvent n) (m2 : MSIState n),
      msi_step_internal m1 e m2 → msi_step_any m1 (.inl e) m2
  | ext : ∀ (m1 : MSIState n) (e : MSIExternalEvent n) (m2 : MSIState n),
      msi_step_external m1 e m2 → msi_step_any m1 (.inr e) m2

/-- Le regole interne come `Rule` di ARS. -/
def msi_rule (n : Nat) : ReachingStar.Rule (MSIState n) := fun a b => ∃ e, msi_step_internal a e b

/-- Raggiungibilità di ARS: da `default` con passi interni ed esterni. -/
def Reach (x : MSIState n) : Prop :=
  ReachingStar.reachable (msi_rule n) msi_step_external x (default : MSIState n)

/-! ## Viste, `synced`, viste cattive, setup della tattica -/

def isGrantM : PCEvent → Bool
  | .rsM _ => true
  | _ => false

def isGrantS : PCEvent → Bool
  | .rsS _ => true
  | _ => false

def isReleaseM : CPEvent → Bool
  | .rsIμ _ => true
  | _ => false

def isReleaseS : CPEvent → Bool
  | .rsIσ => true
  | _ => false

/-- Messaggi con token `M` per l'indice `k`, contati dal lato parent. -/
def muMsgs (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP (fun e => isGrantM e = true) + (p.queue_cip k).countP (fun e => isReleaseM e = true)

/-- Messaggi con token `S` per l'indice `k`, contati dal lato parent. -/
def sigMsgs (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP (fun e => isGrantS e = true) + (p.queue_cip k).countP (fun e => isReleaseS e = true)

/-- La vista della coppia `(i, j)`: la stessa `MSIView.View` di `MSI_def`. -/
def msiView (s : MSIState n) (i j : Fin n) : MSIView.View :=
  ⟨(s.caches i).state,
   s.parent.shared_state i, s.parent.shared_state j,
   Cnt.ofCount (muMsgs s.parent i), Cnt.ofCount (sigMsgs s.parent i),
   decide (i = j)⟩

/-- Le due copie di ogni coda coincidono. -/
def synced (s : MSIState n) : Prop :=
  ∀ k, s.parent.queue_cip k = (s.caches k).queue_cp ∧ s.parent.queue_pci k = (s.caches k).queue_pc

theorem parent_step_local {p1 p2 : ParentState n} {e i}
    (h : parent_msi_step p1 (.upd_queue e i) p2) :
    ∀ k, ¬(k = i) → p2.queue_cip k = p1.queue_cip k ∧ p2.queue_pci k = p1.queue_pci k
                    ∧ p2.shared_state k = p1.shared_state k := by
  cases h <;> intro k hk <;>
    exact ⟨by simp [update_Fin_gso2 _ _ _ _ hk], by simp [update_Fin_gso2 _ _ _ _ hk],
           by simp [update_Fin_gso2 _ _ _ _ hk]⟩

theorem synced_step {s s' : MSIState n} {t} (hs : synced s) (h : msi_step_internal s t s') :
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

theorem synced_step_ext {s s' : MSIState n} {t} (hs : synced s) (h : msi_step_external s t s') :
    synced s' := by
  cases h with
  | cache e cache' p hc =>
      intro k
      by_cases hk : k = p
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2]

theorem synced_step_any {s s' : MSIState n} {t} (hs : synced s) (h : msi_step_any s t s') :
    synced s' := by
  cases h with
  | int _ _ h => exact synced_step hs h
  | ext _ _ h => exact synced_step_ext hs h

/-- **Le viste cattive**: i 13 pattern di `MSIView.badView` (un solo proprietario di `M`,
registrato dal parent, che esclude tutto il resto; ogni portatore di `S` registrato dal parent)
più i due pattern "riga registrata senza portatore": riga `M` di `i` senza cache in `M` né token
`M` in volo; riga `S` di `i` senza cache in `S` né token `S` in volo. -/
def badView (v : MSIView.View) : Prop :=
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
  ∨ (v.d0 = .M ∧ v.c0 ≠ .M ∧ v.m0 = .zero)
  ∨ (v.d0 = .S ∧ v.c0 ≠ .S ∧ v.s0 = .zero)

def msiSetup (n : Nat) :
    SymSetup (MSIState n) (MSIInternalEvent n ⊕ MSIExternalEvent n) (Fin n) MSIView.View where
  trans := msi_step_any
  Inv := synced
  inv_step := fun _ _ _ hs h => synced_step_any hs h
  view := msiView
  bad := badView
  s0 := default
  inv0 := fun _ => ⟨rfl, rfl⟩

/-! ### Lemmi in avanti per la tattica: `countP` di `erase` -/

theorem countP_erase_grantM {s : Multiset PCEvent} {a : PCEvent} (h : a ∈ s) :
    (s.erase a).countP (fun e => isGrantM e = true) + (if isGrantM a = true then 1 else 0)
      = s.countP (fun e => isGrantM e = true) := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

theorem countP_erase_grantS {s : Multiset PCEvent} {a : PCEvent} (h : a ∈ s) :
    (s.erase a).countP (fun e => isGrantS e = true) + (if isGrantS a = true then 1 else 0)
      = s.countP (fun e => isGrantS e = true) := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

theorem countP_erase_releaseM {s : Multiset CPEvent} {a : CPEvent} (h : a ∈ s) :
    (s.erase a).countP (fun e => isReleaseM e = true) + (if isReleaseM a = true then 1 else 0)
      = s.countP (fun e => isReleaseM e = true) := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

theorem countP_erase_releaseS {s : Multiset CPEvent} {a : CPEvent} (h : a ∈ s) :
    (s.erase a).countP (fun e => isReleaseS e = true) + (if isReleaseS a = true then 1 else 0)
      = s.countP (fun e => isReleaseS e = true) := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

/-- La tattica con i parametri del modello bag già messi. -/
syntax "bag_backward_tactic" : tactic
macro_rules
  | `(tactic| bag_backward_tactic) =>
    `(tactic| backward_search_gen (msiSetup _)
      simp [msiView, muMsgs, sigMsgs, synced, update_Fin_gss, update_Fin_gso,
            update_Fin_gso2, Multiset.countP_cons, Multiset.countP_zero,
            isGrantM, isGrantS, isReleaseM, isReleaseS, Cnt.ofCount, Cnt.ofCount_eq_zero,
            Cnt.ofCount_eq_one, Cnt.ofCount_eq_many]
      fwd [countP_erase_grantM, countP_erase_grantS, countP_erase_releaseM, countP_erase_releaseS]
      split Cnt.ofCount_cases Cnt.ofCount
      upd update_Fin
      inv [msi_step_any, msi_step_internal, msi_step_external, cache_msi_step,
           cache_msi_step_internal, parent_msi_step])

set_option maxHeartbeats 0 in
/-- **Il risultato della tattica**: nessuno stato con una vista cattiva è raggiungibile da
`default` con passi interni ed esterni. -/
theorem badView_unreachable_from_default {n} : (msiSetup n).Unreachable := by
  bag_backward_tactic

/-! ## Da `Reach` alle viste: nessun altro invariante -/

theorem reach_any {x : MSIState n} (h : Reach x) :
    ReflTransGen (msiSetup n).atrans (default : MSIState n) x := by
  unfold Reach ReachingStar.reachable at h
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact ReflTransGen.refl
  | step_int l s' s'' _ hstep ih =>
    have key : ∀ {a b : MSIState n}, ReachingStar.trans_refl (msi_rule n) a b →
        ReflTransGen (msiSetup n).atrans a b := by
      intro a b hab
      induction hab with
      | refl => exact ReflTransGen.refl
      | step hr _ ih' =>
        obtain ⟨e, he⟩ := hr
        exact ReflTransGen.head ⟨.inl e, msi_step_any.int _ _ _ he⟩ ih'
    exact ih.trans (key hstep)
  | step_ext l s' s'' e _ hstep ih =>
    exact ih.tail ⟨.inr e, msi_step_any.ext _ _ _ hstep⟩

/-- Lungo i passi (interni ed esterni) da `default` vale `synced`. -/
theorem synced_of_any {x : MSIState n} (h : ReflTransGen (msiSetup n).atrans (default : MSIState n) x) :
    synced x := by
  induction h with
  | refl => exact fun _ => ⟨rfl, rfl⟩
  | tail _ hstep ih => obtain ⟨t, ht⟩ := hstep; exact synced_step_any ih ht

theorem synced_of_reach {x : MSIState n} (h : Reach x) : synced x :=
  synced_of_any (reach_any h)

/-- **Il ponte**: uno stato raggiungibile non ha viste cattive. Nessun invariante dimostrato a
mano: solo il risultato della tattica. -/
theorem noBad_of_reach {x : MSIState n} (h : Reach x) : ∀ i j, ¬ badView (msiView x i j) := by
  intro i j hb
  exact badView_unreachable_from_default x ⟨i, j, hb⟩ (reach_any h)

/-- `Reach` è chiusa per passi interni. -/
theorem reach_step {x y : MSIState n} (h : Reach x) {e} (hs : msi_step_internal x e y) : Reach y := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, ReachingStar.star_extend.step_int _ _ _ _ hl
    (ReachingStar.trans_refl.step ⟨e, hs⟩ ReachingStar.trans_refl.refl)⟩

theorem reach_trans {x y : MSIState n} (h : Reach x) (hs : ReachingStar.trans_refl (msi_rule n) x y) :
    Reach y := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, ReachingStar.star_extend.step_int _ _ _ _ hl hs⟩

theorem reach_step_ext {x y : MSIState n} (h : Reach x) {e} (hs : msi_step_external x e y) : Reach y := by
  obtain ⟨l, hl⟩ := h
  exact ⟨e :: l, ReachingStar.star_extend.step_ext _ _ _ _ _ hl hs⟩

theorem reach_default : Reach (default : MSIState n) := ⟨[], ReachingStar.star_extend.refl _⟩

end MSIBag
