import StarExperimental.MSI_def
import Star.Commute.ARS

/-!
# `MSI_trial`: MSI con richieste non duplicate e invalidate stantii scartati

Variante di `MSI_def` pensata per dimostrare la confluenza dei passi interni **senza terminazione**,
con i diagrammi decrescenti (`DecreasingDiagrams.lean`). Le regole sono quelle di `MSI_def`, con due
modifiche, entrambe sulla cache; il parent è identico (`parent_msi_step` è riusato tale e quale).

1. **Una richiesta per volta, del tipo che serve.** `upgrade_from_I_rq`/`upgrade_from_I_rqS` chiedono
   la linea solo se la cache non ha già una richiesta (`rqM`/`rqS`) in `queue_cp` né un grant
   (`rsM`/`rsS`) in volo per sé in `queue_pc`, e chiedono `M` se il programma ha una store in testa,
   `S` se ha una load. In `MSI_def` una cache in `I` con un grant in volo poteva richiedere di nuovo,
   e i due ordini "richiesta poi presa" / "presa" non si ricongiungevano (`reqMSt`); e poteva chiedere
   `M` e `S` insieme, due richieste che si ricongiungono solo svuotando tutta la directory.
   Le richieste restano spontanee nel *momento*: una cache in `I` con una load in testa può chiedere
   `S` quando vuole, e dopo un rilascio spontaneo chiederla di nuovo.
2. **Gli invalidate stantii muoiono.** Una cache in `I` scarta un `rqIμ` o un `rqIσ` nella sua
   `queue_pc` (`drop_rqIμ`, `drop_rqIσ`). In `MSI_def` un invalidate arrivato dopo il rilascio
   spontaneo restava in coda per sempre, e i due ordini "rilascio spontaneo" / "rilascio su
   invalidate" si ricongiungevano solo *a meno* di quel messaggio (`dropSt`, `invMSt`).

Richieste e rilasci spontanei restano: il modello **non termina**, e la confluenza non può venire da
Newman. Viene dai diagrammi decrescenti con le etichette `lab`:

| etichetta | regole |
|---|---|
| 7 | richiesta (`upgrade_from_I_rq`, `upgrade_from_I_rqS`) |
| 6 | invalidate (`upgrade_to_M_invalid_all`, `invalid_allS`, `upgrade_to_S_invalid_2_rq1S`) |
| 4 | grant (`upgrade_to_M_data_avilable_rq1`, `upgrade_to_S_data_avilable_rq1S`) |
| 3 | presa del grant (`upgrade_from_I_rs`, `upgrade_from_I_rsS`) |
| 2 | rilascio, spontaneo o su invalidate (`rq_data_not_available`, `ld_rq_data_not_availableS`, `downgrade_from_M_rs`, `downgrade_from_S_rsS`) |
| 1 | consumo del rilascio al parent (`downgrade_from_M_rq1`, `downgrade_from_S_rq1S`) |
| 0 | scarto di un invalidate stantio (`drop_rqIμ`, `drop_rqIσ`) |

La raggiungibilità è quella di ARS (`Reach`): da `default` con passi interni **ed esterni**. È la
stessa che compare in `has_diamond_property_on`, e include gli stati con richieste del programma in
coda; `MSI.reachable` di `MSI_def` (soli passi interni) non li include.
-/

open THEORY Relation
open ReachingStar (Rule)

namespace MSITrial

variable {n : Nat}

/-! ## Eventi -/

/-- Eventi interni della cache: quelli di `MSI_def` più i due scarti. -/
inductive CEvent where
  | rq_data_not_available
  | upgrade_from_I_rq
  | upgrade_from_I_rs (v : Value)
  | downgrade_from_M_rs
  | ld_rq_data_not_availableS
  | upgrade_from_I_rqS
  | upgrade_from_I_rsS (v : Value)
  | downgrade_from_S_rsS
  | drop_rqIμ
  | drop_rqIσ
  deriving DecidableEq, Repr

/-- Eventi interni di `MSI_trial`: un evento di cache con il suo indice, o un evento del parent
(`ParentUpdQueueInternalEvent`, come in `MSI_def`) con l'indice su cui agisce. -/
inductive IEvent (n : Nat) where
  | cache (e : CEvent) (i : Fin n)
  | parent (e : ParentUpdQueueInternalEvent n) (i : Fin n)

/-- L'etichetta di un evento interno (tabella nel preambolo). -/
def lab : IEvent n → Nat
  | .cache .rq_data_not_available _ => 2
  | .cache .upgrade_from_I_rq _ => 7
  | .cache (.upgrade_from_I_rs _) _ => 3
  | .cache .downgrade_from_M_rs _ => 2
  | .cache .ld_rq_data_not_availableS _ => 2
  | .cache .upgrade_from_I_rqS _ => 7
  | .cache (.upgrade_from_I_rsS _) _ => 3
  | .cache .downgrade_from_S_rsS _ => 2
  | .cache .drop_rqIμ _ => 0
  | .cache .drop_rqIσ _ => 0
  | .parent (.downgrade_from_M_rq1 _) _ => 1
  | .parent .downgrade_from_S_rq1S _ => 1
  | .parent .upgrade_to_M_data_avilable_rq1 _ => 4
  | .parent .upgrade_to_S_data_avilable_rq1S _ => 4
  | .parent (.upgrade_to_M_invalid_all _) _ => 6
  | .parent .invalid_allS _ => 6
  | .parent (.upgrade_to_S_invalid_2_rq1S _) _ => 6
  | .parent .invalid_allM _ => 6
  | .parent .dawngrade_safe_parent_rq1 _ => 6
  | .parent .dawngrade_safe_parent_rq1S _ => 6

/-! ## Regole della cache -/

/-- Una richiesta è in sospeso: la cache ha già chiesto la linea. -/
def pending (c : CacheState) : Prop := CPEvent.rqM ∈ c.queue_cp ∨ CPEvent.rqS ∈ c.queue_cp

/-- Un grant è in volo verso la cache. -/
def grantInFlight (c : CacheState) : Prop :=
  (∃ v, PCEvent.rsM v ∈ c.queue_pc) ∨ (∃ v, PCEvent.rsS v ∈ c.queue_pc)

/-- Il programma ha una store in testa: la cache vuole `M`. -/
def wantsM (c : CacheState) : Prop := ∃ v rst, c.extqueue.rq = Event.st_rq v :: rst

/-- Il programma ha una load in testa: la cache vuole `S`. -/
def wantsS (c : CacheState) : Prop := ∃ rst, c.extqueue.rq = Event.ld_rq :: rst

inductive cache_step : CacheState → CEvent → CacheState → Prop where
  /-- Rilascio spontaneo da `M` (porta il dato). Come in `MSI_def`. -/
  | rq_data_not_available : ∀ s1,
      s1.state = Bstate.M →
      cache_step s1 .rq_data_not_available
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value], state := Bstate.I }
  /-- Rilascio spontaneo da `S`. Come in `MSI_def`. -/
  | rq_data_not_available1 : ∀ s1,
      s1.state = Bstate.S →
      cache_step s1 .ld_rq_data_not_availableS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rsIσ], state := Bstate.I }
  /-- Richiesta di `M` da `I` (modifica 1): **una sola richiesta per volta** (niente in sospeso, niente
  grant in volo) e **del tipo che serve al programma** (una store in testa). -/
  | upgrade_from_I_rq : ∀ s1,
      s1.state = Bstate.I →
      ¬ pending s1 →
      ¬ grantInFlight s1 →
      wantsM s1 →
      cache_step s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM] }
  /-- Richiesta di `S` da `I` (modifica 1): una sola richiesta per volta, e del tipo che serve al
  programma (una load in testa). -/
  | upgrade_from_I_rq1 : ∀ s1,
      s1.state = Bstate.I →
      ¬ pending s1 →
      ¬ grantInFlight s1 →
      wantsS s1 →
      cache_step s1 .upgrade_from_I_rqS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqS] }
  /-- Presa del grant di `M`. Come in `MSI_def`. -/
  | upgrade_from_I_rs : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsM v) →
      s1.state = Bstate.I →
      cache_step s1 (.upgrade_from_I_rs v)
        { s1 with state := Bstate.M, value := v, queue_pc := s1.queue_pc.eraseIdx j }
  /-- Presa del grant di `S`. Come in `MSI_def`. -/
  | upgrade_from_I_rsS : ∀ s1 v j,
      (s1.queue_pc)[j]? = some (PCEvent.rsS v) →
      s1.state = Bstate.I →
      cache_step s1 (.upgrade_from_I_rsS v)
        { s1 with state := Bstate.S, value := v, queue_pc := s1.queue_pc.eraseIdx j }
  /-- Invalidate ricevuto in `M`: cede la linea con il dato. Come in `MSI_def`. -/
  | downgrade_from_M_rs : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIμ →
      s1.state = Bstate.M →
      cache_step s1 .downgrade_from_M_rs
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIμ s1.value] }
  /-- Invalidate ricevuto in `S`: cede la linea. Come in `MSI_def`. -/
  | downgrade_from_M_rs1 : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIσ →
      s1.state = Bstate.S →
      cache_step s1 .downgrade_from_S_rsS
        { s1 with state := Bstate.I,
                  queue_pc := s1.queue_pc.eraseIdx j,
                  queue_cp := s1.queue_cp ++ [CPEvent.rsIσ] }
  /-- **Scarto di un `rqIμ` stantio** (modifica 2): in `I` non c'è niente da cedere. -/
  | drop_rqIμ : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIμ →
      s1.state = Bstate.I →
      cache_step s1 .drop_rqIμ { s1 with queue_pc := s1.queue_pc.eraseIdx j }
  /-- **Scarto di un `rqIσ` stantio** (modifica 2). -/
  | drop_rqIσ : ∀ s1 j,
      (s1.queue_pc)[j]? = some PCEvent.rqIσ →
      s1.state = Bstate.I →
      cache_step s1 .drop_rqIσ { s1 with queue_pc := s1.queue_pc.eraseIdx j }

/-! ## Passi dell'intero sistema -/

/-- Un passo interno: una regola di cache (con le due copie delle code riallineate lato parent) o
una regola del parent di `MSI_def` (con le copie riallineate lato cache). Stessa composizione di
`msi_step_internal`. -/
inductive step_int : MSIState n → IEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (cache' : CacheState) (i : Fin n) (e : CEvent),
      cache_step (m1.caches i) e cache' →
      step_int m1 (.cache e i)
        { m1 with caches := update_Fin i cache' m1.caches,
                  parent.queue_cip := update_Fin i cache'.queue_cp m1.parent.queue_cip,
                  parent.queue_pci := update_Fin i cache'.queue_pc m1.parent.queue_pci }
  | parent_upd_queue : ∀ (m1 : MSIState n) (parent' : ParentState n)
      (e : ParentUpdQueueInternalEvent n) (i : Fin n),
      parent_msi_step m1.parent (.upd_queue e i) parent' →
      step_int m1 (.parent e i)
        { m1 with caches := update_Fin i { m1.caches i with queue_cp := parent'.queue_cip i,
                                                             queue_pc := parent'.queue_pci i } m1.caches,
                  parent := parent' }

/-- I passi esterni sono quelli di `MSI_def`. -/
abbrev step_ext : MSIState n → MSIExternalEvent n → MSIState n → Prop := msi_step_external

/-- Un passo qualunque, interno o esterno: la transizione su cui gira la tattica backward. -/
inductive step_any : MSIState n → (IEvent n ⊕ MSIExternalEvent n) → MSIState n → Prop where
  | int : ∀ (m1 : MSIState n) (e : IEvent n) (m2 : MSIState n),
      step_int m1 e m2 → step_any m1 (.inl e) m2
  | ext : ∀ (m1 : MSIState n) (e : MSIExternalEvent n) (m2 : MSIState n),
      msi_step_external m1 e m2 → step_any m1 (.inr e) m2

/-- I passi interni come `Rule` di ARS. -/
def rule (n : Nat) : Rule (MSIState n) := fun a b => ∃ e, step_int a e b

/-- I passi interni etichettati: quelli che `DecreasingDiagrams` legge. -/
def lstep (l : Nat) : MSIState n → MSIState n → Prop := fun a b => ∃ e, lab e = l ∧ step_int a e b

theorem rule_iff_lstep {a b : MSIState n} : rule n a b ↔ ∃ l, lstep l a b :=
  ⟨fun ⟨e, h⟩ => ⟨lab e, e, rfl, h⟩, fun ⟨_, e, _, h⟩ => ⟨e, h⟩⟩

/-- Raggiungibilità nel senso di ARS: da `default`, con passi interni ed esterni. -/
def Reach (x : MSIState n) : Prop :=
  ReachingStar.reachable (rule n) step_ext x (default : MSIState n)

/-! ## Le due copie delle code restano allineate -/

theorem synced_step_int {s s' : MSIState n} {e} (hs : MSIView.synced s) (h : step_int s e s') :
    MSIView.synced s' := by
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
        obtain ⟨h3, h4, _⟩ := MSIView.parent_step_local hp k hk
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2, h3, h4]

theorem synced_step_ext {s s' : MSIState n} {e} (hs : MSIView.synced s) (h : step_ext s e s') :
    MSIView.synced s' := by
  cases h with
  | cache e cache' p hc =>
      intro k
      by_cases hk : k = p
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2]

theorem synced_step_any {s s' : MSIState n} {t} (hs : MSIView.synced s) (h : step_any s t s') :
    MSIView.synced s' := by
  cases h with
  | int _ _ h => exact synced_step_int hs h
  | ext _ _ h => exact synced_step_ext hs h

theorem synced_default : MSIView.synced (default : MSIState n) := fun _ => ⟨rfl, rfl⟩

/-- Ogni stato raggiungibile ha le code allineate. -/
theorem synced_of_reach {x : MSIState n} (h : Reach x) : MSIView.synced x := by
  obtain ⟨l, hl⟩ := h
  induction hl with
  | refl => exact synced_default
  | step_int _ _ _ _ htr ih =>
      clear * - ih htr
      induction htr with
      | refl => exact ih
      | step hab _ ih' =>
          obtain ⟨e, he⟩ := hab
          exact ih' (synced_step_int ih he)
  | step_ext _ _ _ _ _ hext ih => exact synced_step_ext ih hext

/-! ## Il setup per la tattica backward

Stessa vista, stesso invariante e stesse viste cattive di `MSI_def`; la transizione è `step_any`,
così il certificato parla della raggiungibilità di ARS (passi interni ed esterni). -/

open BackwardGen in
def msiSetup (n : Nat) :
    SymSetup (MSIState n) (IEvent n ⊕ MSIExternalEvent n) (Fin n) MSIView.View where
  trans := step_any
  Inv := MSIView.synced
  inv_step := fun _ _ _ hs h => synced_step_any hs h
  view := MSIView.msiView
  bad := MSIView.badView
  s0 := default
  inv0 := synced_default

/-- `Reach` è la raggiungibilità del setup: una `trans_refl` di passi interni e passi esterni è
una `ReflTransGen` di `step_any`. -/
theorem reach_iff_setup {x : MSIState n} :
    Reach x ↔ ReflTransGen (msiSetup n).atrans (default : MSIState n) x := by
  constructor
  · rintro ⟨l, hl⟩
    induction hl with
    | refl => exact ReflTransGen.refl
    | step_int _ _ _ _ htr ih =>
        clear * - ih htr
        induction htr with
        | refl => exact ih
        | step hab _ ih' =>
            obtain ⟨e, he⟩ := hab
            exact ih' (ReflTransGen.tail ih ⟨.inl e, step_any.int _ _ _ he⟩)
    | step_ext _ _ _ _ _ hext ih =>
        exact ReflTransGen.tail ih ⟨.inr _, step_any.ext _ _ _ hext⟩
  · intro h
    induction h with
    | refl => exact ⟨[], ReachingStar.star_extend.refl _⟩
    | tail _ hstep ih =>
        obtain ⟨l, hl⟩ := ih
        obtain ⟨t, ht⟩ := hstep
        cases ht with
        | int e _ he =>
            exact ⟨l, ReachingStar.star_extend.step_int _ _ _ _ hl
              (ReachingStar.trans_refl.step ⟨e, he⟩ ReachingStar.trans_refl.refl)⟩
        | ext e _ he => exact ⟨e :: l, ReachingStar.star_extend.step_ext _ _ _ _ _ hl he⟩

end MSITrial
