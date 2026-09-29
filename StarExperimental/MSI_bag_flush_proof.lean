import StarExperimental.MSI_bag_confluent
import Star.SplitJoin.star

/-! # `MSI_bag_flush_proof`: l'inclusione delle tracce di MSI (modello bag) nello spec sequenziale

Lo spec (`SeqState`, `seq_step`) e la relazione `flush` sono quelli di `MSI_flush_proof.lean`, con
le code vuote scritte `0` (sono `Multiset`). Le sei ipotesi di `ReachingStar.trace_inclusion`:
`msi_relation_flush`, `msi_relation_flush_method_int`, `msi_relation_method_int`,
`msi_confluent`, `msi_commutes_upto` (da `MSI_bag_confluent.lean`), `msi_relation_init`.

Che cosa si usa: le viste (attraverso `Good`: uno stato flushed ha `shape = default`, quindi ogni
suo successore interno è buono), il valore logico `val`, e l'invariante `SVal` per le load servite
da `S`. Niente `flushInv`: il ritorno a flush è `reach_quiet` (le misure `μ1, μ2, μ3`) più
`val_trans`. -/

open THEORY Relation
open ReachingStar (Rule Method trans_refl relation_flush relation_flush_method relation_method
  relation_init)

namespace MSIBag

variable {n : Nat}

/-! ## Lo spec sequenziale (copia di `MSI_flush_proof.lean`) -/

structure SeqState (n : Nat) where
  memory : Value
  extqueue : Fin n -> RsRqEvent

instance : Inhabited (SeqState n) where
  default := SeqState.mk default (fun _ => default)

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

def imp_behaviour (n : Nat) :=
  behaviour_extend (default : MSIState n) msi_step_external msi_step_internal

/-! ## La relazione di flush (copia di `MSI_flush_proof.lean`, code `0`) -/

inductive flush0 (i : MSIState n) (s : SeqState n) : Prop where
  | intro :
      (∀ k, (i.caches k).state = Bstate.I ∧ (i.caches k).queue_cp = 0 ∧ (i.caches k).queue_pc = 0) →
      (∀ k, i.parent.shared_state k = Bstate.I ∧ i.parent.queue_cip k = 0 ∧ i.parent.queue_pci k = 0) →
      i.parent.value = s.memory →
      flush0 i s

def flush (i : MSIState n) (s : SeqState n) : Prop :=
  flush0 i s ∧ ∀ k, (i.caches k).extqueue = s.extqueue k

theorem msi_rule_of_step {a b : MSIState n} {e : MSIInternalEvent n}
    (h : msi_step_internal a e b) : msi_rule n a b :=
  Exists.intro e h

/-! ## Flush, quiete e stati buoni -/

theorem quiet_of_flush0 {i : MSIState n} {s : SeqState n} (hf : flush0 i s) : Quiet i := by
  obtain ⟨hc, hp, _⟩ := hf
  exact ⟨fun k => (hc k).1, fun k => (hc k).2.1, fun k => (hc k).2.2,
         fun k => (hp k).1, fun k => (hp k).2.1, fun k => (hp k).2.2⟩

theorem flush0_of_quiet {i : MSIState n} {s : SeqState n} (hq : Quiet i) (hv : i.parent.value = s.memory) :
    flush0 i s :=
  ⟨fun k => ⟨hq.caches k, hq.cp k, hq.pc k⟩, fun k => ⟨hq.rows k, hq.cip k, hq.pci k⟩, hv⟩

theorem synced_of_quiet {i : MSIState n} (hq : Quiet i) : synced i :=
  fun k => ⟨by rw [hq.cip k, hq.cp k], by rw [hq.pci k, hq.pc k]⟩

/-- Uno stato quieto ha la forma di `default`. -/
theorem shape_of_quiet {i : MSIState n} (hq : Quiet i) : shape i = default := by
  have hc : ∀ k, shapeCache (i.caches k) = default := by
    intro k
    unfold shapeCache
    rw [hq.caches k, hq.cp k, hq.pc k, Multiset.map_zero, Multiset.map_zero]
    rfl
  have hp : shapeParent i.parent = default := by
    have h1 : i.parent.shared_state = fun _ => Bstate.I := funext hq.rows
    have h2 : (fun k => (i.parent.queue_cip k).map stripCP) = fun _ => (0 : Multiset CPEvent) := by
      funext k; rw [hq.cip k, Multiset.map_zero]
    have h3 : (fun k => (i.parent.queue_pci k).map stripPC) = fun _ => (0 : Multiset PCEvent) := by
      funext k; rw [hq.pci k, Multiset.map_zero]
    unfold shapeParent
    rw [h1, h2, h3]
    rfl
  unfold shape
  rw [hp]
  show (⟨fun k => shapeCache (i.caches k), default⟩ : MSIState n) = ⟨fun _ => default, default⟩
  congr 1
  funext k
  exact hc k

theorem good_of_quiet {i : MSIState n} (hq : Quiet i) : Good i :=
  ⟨synced_of_quiet hq, by rw [shape_of_quiet hq]⟩

theorem good_of_flush0 {i : MSIState n} {s : SeqState n} (hf : flush0 i s) : Good i :=
  good_of_quiet (quiet_of_flush0 hf)

theorem sval_of_quiet {i : MSIState n} (hq : Quiet i) : SVal i :=
  ⟨fun k hS => absurd (hS.symm.trans (hq.caches k)) (by decide),
   fun k v hv => by rw [hq.pc k] at hv; simp at hv⟩

theorem sval_trans {x y : MSIState n} (hx : Good x) (hv : SVal x) (h : trans_refl (msi_rule n) x y) :
    SVal y := by
  induction h with
  | refl => exact hv
  | step hr _ ih =>
    obtain ⟨e, he⟩ := hr
    exact ih (good_step hx he) (sval_step (noBadFacts_of_good hx) hv he)

theorem val_of_flush0 {i : MSIState n} {s : SeqState n} (hf : flush0 i s) : val i = s.memory := by
  rw [val_of_quiet (good_of_flush0 hf) (quiet_of_flush0 hf)]
  obtain ⟨_, _, hv⟩ := hf
  exact hv

/-! ## Le relazioni di ARS -/

theorem msi_relation_init : relation_init flush (default : MSIState n) (seq_init n) := by
  unfold relation_init flush
  refine ⟨⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ => rfl⟩

/-- `relation_flush`: da uno stato flushed, dopo passi interni, si torna a flushed per lo stesso `s`
(`reach_quiet`, e il parent vale `val`, che i passi interni non cambiano). -/
theorem msi_relation_flush (i i' : MSIState n) (s : SeqState n) :
    relation_flush flush i i' s (msi_rule n) := by
  unfold relation_flush
  intro hf htr
  have hi : Good i := good_of_flush0 hf.1
  have hi' : Good i' := good_trans hi htr
  obtain ⟨y, hy, hq⟩ := reach_quiet hi'
  have hyG : Good y := good_trans hi' hy
  refine ⟨y, hy, flush0_of_quiet hq ?_, ?_⟩
  · rw [← val_of_quiet hyG hq, val_trans hi' hy, val_trans hi htr, val_of_flush0 hf.1]
  · intro k
    rw [ext_trans hy k, ext_trans htr k, hf.2 k]

theorem ext_step_ext {i' i'' : MSIState n} {s s' : SeqState n} {e : Event} {k : Fin n}
    (hext : ∀ k, (i'.caches k).extqueue = s.extqueue k) (h : msi_step_external i' (.cache e k) i'')
    (hs : seq_step s (.cache e k) s') : ∀ k', (i''.caches k').extqueue = s'.extqueue k' := by
  intro k'
  cases h with
  | cache _ c' _ hc' =>
    by_cases hk : k' = k
    · rw [hk]
      cases hc' with
      | ld_rq =>
        cases hs with
        | ld_rq => simp only [update_Fin_gss, hext k]
      | st_rq v =>
        cases hs with
        | st_rq => simp only [update_Fin_gss, hext k]
      | ld_rq_data_available1 rst hrq hS =>
        cases hs with
        | ld_rs _ _ rst' hrq' hm' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
      | ld_rq_data_available rst hrq hM =>
        cases hs with
        | ld_rs _ _ rst' hrq' hm' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
      | st_rq_M_state v rst hrq hM =>
        cases hs with
        | st_rs v' _ rst' hrq' =>
          rw [hext k] at hrq
          rw [hrq] at hrq'
          obtain ⟨_, hr⟩ := List.cons.inj hrq'
          subst hr
          simp only [update_Fin_gss, hext k]
    · have hs' : s'.extqueue k' = s.extqueue k' := by
        cases hs <;> simp only [update_Fin_gso2 _ _ _ _ hk]
      rw [hs']
      simp only [update_Fin_gso2 _ _ _ _ hk]
      exact hext k'

/-- La memoria dello spec dopo un passo: cambia solo con `st_rs`, nel valore in testa alla coda. -/
theorem spec_memory {s s' : SeqState n} {e : Event} {k : Fin n} (hs : seq_step s (.cache e k) s') :
    (e ≠ Event.st_rs → s'.memory = s.memory)
    ∧ (e = Event.st_rs → ∃ v rst, (s.extqueue k).rq = Event.st_rq v :: rst ∧ s'.memory = v) := by
  cases hs with
  | ld_rq => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | st_rq v => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | ld_rs v _ rst hrq hm => exact ⟨fun _ => rfl, fun h => Event.noConfusion h⟩
  | st_rs v _ rst hrq => exact ⟨fun hne => absurd rfl hne, fun _ => ⟨v, rst, hrq, rfl⟩⟩

/-- Il valore restituito da una load servita in `i'` (raggiunto con passi interni da `i` flushed
per `s`) è `s.memory`: la cache è in `S` (`SVal`) o in `M` (`val`), e `val` non cambia. -/
theorem load_value {i i' : MSIState n} {s : SeqState n} {k : Fin n} (hf : flush i s)
    (htr : trans_refl (msi_rule n) i i') (hk : (i'.caches k).state ≠ Bstate.I) :
    (i'.caches k).value = s.memory := by
  have hi : Good i := good_of_flush0 hf.1
  have hi' : Good i' := good_trans hi htr
  have hv : SVal i' := sval_trans hi (sval_of_quiet (quiet_of_flush0 hf.1)) htr
  rw [← val_of_flush0 hf.1, ← val_trans hi htr]
  cases h : (i'.caches k).state with
  | I => exact absurd h hk
  | S => exact val_of_S hi' hv h
  | M => exact val_of_M hi' h

/-- `relation_method_int`: lo spec può fare lo stesso passo esterno. -/
theorem msi_relation_method_int (i i' i'' : MSIState n) (s : SeqState n) (e : MSIExternalEvent n) :
    ReachingStar.relation_method_int flush (msi_rule n) msi_step_external seq_step i i' i'' s e := by
  unfold ReachingStar.relation_method_int
  intro hf htr h
  have hext : ∀ k, (i'.caches k).extqueue = s.extqueue k :=
    fun k => (ext_trans htr k).trans (hf.2 k)
  cases e with
  | cache ev k =>
    cases h with
    | cache _ c' _ hc' =>
      cases hc' with
      | ld_rq => exact ⟨_, seq_step.ld_rq s k⟩
      | st_rq v => exact ⟨_, seq_step.st_rq s v k⟩
      | ld_rq_data_available1 rst hrq hS =>
        exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq)
          (load_value hf htr (by rw [hS]; decide)).symm⟩
      | ld_rq_data_available rst hrq hM =>
        exact ⟨_, seq_step.ld_rs s _ k rst (by rw [← hext k]; exact hrq)
          (load_value hf htr (by rw [hM]; decide)).symm⟩
      | st_rq_M_state v rst hrq hM =>
        exact ⟨_, seq_step.st_rs s v k rst (by rw [← hext k]; exact hrq)⟩

/-- `relation_flush_method_int`: dopo lo stesso passo esterno in `i'` e in `s`, con passi interni si
torna a flushed per `s'` (`reach_quiet`; il parent vale `val`, che è `s'.memory` per `val_ext` e
`spec_memory`). -/
theorem msi_relation_flush_method_int (i i' i'' : MSIState n) (s s' : SeqState n)
    (e : MSIExternalEvent n) :
    ReachingStar.relation_flush_method_int flush (msi_rule n) msi_step_external seq_step
      i i' i'' s s' e := by
  unfold ReachingStar.relation_flush_method_int
  intro hf htr hstep hs
  have hi : Good i := good_of_flush0 hf.1
  have hi' : Good i' := good_trans hi htr
  have hi'' : Good i'' := good_step_ext hi' hstep
  have hext : ∀ k, (i'.caches k).extqueue = s.extqueue k :=
    fun k => (ext_trans htr k).trans (hf.2 k)
  obtain ⟨y, hy, hq⟩ := reach_quiet hi''
  have hyG : Good y := good_trans hi'' hy
  refine ⟨y, hy, flush0_of_quiet hq ?_, ?_⟩
  · rw [← val_of_quiet hyG hq, val_trans hi'' hy]
    cases e with
    | cache ev k =>
      obtain ⟨hne, hst⟩ := val_ext hi' hstep
      obtain ⟨sne, sst⟩ := spec_memory hs
      by_cases hev : ev = Event.st_rs
      · obtain ⟨v, rst, hrq, hv⟩ := hst hev
        obtain ⟨v', rst', hrq', hm⟩ := sst hev
        rw [hext k] at hrq
        rw [hv, hm]
        exact Event.st_rq.inj (List.cons.inj (hrq.symm.trans hrq')).1
      · rw [hne hev, val_trans hi htr, val_of_flush0 hf.1, sne hev]
  · cases e with
    | cache ev k =>
      intro k'
      rw [ext_trans hy k']
      exact ext_step_ext hext hstep hs k'

/-! ## Il teorema -/

/-- **L'inclusione delle tracce di MSI (modello bag) nello spec sequenziale.** -/
theorem trace_inclusion (l : List (MSIExternalEvent n)) :
  imp_behaviour n l -> spec_behaviour n l := by
  intro himp
  have conv_imp : ∀ (a b : MSIState n) (l : List (MSIExternalEvent n)),
      star_extend msi_step_external msi_step_internal a l b →
      ReachingStar.star_extend (msi_rule n) msi_step_external a l b := by
    intro a b l h
    induction h with
    | refl => exact ReachingStar.star_extend.refl a
    | step_int l₁ s₁ s₂ ie _ hstep ih =>
      exact ReachingStar.star_extend.step_int a l₁ s₁ s₂ ih
        (trans_refl.step (msi_rule_of_step hstep) trans_refl.refl)
    | step_ext l₁ s₁ s₂ e _ hstep ih => exact ReachingStar.star_extend.step_ext a l₁ s₁ s₂ e ih hstep
  have conv_spec : ∀ (a b : SeqState n) (l : List (MSIExternalEvent n)),
      ReachingStar.star seq_step a l b → star seq_step a l b := by
    intro a b l h
    induction h with
    | refl => exact star.refl a
    | step s₂ s₃ l₁ e₁ _ hstep ih => exact star.step a s₂ s₃ l₁ e₁ ih hstep
  have himp' : ReachingStar.imp_behaviour (msi_rule n) msi_step_external l (default : MSIState n) := by
    unfold imp_behaviour behaviour_extend at himp
    obtain ⟨s', hs'⟩ := himp
    exact ⟨s', conv_imp _ _ _ hs'⟩
  have hspec := ReachingStar.trace_inclusion flush (msi_rule n) msi_step_external seq_step l
    (default : MSIState n) (seq_init n) msi_relation_flush msi_relation_flush_method_int
    msi_relation_method_int msi_confluent msi_commutes_upto msi_relation_init himp'
  obtain ⟨s', hs'⟩ := hspec
  unfold spec_behaviour behaviour
  exact ⟨s', conv_spec _ _ _ hs'⟩

end MSIBag
