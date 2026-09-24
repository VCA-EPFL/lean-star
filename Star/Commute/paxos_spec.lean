import Star.Commute.paxos
import Star.SplitJoin.star
import Star.Commute.ARS

open Relation
/- Solo i nomi del framework che servono: `open ReachingStar` intero renderebbe ambigui `star` e
`star_extend`, definiti anche in `Star/SplitJoin/star.lean` (usato da `spec_behaviour`). -/
open ReachingStar (Rule Method trans_refl relation_flush relation_flush_method relation_method
  relation_init)


/-!
# Spec di Paxos: consenso centralizzato con soli passi esterni

Lo spec di `paxos.lean` come algoritmo centralizzato: niente messaggi, niente ballot, niente
guasti. Come `seq_step` in `MSI_flush_proof.lean` ha **solo passi esterni**, con le stesse
etichette (`PaxosExternalEvent`) e le stesse regole (`propose_rq`, `decide_rs`) di
`paxos_step_external`, e nessun passo interno (`spec_behaviour` usa `behaviour` di `star.lean`,
senza passi interni). Con `propose_rq v` il partecipante `i` scrive il valore che vuole
proporre (`pref`, una volta sola); con `decide_rs v` decide `v` (una volta sola) e lo consegna
all'esterno, registrandolo in `rs` come il learner dell'implementazione. La prima `decide_rs`
fissa il valore scelto (`chosen`, il punto di linearizzazione), che deve essere uno dei valori
proposti; le successive devono decidere lo stesso valore. L'interfaccia esterna (`Iface`) è
quella dell'implementazione. In fondo al file la relazione di flush e le relazioni del framework
`ARS` (`relation_method`, `relation_flush_method`, `relation_init`, `relation_flush`) istanziate
su Paxos, come in `MSI_flush_proof.lean`.
-/

structure SpecParticipant where
  pref : Option Value      -- il valore che vuole proporre (scritto dall'esterno)
  decision : Option Value  -- la decisione presa
  rs : List Value          -- decisioni consegnate all'esterno (registro delle `decide_rs`)

instance : Inhabited SpecParticipant where
  default := ⟨none, none, []⟩

structure SpecState (n : Nat) where
  parts : Fin n → SpecParticipant
  chosen : Option Value    -- il valore scelto (`none`: nessuna decisione ancora)

instance : Inhabited (SpecState n) where
  default := ⟨fun _ => default, none⟩

/-- L'interfaccia esterna del partecipante `i`, la stessa di `PaxosState.iface`. -/
def SpecState.iface {n} (s : SpecState n) (i : Fin n) : Iface :=
  ⟨(s.parts i).pref, (s.parts i).rs⟩

/-- Stato iniziale: nessuna proposta, nessuna decisione, nessuna scelta. -/
@[simp]
def spec_init (s : SpecState n) : Prop :=
  (∀ k, (s.parts k).pref = none ∧ (s.parts k).decision = none ∧ (s.parts k).rs = [])
  ∧ s.chosen = none

/-- I passi dello spec: solo quelli esterni, gli stessi di `paxos_step_external`. -/
inductive spec_step : SpecState n → PaxosExternalEvent n → SpecState n → Prop where
  -- l'esterno scrive il valore che il partecipante `i` vuole proporre (una volta sola)
  | propose_rq : ∀ (s : SpecState n) i v,
      (s.parts i).pref = none →
      spec_step s (.part (.propose_rq v) i)
        { s with parts := update_Fin i { s.parts i with pref := some v } s.parts }
  -- il partecipante `i` decide `v` (una volta sola) e lo consegna all'esterno: `v` è stato
  -- proposto da qualcuno (`j`) ed è il valore scelto, oppure non è ancora stato scelto nulla e
  -- `v` diventa il valore scelto
  | decide_rs : ∀ (s : SpecState n) i j v,
      (s.parts i).decision = none →
      (s.parts j).pref = some v →
      (s.chosen = none ∨ s.chosen = some v) →
      spec_step s (.part (.decide_rs v) i)
        { s with parts := update_Fin i { s.parts i with decision := some v,
                                                        rs := (s.parts i).rs ++ [v] } s.parts,
                 chosen := some v }

def Spec {n : Nat} : Paxos.LTS (PaxosExternalEvent n) where
  S := SpecState n
  transitions := spec_step
  init s := spec_init s

/-- I comportamenti dello spec (`behaviour` di `star.lean`): solo passi esterni, come
`spec_behaviour` in `MSI_flush_proof.lean`. -/
def spec_behaviour (n : Nat) :=
  behaviour (default : SpecState n) spec_step

/-- I comportamenti dell'implementazione (`behaviour_extend` di `star.lean`, come `imp_behaviour`
in MSI): passi esterni `paxos_step_external`, passi interni `paxos_step`. -/
def imp_behaviour (n : Nat) :=
  behaviour_extend (default : PaxosState n) paxos_step_external paxos_step

/-- `default` è uno stato iniziale. -/
theorem spec_init_default {n} : spec_init (default : SpecState n) :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

@[simp] theorem SpecParticipant.default_pref : (default : SpecParticipant).pref = none := rfl
@[simp] theorem SpecParticipant.default_decision : (default : SpecParticipant).decision = none := rfl
@[simp] theorem SpecParticipant.default_rs : (default : SpecParticipant).rs = [] := rfl
@[simp] theorem SpecState.default_parts {n} (i : Fin n) : (default : SpecState n).parts i = default := rfl
@[simp] theorem SpecState.default_chosen {n} : (default : SpecState n).chosen = none := rfl


/-! ## Sicurezza dello spec

Ogni decisione presa, e ogni decisione consegnata all'esterno, è il valore scelto; il valore
scelto è uno dei valori proposti. Ne segue la correttezza: due partecipanti che decidono, decidono
lo stesso valore. -/

structure specInv (s : SpecState n) : Prop where
  decision_chosen : ∀ i v, (s.parts i).decision = some v → s.chosen = some v
  rs_chosen : ∀ i v, v ∈ (s.parts i).rs → s.chosen = some v
  chosen_pref : ∀ v, s.chosen = some v → ∃ i, (s.parts i).pref = some v

theorem specInv_default {n} : specInv (default : SpecState n) where
  decision_chosen := fun _ _ h => by simp at h
  rs_chosen := fun _ _ h => by simp at h
  chosen_pref := fun _ h => by simp at h

theorem specInv_step {n} {s s' : SpecState n} {t : PaxosExternalEvent n}
    (hI : specInv s) (h : spec_step s t s') : specInv s' := by
  cases h with
  | propose_rq i v hp =>
    refine ⟨?_, ?_, ?_⟩
    · intro k w hw
      by_cases hk : k = i
      · subst hk; simp only [update_Fin_gss] at hw; exact hI.decision_chosen k w hw
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hw; exact hI.decision_chosen k w hw
    · intro k w hw
      by_cases hk : k = i
      · subst hk; simp only [update_Fin_gss] at hw; exact hI.rs_chosen k w hw
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hw; exact hI.rs_chosen k w hw
    · intro w hw
      obtain ⟨k, hk⟩ := hI.chosen_pref w hw
      refine ⟨k, ?_⟩
      by_cases hki : k = i
      · subst hki; rw [hp] at hk; cases hk
      · simp only [update_Fin_gso2 _ _ _ _ hki]; exact hk
  | decide_rs i j v hd hp hch =>
    -- il valore scelto, se c'era già, è `v`
    have hchosen : ∀ w, s.chosen = some w → w = v := by
      intro w hw
      rcases hch with hn | hv
      · rw [hn] at hw; cases hw
      · rw [hv] at hw; exact (Option.some.inj hw).symm
    refine ⟨?_, ?_, ?_⟩
    · intro k w hw
      by_cases hk : k = i
      · subst hk
        simp only [update_Fin_gss, Option.some.injEq] at hw
        subst hw
        rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hw
        have := hchosen w (hI.decision_chosen k w hw)
        subst this
        rfl
    · intro k w hw
      by_cases hk : k = i
      · subst hk
        simp only [update_Fin_gss, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hchosen w (hI.rs_chosen k w hw)
          subst this
          rfl
        · rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hw
        have := hchosen w (hI.rs_chosen k w hw)
        subst this
        rfl
    · intro w hw
      simp only [Option.some.injEq] at hw
      subst hw
      refine ⟨j, ?_⟩
      by_cases hji : j = i
      · subst hji; simp only [update_Fin_gss]; exact hp
      · simp only [update_Fin_gso2 _ _ _ _ hji]; exact hp

/-- Ogni stato iniziale è `default`. -/
theorem spec_eq_default_of_init {n} {s : SpecState n} (h : spec_init s) : s = default := by
  obtain ⟨hp, hch⟩ := h
  obtain ⟨parts, chosen⟩ := s
  simp only at hp hch
  subst hch
  have e1 : parts = fun _ => default := by
    funext k
    obtain ⟨h1, h2, h3⟩ := hp k
    generalize parts k = p at h1 h2 h3 ⊢
    obtain ⟨pf, d, rs⟩ := p
    try dsimp only at h1 h2 h3
    subst h1 h2 h3
    rfl
  subst e1
  rfl

theorem specInv_of_reachable {n} {s : SpecState n} (h : Spec.reachable s) : specInv s := by
  have key : ∀ x, ReflTransGen Spec.atrans (default : SpecState n) x → specInv x := by
    intro x hx
    induction hx with
    | refl => exact specInv_default
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      exact specInv_step ih ht
  exact key s (h _ spec_init_default)

/-- Correttezza dello spec: due partecipanti che hanno deciso, hanno deciso lo stesso valore. -/
theorem spec_correctness {n} {s : SpecState n} (h : Spec.reachable s) :
    ∀ i j v w, (s.parts i).decision = some v → (s.parts j).decision = some w → v = w := by
  intro i j v w hi hj
  have hI := specInv_of_reachable h
  have e₁ := hI.decision_chosen i v hi
  have e₂ := hI.decision_chosen j w hj
  exact Option.some.inj (e₁.symm.trans e₂)

/-- Il valore deciso è uno dei valori proposti. -/
theorem spec_validity {n} {s : SpecState n} (h : Spec.reachable s) :
    ∀ i v, (s.parts i).decision = some v → ∃ j, (s.parts j).pref = some v := by
  intro i v hi
  have hI := specInv_of_reachable h
  exact hI.chosen_pref v (hI.decision_chosen i v hi)


/-! ## Un'esecuzione

Con un solo partecipante: l'esterno chiede di proporre `7` e il partecipante decide `7`: gli
stessi eventi esterni dell'esecuzione `decision_reachable_one` dell'implementazione. -/
theorem spec_decision_reachable_one :
    ∃ s : SpecState 1, ReflTransGen Spec.atrans (default : SpecState 1) s
      ∧ (s.parts 0).decision = some 7 ∧ (s.parts 0).rs = [7] := by
  have c0 : ReflTransGen Spec.atrans (default : SpecState 1) _ :=
    ReflTransGen.tail ReflTransGen.refl (Exists.intro (.part (.propose_rq 7) 0)
      (spec_step.propose_rq _ 0 7 rfl))
  have c1 : ReflTransGen Spec.atrans (default : SpecState 1) _ :=
    ReflTransGen.tail c0 (Exists.intro (.part (.decide_rs 7) 0)
      (spec_step.decide_rs _ 0 0 7 rfl rfl (Or.inl rfl)))
  exact ⟨_, c1, rfl, rfl⟩

/-- La stessa esecuzione come comportamento (`star` accoda gli eventi in testa: la lista è in
ordine inverso). -/
theorem spec_behaviour_one : spec_behaviour 1 [.part (.decide_rs 7) 0, .part (.propose_rq 7) 0] :=
  ⟨_, star.step _ _ _ _ _
        (star.step _ _ _ _ _ (star.refl _) (spec_step.propose_rq _ 0 7 rfl))
        (spec_step.decide_rs _ 0 0 7 rfl rfl (Or.inl rfl))⟩


/-! ## Le relazioni del framework (`Star/Commute/ARS.lean`) istanziate su Paxos

`flush` è la relazione di flush tra implementazione e spec, `paxos_step_external` e `spec_step`
sono i `Method` di implementazione e spec (entrambi etichettati da `PaxosExternalEvent n`),
`paxos_rule` è la `Rule` interna. Gli enunciati che seguono sono esattamente `relation_method`,
`relation_flush_method`, `relation_init` e `relation_flush` di ARS, come in
`MSI_flush_proof.lean`. A differenza di MSI, `relation_flush` vale in forma forte (ogni sequenza
di passi interni conserva il flush con lo stesso `s`): i passi interni di Paxos non toccano né
l'interfaccia (`pref`, `rs`) né le decisioni. -/

/-- Le regole interne di Paxos come `Rule` del framework: un passo interno con una qualunque
etichetta. -/
def paxos_rule (n : Nat) : Rule (PaxosState n) := fun a b => ∃ e, paxos_step a e b

theorem paxos_rule_of_step {a b : PaxosState n} {e : PaxosEvent n}
    (h : paxos_step a e b) : paxos_rule n a b :=
  Exists.intro e h

/-! ### Lemmi sull'implementazione -/

/-- I passi interni non toccano `pref`, `decision` e `rs` di nessun partecipante. -/
theorem paxos_step_iface {n} {s s' : PaxosState n} {t : PaxosEvent n} (h : paxos_step s t s')
    (k : Fin n) :
    (s'.proposers k).pref = (s.proposers k).pref
      ∧ (s'.learners k).decision = (s.learners k).decision
      ∧ (s'.learners k).rs = (s.learners k).rs := by
  cases h with
  | proposer p' net' e i hc hp =>
    refine ⟨?_, rfl, rfl⟩
    by_cases hk : k = i
    · rw [hk]; simp only [update_Fin_gss]; cases hp <;> rfl
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | acceptor ac' net' e a hc ha => exact ⟨rfl, rfl, rfl⟩
  | learner l' net' e l hc hl =>
    refine ⟨rfl, ?_, ?_⟩
    · by_cases hk : k = l
      · rw [hk]; simp only [update_Fin_gss]; cases hl; rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · by_cases hk : k = l
      · rw [hk]; simp only [update_Fin_gss]; cases hl; rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
  | crash i hc => exact ⟨rfl, rfl, rfl⟩

/-- Ogni valore proposto in fase 2a (`propose b v` in una outbox) è il `pref` di qualche
proposer: `pref` non viene mai cancellato, e il valore proposto è il `pref` del proposer oppure
il valore di un voto riportato, che a sua volta era stato proposto (`maxAcc_msg` di `invS`,
`report_vote` e `vote_propose` di `invE`). Serve per la validità: il valore deciso è uno dei
valori proposti dall'esterno. -/
def propose_pref {n} (s : PaxosState n) : Prop :=
  ∀ i b v, PMessage.propose b v ∈ s.network.pmsgs i → ∃ j, (s.proposers j).pref = some v

theorem propose_pref_default {n} : propose_pref (default : PaxosState n) :=
  fun _ _ _ h => by simp at h

theorem propose_pref_step {n} {s s' : PaxosState n} {t : PaxosEvent n}
    (hE : invE s) (hS : invS s) (hP : propose_pref s) (h : paxos_step s t s') : propose_pref s' := by
  intro k b' v hm
  -- `pref` non cambia: basta trovare il proposer in `s`
  suffices hs : ∃ j, (s.proposers j).pref = some v by
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, ((paxos_step_iface h j).1).trans hj⟩
  cases t with
  | proposer e i =>
    cases e with
    | prepare b =>
      obtain ⟨_, _, rfl⟩ := prepare_inv h
      apply hP k b' v
      simp only [prepareSt] at hm
      by_cases hk : k = i
      · rw [hk] at hm ⊢
        simp only [update_Fin_gss, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hm
        · cases hm
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hm; exact hm
    | collect_promise a b acc =>
      obtain ⟨_, _, _, _, hcase⟩ := collect_inv h
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hP k b' v hm
      · exact hP k b' v hm
    | accept b v₀ =>
      obtain ⟨_, hb, _, _, hpv, rfl⟩ := accept_inv h
      simp only [acceptSt] at hm
      by_cases hk : k = i
      · rw [hk] at hm
        simp only [update_Fin_gss, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hP i b' v hm
        · -- il messaggio nuovo: `v` è il valore proposto ora
          have hv : v = v₀ := by cases hm; rfl
          rw [hv]
          cases hmax : (s.proposers i).maxAcc with
          | none =>
            refine ⟨i, ?_⟩
            rw [hmax] at hpv
            exact hpv
          | some x =>
            obtain ⟨bx, vx⟩ := x
            have hvx : v₀ = vx := proposeValue_some hpv (bx, vx) hmax
            obtain ⟨a, _, hprom⟩ := hS.maxAcc_msg i b (bx, vx) hb hmax
            have hvote := hE.report_vote a b bx vx hprom
            obtain ⟨i', hi'⟩ := hE.vote_propose a bx vx hvote
            obtain ⟨j, hj⟩ := hP i' bx vx hi'
            exact ⟨j, by rw [hvx]; exact hj⟩
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hm; exact hP k b' v hm
  | acceptor e a =>
    cases e with
    | promise b =>
      obtain ⟨_, _, _, rfl⟩ := promise_inv h
      exact hP k b' v hm
    | vote b v₀ =>
      obtain ⟨_, _, _, rfl⟩ := vote_inv h
      exact hP k b' v hm
  | learner e l =>
    cases e with
    | collect_accepted a b v₀ =>
      obtain ⟨_, _, _, rfl⟩ := lcollect_inv h
      exact hP k b' v hm
  | crash i =>
    obtain ⟨_, rfl⟩ := crash_inv h
    exact hP k b' v hm

theorem propose_pref_step_ext {n} {s s' : PaxosState n} {t : PaxosExternalEvent n}
    (hP : propose_pref s) (h : paxos_step_external s t s') : propose_pref s' := by
  intro k b v hm
  cases h with
  | propose_rq i w hc hp =>
    obtain ⟨j, hj⟩ := hP k b v hm
    refine ⟨j, ?_⟩
    by_cases hji : j = i
    · rw [hji] at hj; rw [hp] at hj; cases hj
    · simp only [update_Fin_gso2 _ _ _ _ hji]; exact hj
  | decide_rs i b₀ w hc hd hq =>
    exact hP k b v hm

/-- Ogni stato raggiungibile soddisfa `propose_pref`. -/
theorem propose_pref_of_reachable {n} {s : PaxosState n} (h : Paxos.reachable s) : propose_pref s := by
  have key : ∀ x, ReflTransGen Paxos.atrans (default : PaxosState n) x →
      invE x ∧ invS x ∧ propose_pref x := by
    intro x hx
    induction hx with
    | refl => exact ⟨invE_default, invS_default, propose_pref_default⟩
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      cases ht
      · exact ⟨invE_step ih.1 ‹_›, invS_step ih.1 ih.2.1 ‹_›,
          propose_pref_step ih.1 ih.2.1 ih.2.2 ‹_›⟩
      · exact ⟨invE_step_ext ih.1 ‹_›, invS_step_ext ih.2.1 ‹_›, propose_pref_step_ext ih.2.2 ‹_›⟩
  exact (key s (h _ paxos_init_default)).2.2

/-- Un quorum di voti per `v` in un learner: `v` è il `pref` di qualche proposer. -/
theorem pref_of_quorum {n} {s : PaxosState n} {l : Fin n} {b : Ballot} {v : Value}
    (hE : invE s) (hP : propose_pref s) (hq : isQuorum n (count ((s.learners l).accepts (b, v)))) :
    ∃ j, (s.proposers j).pref = some v := by
  obtain ⟨a, ha⟩ := agreement_of_inv_aux1 _ hq
  obtain ⟨i, hi⟩ := hE.vote_propose a b v (hE.accepts_vote l b v a ha)
  exact hP i b v hi

/-- Un quorum di voti per `v` e una decisione `w` (di un learner qualsiasi): `v = w`. È la
sicurezza di Paxos (`agreement_of_inv`). -/
theorem decision_eq_of_quorum {n} {s : PaxosState n} {l l' : Fin n} {b : Ballot} {v w : Value}
    (hE : invE s) (hS : invS s) (hq : isQuorum n (count ((s.learners l).accepts (b, v))))
    (hd : (s.learners l').decision = some w) : v = w := by
  obtain ⟨b', hq'⟩ := hE.decision_quorum l' w hd
  exact agreement_of_inv hE hS v w (chosen_of_quorum hE hq) (chosen_of_quorum hE hq')

/-! ### Lemmi di inversione sui passi dello spec -/

theorem spec_propose_rq_inv {n} {s s' : SpecState n} {i : Fin n} {v : Value}
    (h : spec_step s (.part (.propose_rq v) i) s') :
    (s.parts i).pref = none
      ∧ s' = { s with parts := update_Fin i { s.parts i with pref := some v } s.parts } := by
  cases h
  exact ⟨‹_›, rfl⟩

theorem spec_decide_rs_inv {n} {s s' : SpecState n} {i : Fin n} {v : Value}
    (h : spec_step s (.part (.decide_rs v) i) s') :
    (s.parts i).decision = none ∧ (∃ j, (s.parts j).pref = some v)
      ∧ (s.chosen = none ∨ s.chosen = some v)
      ∧ s' = { s with parts := update_Fin i { s.parts i with decision := some v,
                                                              rs := (s.parts i).rs ++ [v] } s.parts,
                      chosen := some v } := by
  cases h
  exact ⟨‹_›, ⟨_, ‹_›⟩, ‹_›, rfl⟩

/-! ### La relazione di flush -/

/-- La relazione di flush. Uno stato `i` dell'implementazione e uno `s` dello spec sono in
relazione se `i` è raggiungibile (servono gli invarianti di Paxos, cioè la sicurezza), se
coincidono sull'interfaccia e sulle decisioni di ogni partecipante (`pref`, `decision`, `rs`), e
se il valore scelto dello spec è il valore deciso da qualche learner (`none` se nessuno ha ancora
deciso). Non vincola messaggi, ballot, promesse, voti né i crash: i passi interni non toccano
nulla di ciò che la relazione guarda. -/
inductive flush (i : PaxosState n) (s : SpecState n) : Prop where
  | intro :
      Paxos.reachable i →
      (∀ k, (s.parts k).pref = (i.proposers k).pref
            ∧ (s.parts k).decision = (i.learners k).decision
            ∧ (s.parts k).rs = (i.learners k).rs) →
      (∀ v, s.chosen = some v ↔ ∃ l, (i.learners l).decision = some v) →
      flush i s

/-- `relation_init` di ARS: gli stati iniziali sono in relazione. -/
theorem paxos_relation_init : relation_init flush (default : PaxosState n) (default : SpecState n) := by
  unfold relation_init
  refine ⟨?_, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro s₀ h₀
    have e := eq_default_of_init h₀
    subst e
    exact ReflTransGen.refl
  · intro v
    constructor
    · intro h; simp at h
    · intro ⟨l, hl⟩; simp at hl

/-- Un passo interno conserva il flush con lo stesso `s`. -/
theorem flush_step {n} {i i' : PaxosState n} {s : SpecState n} {t : PaxosEvent n}
    (hf : flush i s) (h : paxos_step i t i') : flush i' s := by
  obtain ⟨hr, hif, hch⟩ := hf
  refine ⟨fun s₀ h₀ => ReflTransGen.tail (hr s₀ h₀)
            (Exists.intro (.int t) (paxos_step_all.int _ _ _ h)), ?_, ?_⟩
  · intro k
    obtain ⟨h1, h2, h3⟩ := paxos_step_iface h k
    rw [h1, h2, h3]
    exact hif k
  · intro v
    rw [hch v]
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, by rw [(paxos_step_iface h l).2.1]; exact hl⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, by rw [← (paxos_step_iface h l).2.1]; exact hl⟩

/-- `relation_flush` di ARS (ritorno a flush dopo passi interni), qui in forma forte: ogni sequenza
di passi interni conserva il flush, quindi si torna a flush con zero passi. -/
theorem paxos_relation_flush (i i' : PaxosState n) (s : SpecState n) :
    relation_flush flush i i' s (paxos_rule n) := by
  unfold relation_flush
  intro hf htr
  -- forma forte: `i'` stesso è già flushed, zero passi di ritorno
  refine ⟨i', trans_refl.refl, ?_⟩
  revert hf
  induction htr with
  | refl => exact id
  | step hab _ ih =>
    intro hf
    obtain ⟨t, ht⟩ := hab
    exact ih (flush_step hf ht)

/-- `relation_method` di ARS: ogni passo esterno dell'implementazione da uno stato flushed è
possibile anche nello spec. Per `decide_rs v` servono gli invarianti: il quorum per `v` dà un
proposer con `pref = some v` (`pref_of_quorum`) e, se lo spec ha già scelto `w`, qualche learner
ha deciso `w`, quindi `v = w` (`decision_eq_of_quorum`). -/
theorem paxos_relation_method (i i' : PaxosState n) (s : SpecState n) (e : PaxosExternalEvent n) :
    relation_method flush paxos_step_external spec_step i i' s e := by
  unfold relation_method
  intro hf h
  obtain ⟨hr, hif, hch⟩ := hf
  cases h with
  | propose_rq k v hc hp =>
    refine ⟨_, spec_step.propose_rq s k v ?_⟩
    rw [(hif k).1]; exact hp
  | decide_rs k b v hc hd hq =>
    obtain ⟨hE, hS⟩ := inv_of_reachable hr
    obtain ⟨j, hj⟩ := pref_of_quorum hE (propose_pref_of_reachable hr) hq
    refine ⟨_, spec_step.decide_rs s k j v ?_ ?_ ?_⟩
    · rw [(hif k).2.1]; exact hd
    · rw [(hif j).1]; exact hj
    · cases hchs : s.chosen with
      | none => exact Or.inl rfl
      | some w =>
        obtain ⟨l', hl'⟩ := (hch w).1 hchs
        exact Or.inr (by rw [decision_eq_of_quorum hE hS hq hl'])

/-- `relation_flush_method` di ARS: dopo lo stesso passo esterno in `i` e in `s` si è di nuovo
flushed, con zero passi interni (`i'' = i'`, `trans_refl.refl`). -/
theorem paxos_relation_flush_method (i i' : PaxosState n) (s s' : SpecState n)
    (e : PaxosExternalEvent n) :
    relation_flush_method flush (paxos_rule n) paxos_step_external spec_step i i' s s' e := by
  unfold relation_flush_method
  intro hf h hs
  obtain ⟨hr, hif, hch⟩ := hf
  refine ⟨i', trans_refl.refl, ?_⟩
  have hr' : Paxos.reachable i' := fun s₀ h₀ =>
    ReflTransGen.tail (hr s₀ h₀) (Exists.intro (.ext e) (paxos_step_all.ext _ _ _ h))
  cases h with
  | propose_rq k v hc hp =>
    obtain ⟨_, rfl⟩ := spec_propose_rq_inv hs
    refine ⟨hr', ?_, ?_⟩
    · intro j
      refine ⟨?_, ?_, ?_⟩
      · by_cases hjk : j = k
        · rw [hjk]; simp only [update_Fin_gss]
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j).1
      · by_cases hjk : j = k
        · rw [hjk]; simp only [update_Fin_gss]; exact (hif k).2.1
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j).2.1
      · by_cases hjk : j = k
        · rw [hjk]; simp only [update_Fin_gss]; exact (hif k).2.2
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j).2.2
    · intro w
      exact hch w
  | decide_rs k b v hc hd hq =>
    obtain ⟨_, _, hch₀, rfl⟩ := spec_decide_rs_inv hs
    refine ⟨hr', ?_, ?_⟩
    · intro j'
      refine ⟨?_, ?_, ?_⟩
      · by_cases hjk : j' = k
        · rw [hjk]; simp only [update_Fin_gss]; exact (hif k).1
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j').1
      · by_cases hjk : j' = k
        · rw [hjk]; simp only [update_Fin_gss]
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j').2.1
      · by_cases hjk : j' = k
        · rw [hjk]; simp only [update_Fin_gss]; rw [(hif k).2.2]
        · simp only [update_Fin_gso2 _ _ _ _ hjk]; exact (hif j').2.2
    · intro w
      constructor
      · intro hw
        simp only [Option.some.injEq] at hw
        subst hw
        exact ⟨k, by simp only [update_Fin_gss]⟩
      · rintro ⟨l', hl'⟩
        by_cases hlk : l' = k
        · rw [hlk] at hl'
          simp only [update_Fin_gss] at hl'
          exact hl'
        · simp only [update_Fin_gso2 _ _ _ _ hlk] at hl'
          have hsw : s.chosen = some w := (hch w).2 ⟨l', hl'⟩
          rcases hch₀ with hn | hv
          · rw [hn] at hsw; cases hsw
          · rw [hv] at hsw; exact hsw

/-! ### Inclusione delle tracce

`ReachingStar.trace_inclusion` di ARS, come `trace_inclusion` in `MSI_flush_proof.lean`. I
comportamenti di ARS usano `star`/`star_extend` di `ReachingStar` (passi interni in `trans_refl`),
quelli qui sopra `star`/`star_extend` di `star.lean` (passi interni uno alla volta): i due lemmi
ponte passano dall'uno all'altro. -/

/-- Da `star_extend` di `star.lean` a quello di ARS (ogni passo interno è un `trans_refl` di un
passo). -/
theorem star_extend_ars {n} {a b : PaxosState n} {l : List (PaxosExternalEvent n)}
    (h : star_extend paxos_step_external paxos_step a l b) :
    ReachingStar.star_extend (paxos_rule n) paxos_step_external a l b := by
  induction h with
  | refl => exact ReachingStar.star_extend.refl _
  | step_int l s' s'' ie _ hstep ih =>
    exact ReachingStar.star_extend.step_int _ l s' s'' ih
      (trans_refl.step (paxos_rule_of_step hstep) trans_refl.refl)
  | step_ext l s' s'' e _ hstep ih =>
    exact ReachingStar.star_extend.step_ext _ l s' s'' e ih hstep

theorem imp_behaviour_ars {n} {l : List (PaxosExternalEvent n)} (h : imp_behaviour n l) :
    ReachingStar.imp_behaviour (paxos_rule n) paxos_step_external l (default : PaxosState n) := by
  obtain ⟨s', hs⟩ := h
  exact Exists.intro s' (star_extend_ars hs)

/-- Da `star` di ARS a quello di `star.lean` (sono la stessa induzione). -/
theorem star_of_ars {n} {a b : SpecState n} {l : List (PaxosExternalEvent n)}
    (h : ReachingStar.star spec_step a l b) : star spec_step a l b := by
  induction h with
  | refl => exact star.refl _
  | step s2 s3 l e _ hstep ih => exact star.step _ s2 s3 l e ih hstep

theorem spec_behaviour_of_ars {n} {l : List (PaxosExternalEvent n)}
    (h : ReachingStar.spec_behaviour spec_step l (default : SpecState n)) : spec_behaviour n l := by
  obtain ⟨s', hs⟩ := h
  exact Exists.intro s' (star_of_ars hs)

/-- **Inclusione delle tracce** di Paxos nello spec, via `ReachingStar.trace_inclusion`. Le ipotesi
sulle relazioni (`relation_flush`, `relation_flush_method`, `relation_method`, `relation_init`)
sono i teoremi qui sopra. Le due ipotesi di commutazione restano **`admit`**, perché sono false
per Paxos così come sono enunciate: `has_diamond_property (trans_refl (paxos_rule n))` e
`commutes_weakly_method_rule paxos_step_external (paxos_rule n)` quantificano su *tutti* gli stati
(l'ipotesi `reachable i'` non lega `i'` alla proprietà) e comunque il crash di un nodo non commuta
mai con un passo dello stesso nodo (crash-stop: disgiunto `i = i'` nei `comm_crash_*`), né con un
`propose_rq`/`decide_rs` dello stesso nodo. Per chiuderle servirebbe una versione del framework
con la commutazione "a meno di `¬ reachable`" (come nei 36 `comm_*`) e un trattamento del crash. -/
theorem trace_inclusion (l : List (PaxosExternalEvent n)) :
    imp_behaviour n l → spec_behaviour n l := by
  intro h
  refine spec_behaviour_of_ars (ReachingStar.trace_inclusion_strong flush (paxos_rule n)
    paxos_step_external spec_step l default default
    paxos_relation_flush paxos_relation_flush_method paxos_relation_method
    ?diamond ?comm paxos_relation_init (imp_behaviour_ars h))
  case diamond =>
    -- falso per Paxos (crash-stop, e quantifica su tutti gli stati): vedi la docstring
    intro _ _
    admit
  case comm =>
    -- falso per Paxos (crash-stop, e quantifica su tutti gli stati): vedi la docstring
    intro _ _
    admit
