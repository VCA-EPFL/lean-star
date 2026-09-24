import Star.Commute.paxos

open Relation


/-!
# Paxos con rete a *bag*: i messaggi vengono cancellati alla ricezione

Variante di `paxos.lean` con una rete diversa. I ruoli e i loro stati locali (`Proposer`,
`Acceptor`, `Learner`), le scelte deterministiche (`nextBallot`, `proposeValue`) e l'interfaccia
esterna (`Event`, `PaxosExternalEvent`, `Iface`) sono importati da `paxos.lean`; i guasti
crash-stop sono gli stessi (la regola `crash` e la guardia `crashed = false` sono ridefinite qui).
Cambia solo la rete:

* un'unica lista `bag` di messaggi, ognuno con **mittente e destinatario** (`Msg`);
* chi vuole parlare con `k` processi mette `k` messaggi nella bag, uno per destinatario
  (`broadcast`: `prepare` e `propose` a tutti gli acceptor, `accepted` a tutti i learner; la
  `promise` è una risposta al solo proposer che ha mandato il `prepare`);
* un processo prende dalla bag un messaggio destinato a lui, in una posizione `j` qualsiasi (la
  rete riordina), fa il suo passo e **lo cancella** (`List.eraseIdx j`);
* un messaggio stantio viene buttato via senza fare nulla: un `prepare b` con `b` non superiore
  al ballot già promesso (`drop_prepare`), un `propose b v` con `b` inferiore al ballot promesso
  (`drop_propose`), una `promise` per un ballot che non è quello corrente del proposer o da un
  acceptor già contato (`drop_promise`), un `accepted` già contato (`drop_accepted`). Così ogni
  messaggio destinato a un nodo non fermo può sempre essere consumato (ricevuto o buttato via) dal
  destinatario; un messaggio per un nodo fermo resta nella bag per sempre.

A differenza di `paxos.lean` la rete non è un registro: di un messaggio consumato non resta
traccia, e la storia (chi ha promesso o votato cosa) sopravvive solo nello stato locale
(`maxBal`, `maxAcc`, `promises`, `accepts`). Il sistema `Paxos` di questo file ha etichette
interne ed esterne come quello di `paxos.lean`.
-/

namespace Bag

/-!
# Messaggi e stato
-/

/-- Un messaggio nella bag, con mittente `src` e destinatario `dst`. -/
inductive Msg (n : Nat) where
  | prepare (src dst : Fin n) (b : Ballot)                                 -- proposer → acceptor (1a)
  | promise (src dst : Fin n) (b : Ballot) (acc : Option (Ballot × Value)) -- acceptor → proposer (1b)
  | propose (src dst : Fin n) (b : Ballot) (v : Value)                     -- proposer → acceptor (2a)
  | accepted (src dst : Fin n) (b : Ballot) (v : Value)                    -- acceptor → learner (2b)
deriving DecidableEq, Repr

/-- Un messaggio per ogni destinatario `d : Fin n`. -/
def broadcast {n : Nat} (f : Fin n → Msg n) : List (Msg n) := (List.finRange n).map f

structure PaxosState (n : Nat) where
  proposers : Fin n → Proposer n
  acceptors : Fin n → Acceptor
  learners : Fin n → Learner n
  bag : List (Msg n)      -- i messaggi in volo
  crashed : Fin n → Bool

instance : Inhabited (PaxosState n) where
  default := ⟨fun _ => default, fun _ => default, fun _ => default, [], fun _ => false⟩

/-- Stato iniziale: ruoli nello stato di default, bag vuota, nessun nodo fermo. -/
@[simp]
def paxos_init (s : PaxosState n) : Prop :=
  (∀ k, s.proposers k = default) ∧ (∀ k, s.acceptors k = default) ∧ (∀ k, s.learners k = default)
  ∧ s.bag = [] ∧ (∀ k, s.crashed k = false)

/-- L'interfaccia esterna del partecipante `i`, la stessa di `PaxosState.iface` in `paxos.lean`. -/
def PaxosState.iface {n} (s : PaxosState n) (i : Fin n) : Iface :=
  ⟨(s.proposers i).pref, (s.learners i).rs⟩


/-!
# Eventi
-/

/-- Eventi del proposer. -/
inductive ProposerEvent (n : Nat) where
  | prepare (b : Ballot)                                                     -- fase 1a
  | collect_promise (a : Fin n) (b : Ballot) (acc : Option (Ballot × Value)) -- riceve un 1b
  | drop_promise (a : Fin n) (b : Ballot) (acc : Option (Ballot × Value))    -- butta via un 1b stantio
  | accept (b : Ballot) (v : Value)                                          -- fase 2a
deriving DecidableEq, Repr

/-- Eventi dell'acceptor: `i` è il proposer mittente del messaggio ricevuto. -/
inductive AcceptorEvent (n : Nat) where
  | promise (i : Fin n) (b : Ballot)                  -- fase 1b, risposta al proposer `i`
  | drop_prepare (i : Fin n) (b : Ballot)             -- butta via un 1a stantio
  | vote (i : Fin n) (b : Ballot) (v : Value)         -- fase 2b
  | drop_propose (i : Fin n) (b : Ballot) (v : Value) -- butta via un 2a stantio
deriving DecidableEq, Repr

/-- Eventi del learner. -/
inductive LearnerEvent (n : Nat) where
  | collect_accepted (a : Fin n) (b : Ballot) (v : Value) -- riceve un 2b
  | drop_accepted (a : Fin n) (b : Ballot) (v : Value)    -- butta via un 2b già contato
deriving DecidableEq, Repr

inductive PaxosEvent (n : Nat) where
  | proposer (e : ProposerEvent n) (i : Fin n)
  | acceptor (e : AcceptorEvent n) (a : Fin n)
  | learner (e : LearnerEvent n) (l : Fin n)
  | crash (i : Fin n)
deriving DecidableEq, Repr


/-!
# Proposer step, Acceptor step e Learner step

Ogni ruolo prende il proprio stato e la bag, restituisce i nuovi. Ricevere è `bag[j]? = some m`
con `m` destinato al ruolo, e il messaggio viene tolto con `bag.eraseIdx j`.
-/

/-- Le regole del proposer `i`. -/
inductive proposer_step (i : Fin n) :
    Proposer n → List (Msg n) → ProposerEvent n → Proposer n → List (Msg n) → Prop where
  -- fase 1a: apre il ballot successivo e manda `prepare` a tutti gli acceptor
  | prepare : ∀ (p : Proposer n) (bag : List (Msg n)) b,
      b = nextBallot i p.ballot →
      proposer_step i p bag (.prepare b)
        { p with ballot := some b, promises := fun _ => false, maxAcc := none, proposed := none }
        (bag ++ broadcast (fun a => Msg.prepare i a b))
  -- fase 1b ricevuta per il ballot corrente da un acceptor nuovo: il voto riportato non batte
  -- quello noto
  | collect_promise : ∀ (p : Proposer n) (bag : List (Msg n)) a b acc (j : Nat),
      bag[j]? = some (Msg.promise a i b acc) →
      p.ballot = some b →
      p.promises a = false →
      ¬ acc_gt acc p.maxAcc →
      proposer_step i p bag (.collect_promise a b acc)
        { p with promises := update_Fin a true p.promises }
        (bag.eraseIdx j)
  -- come sopra, ma il voto riportato batte quello noto: diventa il nuovo `maxAcc`
  | collect_promise_update : ∀ (p : Proposer n) (bag : List (Msg n)) a b acc (j : Nat),
      bag[j]? = some (Msg.promise a i b acc) →
      p.ballot = some b →
      p.promises a = false →
      acc_gt acc p.maxAcc →
      proposer_step i p bag (.collect_promise a b acc)
        { p with promises := update_Fin a true p.promises, maxAcc := acc }
        (bag.eraseIdx j)
  -- promessa stantia (ballot non corrente) o doppia (acceptor già contato): buttata via
  | drop_promise : ∀ (p : Proposer n) (bag : List (Msg n)) a b acc (j : Nat),
      bag[j]? = some (Msg.promise a i b acc) →
      (p.ballot ≠ some b ∨ p.promises a = true) →
      proposer_step i p bag (.drop_promise a b acc) p (bag.eraseIdx j)
  -- fase 2a: con una maggioranza di promesse propone il valore scelto a tutti gli acceptor, una
  -- sola volta per ballot
  | accept : ∀ (p : Proposer n) (bag : List (Msg n)) b v,
      p.ballot = some b →
      p.proposed = none →
      isQuorum n (count p.promises) →
      proposeValue p.pref p.maxAcc = some v →
      proposer_step i p bag (.accept b v)
        { p with proposed := some v }
        (bag ++ broadcast (fun a => Msg.propose i a b v))

/-- Le regole dell'acceptor `a`. -/
inductive acceptor_step (a : Fin n) :
    Acceptor → List (Msg n) → AcceptorEvent n → Acceptor → List (Msg n) → Prop where
  -- fase 1b: `prepare b` dal proposer `i` con `b` più alto di ogni ballot promesso: promette e
  -- risponde a `i` riportando l'ultimo voto
  | promise : ∀ (ac : Acceptor) (bag : List (Msg n)) (i : Fin n) b (j : Nat),
      bag[j]? = some (Msg.prepare i a b) →
      bal_gt b ac.maxBal →
      acceptor_step a ac bag (.promise i b)
        { ac with maxBal := some b }
        (bag.eraseIdx j ++ [Msg.promise a i b ac.maxAcc])
  -- `prepare b` stantio (`b` non supera il ballot promesso): buttato via
  | drop_prepare : ∀ (ac : Acceptor) (bag : List (Msg n)) (i : Fin n) b (j : Nat),
      bag[j]? = some (Msg.prepare i a b) →
      ¬ bal_gt b ac.maxBal →
      acceptor_step a ac bag (.drop_prepare i b) ac (bag.eraseIdx j)
  -- fase 2b: `propose b v` con `b` non inferiore al ballot promesso: vota e lo comunica a tutti i
  -- learner
  | vote : ∀ (ac : Acceptor) (bag : List (Msg n)) (i : Fin n) b v (j : Nat),
      bag[j]? = some (Msg.propose i a b v) →
      bal_ge b ac.maxBal →
      acceptor_step a ac bag (.vote i b v)
        { ac with maxBal := some b, maxAcc := some (b, v) }
        (bag.eraseIdx j ++ broadcast (fun l => Msg.accepted a l b v))
  -- `propose b v` stantio (`b` inferiore al ballot promesso): buttato via
  | drop_propose : ∀ (ac : Acceptor) (bag : List (Msg n)) (i : Fin n) b v (j : Nat),
      bag[j]? = some (Msg.propose i a b v) →
      ¬ bal_ge b ac.maxBal →
      acceptor_step a ac bag (.drop_propose i b v) ac (bag.eraseIdx j)

/-- Le regole del learner `l`. -/
inductive learner_step (l : Fin n) :
    Learner n → List (Msg n) → LearnerEvent n → Learner n → List (Msg n) → Prop where
  -- riceve il voto di `a` per `(b, v)`, se non l'aveva già contato
  | collect_accepted : ∀ (le : Learner n) (bag : List (Msg n)) a b v (j : Nat),
      bag[j]? = some (Msg.accepted a l b v) →
      le.accepts (b, v) a = false →
      learner_step l le bag (.collect_accepted a b v)
        { le with accepts := update_Key (b, v) (update_Fin a true (le.accepts (b, v))) le.accepts }
        (bag.eraseIdx j)
  -- voto già contato: buttato via
  | drop_accepted : ∀ (le : Learner n) (bag : List (Msg n)) a b v (j : Nat),
      bag[j]? = some (Msg.accepted a l b v) →
      le.accepts (b, v) a = true →
      learner_step l le bag (.drop_accepted a b v) le (bag.eraseIdx j)


/-!
# Paxos step
-/

/-- Il passo di sistema: un ruolo di un nodo non fermo fa un passo, oppure un nodo si ferma. -/
inductive paxos_step : PaxosState n → PaxosEvent n → PaxosState n → Prop where
  | proposer : ∀ (s : PaxosState n) p' bag' e i,
      s.crashed i = false →
      proposer_step i (s.proposers i) s.bag e p' bag' →
      paxos_step s (.proposer e i)
        { s with proposers := update_Fin i p' s.proposers, bag := bag' }
  | acceptor : ∀ (s : PaxosState n) ac' bag' e a,
      s.crashed a = false →
      acceptor_step a (s.acceptors a) s.bag e ac' bag' →
      paxos_step s (.acceptor e a)
        { s with acceptors := update_Fin a ac' s.acceptors, bag := bag' }
  | learner : ∀ (s : PaxosState n) l' bag' e l,
      s.crashed l = false →
      learner_step l (s.learners l) s.bag e l' bag' →
      paxos_step s (.learner e l)
        { s with learners := update_Fin l l' s.learners, bag := bag' }
  -- crash-stop: il nodo `i` si ferma per sempre
  | crash : ∀ (s : PaxosState n) i,
      s.crashed i = false →
      paxos_step s (.crash i)
        { s with crashed := update_Fin i true s.crashed }

/-- Il passo esterno, identico a quello di `paxos.lean`: l'esterno scrive il valore che il
partecipante `i` (non fermo) vuole proporre (una volta sola), oppure il learner di `i` (non fermo)
decide `v`, quando una maggioranza di acceptor lo ha votato in uno stesso ballot, e lo consegna
all'esterno (`decide_rs v`), registrandolo in `rs`. -/
inductive paxos_step_external : PaxosState n → PaxosExternalEvent n → PaxosState n → Prop where
  | propose_rq : ∀ (s : PaxosState n) i v,
      s.crashed i = false →
      (s.proposers i).pref = none →
      paxos_step_external s (.part (.propose_rq v) i)
        { s with proposers := update_Fin i { s.proposers i with pref := some v } s.proposers }
  | decide_rs : ∀ (s : PaxosState n) i b v,
      s.crashed i = false →
      (s.learners i).decision = none →
      isQuorum n (count ((s.learners i).accepts (b, v))) →
      paxos_step_external s (.part (.decide_rs v) i)
        { s with learners := update_Fin i { s.learners i with decision := some v,
                                                              rs := (s.learners i).rs ++ [v] } s.learners }

/-- Etichette del sistema completo: passi interni e passi esterni. -/
inductive PaxosLabel (n : Nat) where
  | int (e : PaxosEvent n)
  | ext (e : PaxosExternalEvent n)
deriving DecidableEq, Repr

inductive paxos_step_all : PaxosState n → PaxosLabel n → PaxosState n → Prop where
  | int : ∀ s e s', paxos_step s e s' → paxos_step_all s (.int e) s'
  | ext : ∀ s e s', paxos_step_external s e s' → paxos_step_all s (.ext e) s'

/-- Il sistema completo (passi interni ed esterni), come `Paxos` in `paxos.lean`. -/
def Paxos {n : Nat} : Paxos.LTS (PaxosLabel n) where
  S := PaxosState n
  transitions := paxos_step_all
  init s := paxos_init s

/-- `default` è uno stato iniziale. -/
theorem paxos_init_default {n} : paxos_init (default : PaxosState n) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩

/-- Ogni stato iniziale è `default`. -/
theorem eq_default_of_init {n} {s : PaxosState n} (h : paxos_init s) : s = default := by
  obtain ⟨hp, ha, hl, hb, hc⟩ := h
  obtain ⟨p, a, l, bag, c⟩ := s
  simp only at hp ha hl hb hc
  subst hb
  have e1 : p = fun _ => default := funext hp
  have e2 : a = fun _ => default := funext ha
  have e3 : l = fun _ => default := funext hl
  have e4 : c = fun _ => false := funext hc
  subst e1 e2 e3 e4
  rfl

/-- I passi interni non toccano `pref`, `decision` e `rs` di nessun partecipante (come
`paxos_step_iface` in `paxos_spec.lean`, dove serve per la relazione di flush). -/
theorem paxos_step_iface {n} {s s' : PaxosState n} {t : PaxosEvent n} (h : paxos_step s t s')
    (k : Fin n) :
    (s'.proposers k).pref = (s.proposers k).pref
      ∧ (s'.learners k).decision = (s.learners k).decision
      ∧ (s'.learners k).rs = (s.learners k).rs := by
  cases h with
  | proposer p' bag' e i hc hp =>
    refine ⟨?_, rfl, rfl⟩
    by_cases hk : k = i
    · rw [hk]; simp only [update_Fin_gss]; cases hp <;> rfl
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | acceptor ac' bag' e a hc ha => exact ⟨rfl, rfl, rfl⟩
  | learner l' bag' e l hc hl =>
    refine ⟨rfl, ?_, ?_⟩
    · by_cases hk : k = l
      · rw [hk]; simp only [update_Fin_gss]; cases hl <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
    · by_cases hk : k = l
      · rw [hk]; simp only [update_Fin_gss]; cases hl <;> rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk]
  | crash i hc => exact ⟨rfl, rfl, rfl⟩


/-! # Due esecuzioni

Con un solo partecipante: l'esterno chiede di proporre `7`; ogni messaggio viene messo nella bag,
consumato dal destinatario e cancellato; alla fine il partecipante decide `7` e la bag è vuota.
Con due partecipanti: l'acceptor 0 riceve `prepare 1` prima di `prepare 0`, promette il ballot 1
e poi butta via `prepare 0`, che sparisce dalla bag. -/

theorem decision_reachable_one :
    ∃ s : PaxosState 1, ReflTransGen Paxos.atrans (default : PaxosState 1) s
      ∧ (s.learners 0).decision = some 7 ∧ (s.learners 0).rs = [7] ∧ s.bag = [] := by
  -- l'esterno chiede al partecipante `0` di proporre `7`
  have c0 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail ReflTransGen.refl (Exists.intro (.ext (.part (.propose_rq 7) 0))
      (paxos_step_all.ext _ _ _ (paxos_step_external.propose_rq _ 0 7 rfl rfl)))
  -- fase 1a: `prepare 0` nella bag
  have c1 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c0 (Exists.intro (.int (.proposer (.prepare 0) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl (proposer_step.prepare _ _ 0 rfl))))
  -- fase 1b: l'acceptor consuma `prepare 0` e mette `promise 0` nella bag
  have c2 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c1 (Exists.intro (.int (.acceptor (.promise 0 0) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.promise _ _ 0 0 0 rfl trivial))))
  -- il proposer consuma la promessa: bag vuota
  have c3 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c2 (Exists.intro (.int (.proposer (.collect_promise 0 0 none) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl
        (proposer_step.collect_promise _ _ 0 0 none 0 rfl rfl rfl (fun h => h)))))
  -- fase 2a: `propose 0 7` nella bag
  have c4 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c3 (Exists.intro (.int (.proposer (.accept 0 7) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl
        (proposer_step.accept _ _ 0 7 rfl rfl (by unfold isQuorum count; decide) rfl))))
  -- fase 2b: l'acceptor consuma la proposta e mette `accepted 0 7` nella bag
  have c5 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c4 (Exists.intro (.int (.acceptor (.vote 0 0 7) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.vote _ _ 0 0 7 0 rfl (Nat.le_refl 0)))))
  -- il learner consuma il voto: bag vuota
  have c6 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c5 (Exists.intro (.int (.learner (.collect_accepted 0 0 7) 0))
      (paxos_step_all.int _ _ _ (paxos_step.learner _ _ _ _ 0 rfl
        (learner_step.collect_accepted _ _ 0 0 7 0 rfl (by decide)))))
  -- decisione, consegnata all'esterno
  have c7 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c6 (Exists.intro (.ext (.part (.decide_rs 7) 0))
      (paxos_step_all.ext _ _ _
        (paxos_step_external.decide_rs _ 0 0 7 rfl rfl (by unfold isQuorum count; decide))))
  exact ⟨_, c7, rfl, rfl, rfl⟩

/-- Con due nodi: `prepare 0` e `prepare 1` sono nella bag (due copie ciascuno, una per acceptor);
l'acceptor 0 promette il ballot 1 e poi butta via `prepare 0`, che non è più nella bag. -/
theorem drop_prepare_reachable :
    ∃ s : PaxosState 2, ReflTransGen Paxos.atrans (default : PaxosState 2) s
      ∧ (s.acceptors 0).maxBal = some 1
      ∧ s.bag = [Msg.prepare 0 1 0, Msg.prepare 1 1 1, Msg.promise 0 1 1 none] := by
  -- il proposer 0 manda `prepare 0` ai due acceptor
  have c1 : ReflTransGen Paxos.atrans (default : PaxosState 2) _ :=
    ReflTransGen.tail ReflTransGen.refl (Exists.intro (.int (.proposer (.prepare 0) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl (proposer_step.prepare _ _ 0 rfl))))
  -- il proposer 1 manda `prepare 1` ai due acceptor
  have c2 : ReflTransGen Paxos.atrans (default : PaxosState 2) _ :=
    ReflTransGen.tail c1 (Exists.intro (.int (.proposer (.prepare 1) 1))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 1 rfl (proposer_step.prepare _ _ 1 rfl))))
  -- l'acceptor 0 consuma `prepare 1` (posizione 2) e promette il ballot 1
  have c3 : ReflTransGen Paxos.atrans (default : PaxosState 2) _ :=
    ReflTransGen.tail c2 (Exists.intro (.int (.acceptor (.promise 1 1) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.promise _ _ 1 1 2 rfl trivial))))
  -- l'acceptor 0 trova `prepare 0` (posizione 0), ormai stantio, e lo butta via
  have c4 : ReflTransGen Paxos.atrans (default : PaxosState 2) _ :=
    ReflTransGen.tail c3 (Exists.intro (.int (.acceptor (.drop_prepare 0 0) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.drop_prepare _ _ 0 0 0 rfl (Nat.not_lt_zero 1)))))
  exact ⟨_, c4, rfl, rfl⟩

end Bag
