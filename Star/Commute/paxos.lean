import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation


/-!
# Paxos (decisione singola) con guasti crash-stop

Modello di Paxos a decisione singola nello stile di `MSI.lean`, ispirato anche a
`Distributed/paxos.lean` di Lorenzo Padrini (VCA-EPFL, repo `distributed-verification`):
`n` nodi indicizzati da `Fin n`, ognuno con un *proposer* (fasi 1a e 2a), un *acceptor*
(fasi 1b e 2b) e un *learner* (raccoglie i voti e decide). I ruoli hanno ognuno la propria
relazione di passo (`proposer_step`, `acceptor_step`, `learner_step`), composte nel passo di
sistema `paxos_step` come le regole di cache e parent in `MSI.lean`.

La rete è fatta di *outbox*: `pmsgs i` sono i messaggi mandati dal proposer `i`, `amsgs a` quelli
mandati dall'acceptor `a`. I messaggi non vengono mai cancellati: la ricezione legge il messaggio
in una posizione `j` qualsiasi (`msgs[j]? = some …`). Così sono già coperti il riordino, la
duplicazione (un messaggio si può rileggere) e la perdita (un messaggio può non essere mai letto),
senza regole di rete. Le outbox per mittente (e non un'unica lista) servono ai diagrammi di
commutazione: due invii da mittenti diversi commutano esattamente (`update_Fin_append_comm2`).

Le scelte del protocollo sono deterministiche, come in `MSI.lean` dove il solo nondeterminismo è
lo scheduling: il proposer `i` apre i ballot `i, i + n, i + 2n, …` (`nextBallot`), e in fase 2a
propone il valore del voto con ballot più alto riportato nelle promesse, altrimenti quello che
l'esterno gli ha chiesto di proporre (`pref`, `proposeValue`). Gli insiemi di acceptor (`promises`,
`accepts`) sono funzioni `Fin n → Bool` aggiornate con `update_Fin`, così due ricezioni commutano.

L'interfaccia esterna (`Event`, `PaxosExternalEvent`, `paxos_step_external`) è per partecipante,
come `cache_msi_step` in MSI: `propose_rq v` scrive in `pref` il valore che il partecipante vuole
proporre (una volta sola); `decide_rs v` è la decisione del learner (una maggioranza di acceptor
ha votato `v` in uno stesso ballot), consegnata all'esterno e registrata in `rs` (mai consumata,
come `extqueue.rs` in MSI), come le risposte `ld_rs`/`st_rs` di MSI. Lo spec centralizzato di `paxos_spec.lean` ha solo passi esterni,
gli stessi, e la stessa interfaccia (`Iface`). Il sistema `Paxos` ha etichette interne ed esterne
(`PaxosLabel`, `paxos_step_all`).

Guasti **crash-stop**: un nodo può fermarsi in ogni momento (`crash`); da quel momento nessuno
dei suoi ruoli fa più un passo (guardia `crashed i = false` nel passo di sistema) e non riparte
mai (`crashed_step`, `crashed_frozen`). Con `n = 2f + 1` nodi il quorum è `f + 1`
(`isQuorum_faults`): il protocollo tollera `f` crash.
-/

abbrev Ballot := Nat
abbrev Value := Nat


/-!
# Define Events
-/

/-- Messaggi proposer → acceptor (nell'outbox `pmsgs i` del proposer `i`). -/
inductive PMessage where
  | prepare (b : Ballot)              -- fase 1a
  | propose (b : Ballot) (v : Value)  -- fase 2a
deriving DecidableEq, Repr

/-- Messaggi acceptor → proposer/learner (nell'outbox `amsgs a` dell'acceptor `a`). -/
inductive AMessage where
  | promise (b : Ballot) (acc : Option (Ballot × Value)) -- fase 1b, con l'ultimo voto di `a`
  | accepted (b : Ballot) (v : Value)                     -- fase 2b, voto di `a`
deriving DecidableEq, Repr

/-- Eventi del proposer. -/
inductive ProposerEvent (n : Nat) where
  | prepare (b : Ballot)                                                     -- fase 1a
  | collect_promise (a : Fin n) (b : Ballot) (acc : Option (Ballot × Value)) -- riceve un 1b
  | accept (b : Ballot) (v : Value)                                          -- fase 2a
deriving DecidableEq, Repr

/-- Eventi dell'acceptor. -/
inductive AcceptorEvent where
  | promise (b : Ballot)              -- fase 1b
  | vote (b : Ballot) (v : Value)     -- fase 2b
deriving DecidableEq, Repr

/-- Eventi del learner (la decisione è il passo esterno `decide_rs`). -/
inductive LearnerEvent (n : Nat) where
  | collect_accepted (a : Fin n) (b : Ballot) (v : Value) -- riceve un 2b
deriving DecidableEq, Repr

inductive PaxosEvent (n : Nat) where
  | proposer (e : ProposerEvent n) (i : Fin n)
  | acceptor (e : AcceptorEvent) (a : Fin n)
  | learner (e : LearnerEvent n) (l : Fin n)
  | crash (i : Fin n)
deriving DecidableEq, Repr

/-- Eventi esterni di un partecipante: scrive il valore che vuole proporre, o decide. -/
inductive Event where
  | propose_rq (v : Value) -- l'esterno chiede al partecipante di proporre `v`
  | decide_rs (v : Value)  -- il partecipante decide `v` e lo consegna all'esterno
deriving DecidableEq, Repr

/-- Evento esterno etichettato con il partecipante. -/
inductive PaxosExternalEvent (n : Nat) where
  | part (e : Event) (i : Fin n)
deriving DecidableEq, Repr


/-!
# Proposer, Acceptor, Learner, Network and PaxosState
-/

structure Proposer (n : Nat) where
  ballot : Option Ballot            -- ballot corrente (`none`: nessun ballot aperto)
  promises : Fin n → Bool           -- acceptor che hanno promesso per `ballot`
  maxAcc : Option (Ballot × Value)  -- il voto con ballot più alto riportato nelle promesse
  proposed : Option Value           -- valore mandato in fase 2a per `ballot`
  pref : Option Value               -- valore che l'esterno ha chiesto di proporre

structure Acceptor where
  maxBal : Option Ballot            -- ballot più alto promesso
  maxAcc : Option (Ballot × Value)  -- ultimo voto (ballot, valore)

structure Learner (n : Nat) where
  accepts : Ballot × Value → Fin n → Bool -- per ogni proposta, gli acceptor che l'hanno votata
  decision : Option Value
  rs : List Value                          -- decisioni consegnate all'esterno (registro delle `decide_rs`)

structure Network (n : Nat) where
  pmsgs : Fin n → List PMessage -- outbox del proposer `i`
  amsgs : Fin n → List AMessage -- outbox dell'acceptor `a`

instance : Inhabited (Proposer n) where
  default := ⟨none, fun _ => false, none, none, none⟩

instance : Inhabited Acceptor where
  default := ⟨none, none⟩

instance : Inhabited (Learner n) where
  default := ⟨fun _ _ => false, none, []⟩

instance : Inhabited (Network n) where
  default := ⟨fun _ => [], fun _ => []⟩

structure PaxosState (n : Nat) where
  proposers : Fin n → Proposer n
  acceptors : Fin n → Acceptor
  learners : Fin n → Learner n
  network : Network n
  crashed : Fin n → Bool

instance : Inhabited (PaxosState n) where
  default := ⟨fun _ => default, fun _ => default, fun _ => default, default, fun _ => false⟩

/-- Stato iniziale: nessun ballot aperto, nessuna promessa né voto, nessuna decisione, nessun
nodo fermo, outbox vuote. Come in `msi_init` i campi sono tutti fissati: l'unico stato iniziale
è `default`. -/
@[simp]
def paxos_init (s : PaxosState n) : Prop :=
  (∀ k, (s.proposers k).ballot = none ∧ (s.proposers k).promises = (fun _ => false)
        ∧ (s.proposers k).maxAcc = none ∧ (s.proposers k).proposed = none
        ∧ (s.proposers k).pref = none)
  ∧ (∀ k, (s.acceptors k).maxBal = none ∧ (s.acceptors k).maxAcc = none)
  ∧ (∀ k, (s.learners k).accepts = (fun _ _ => false) ∧ (s.learners k).decision = none
        ∧ (s.learners k).rs = [])
  ∧ (∀ k, s.crashed k = false)
  ∧ (∀ k, s.network.pmsgs k = [] ∧ s.network.amsgs k = [])


/-!
# update_Fin and update_Key
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

/-- Aggiornare due indici distinti con due `append` diverse commuta. -/
theorem update_Fin_append_comm2 {α : Type} {n} (f : Fin n → List α) (a b : Fin n) (x y : List α)
    (hab : ¬ a = b) :
    update_Fin a (update_Fin b (f b ++ y) f a ++ x) (update_Fin b (f b ++ y) f)
      = update_Fin b (update_Fin a (f a ++ x) f b ++ y) (update_Fin a (f a ++ x) f) := by
  funext k
  by_cases hka : k = a
  · subst hka; simp [update_Fin, Ne.symm hab]
  · by_cases hkb : k = b
    · subst hkb; simp [update_Fin, hab]
    · simp [update_Fin, Ne.symm hka, Ne.symm hkb]

/-- Aggiornare due indici distinti commuta. -/
theorem update_Fin_comm {α : Type} {n} (f : Fin n → α) (a b : Fin n) (x y : α) (hab : ¬ a = b) :
    update_Fin a x (update_Fin b y f) = update_Fin b y (update_Fin a x f) := by
  funext k
  by_cases hka : k = a
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

/-- `update_Fin` per una chiave qualsiasi con uguaglianza decidibile (le proposte `(b, v)`). -/
def update_Key {α β : Type} [DecidableEq α] (k : α) (e : β) (f : α → β) : α → β :=
  fun x => if k = x then e else f x

@[simp]
theorem update_Key_gss {α β : Type} [DecidableEq α] (k : α) (e : β) (f : α → β) :
    update_Key k e f k = e := by
  unfold update_Key; simp

@[simp]
theorem update_Key_gso {α β : Type} [DecidableEq α] (x k : α) (e : β) (f : α → β) :
    ¬(k = x) → update_Key k e f x = f x := by
  intro h; unfold update_Key; simp [h]

@[simp]
theorem update_Key_gso2 {α β : Type} [DecidableEq α] (x k : α) (e : β) (f : α → β) :
    ¬(x = k) → update_Key k e f x = f x := by
  intro h; unfold update_Key; simp [Ne.symm h]

/-- Aggiornare due chiavi distinte commuta. -/
theorem update_Key_comm {α β : Type} [DecidableEq α] (f : α → β) (k k' : α) (x y : β)
    (h : ¬ k = k') : update_Key k x (update_Key k' y f) = update_Key k' y (update_Key k x f) := by
  funext z
  by_cases hz : z = k
  · subst hz; simp [update_Key, Ne.symm h]
  · by_cases hz' : z = k'
    · subst hz'; simp [update_Key, h]
    · simp [update_Key, Ne.symm hz, Ne.symm hz']

/-- Aggiornare due volte la stessa chiave: vince l'ultimo. -/
theorem update_Key_update_Key_same {α β : Type} [DecidableEq α] (k : α) (e e' : β) (f : α → β) :
    update_Key k e (update_Key k e' f) = update_Key k e f := by
  funext z
  by_cases hz : z = k
  · subst hz; simp [update_Key_gss]
  · simp [update_Key_gso2 _ _ _ _ hz]


/-!
# Ballot, voti e quorum
-/

/-- `b` è più alto di ogni ballot in `ob` (`none` = nessun ballot visto). -/
def bal_gt (b : Ballot) : Option Ballot → Prop
  | none => True
  | some b₀ => b₀ < b

/-- `b` è almeno il ballot in `ob` (`none` = nessun ballot visto). -/
def bal_ge (b : Ballot) : Option Ballot → Prop
  | none => True
  | some b₀ => b₀ ≤ b

/-- Il voto `acc` riportato in una promessa batte il voto `cur` già noto al proposer:
"nessun voto" non batte nulla, un voto batte "nessun voto" e ogni voto con ballot minore. -/
def acc_gt : Option (Ballot × Value) → Option (Ballot × Value) → Prop
  | none, _ => False
  | some _, none => True
  | some (b, _), some (b₀, _) => b₀ < b

/-- Il ballot successivo del proposer `i`: il primo è `i`, poi si sale di `n`; così i ballot di
`i` sono esattamente quelli con `b % n = i`. -/
def nextBallot {n} (i : Fin n) : Option Ballot → Ballot
  | none => i.val
  | some b₀ => b₀ + n

/-- Il valore proponibile in fase 2a: quello del voto con ballot più alto riportato nelle promesse,
altrimenti (nessun acceptor aveva votato) quello chiesto dall'esterno (`none`: niente da proporre). -/
def proposeValue (pref : Option Value) : Option (Ballot × Value) → Option Value
  | none => pref
  | some (_, w) => some w

theorem proposeValue_some {pref : Option Value} {m : Option (Ballot × Value)} {v : Value}
    (h : proposeValue pref m = some v) : ∀ x, m = some x → v = x.2 := by
  intro x hx
  subst hx
  obtain ⟨b, w⟩ := x
  simp only [proposeValue, Option.some.injEq] at h
  exact h.symm

/-- Quanti indici soddisfano `S`. -/
def count {n} (S : Fin n → Bool) : Nat := (List.finRange n).countP S

/-- Maggioranza: `k` è più della metà degli `n` nodi. -/
def isQuorum (n k : Nat) : Prop := n < 2 * k

/-- Con `n = 2f + 1` nodi il quorum è `f + 1`: si tollerano `f` crash. -/
theorem isQuorum_faults (f k : Nat) : isQuorum (2 * f + 1) k ↔ f + 1 ≤ k := by
  unfold isQuorum; omega

/-- `count` è monotono. -/
theorem count_mono {n} {S T : Fin n → Bool} (h : ∀ a, S a = true → T a = true) :
    count S ≤ count T := by
  unfold count
  apply List.countP_mono_left
  intro a _ ha
  exact h a ha

/-- Aggiungere un indice non fa calare il conteggio. -/
theorem count_le_update {n} (S : Fin n → Bool) (a : Fin n) :
    count S ≤ count (update_Fin a true S) := by
  apply count_mono
  intro k hk
  by_cases hka : k = a
  · subst hka; simp [update_Fin_gss]
  · simp [update_Fin_gso2 _ _ _ _ hka, hk]

/-- Due maggioranze si intersecano: il fatto su cui poggia tutta la sicurezza di Paxos. -/
theorem quorum_intersect {n} (P Q : Fin n → Bool)
    (hP : isQuorum n (count P)) (hQ : isQuorum n (count Q)) :
    ∃ a, P a = true ∧ Q a = true := by
  by_contra hno
  have h1 : (List.finRange n).countP Q ≤ (List.finRange n).countP (fun a => ¬ P a) := by
    apply List.countP_mono_left
    intro a _ hQa
    cases hPa : P a
    · simp
    · exact absurd ⟨a, hPa, hQa⟩ hno
  have h2 : (List.finRange n).length
      = (List.finRange n).countP P + (List.finRange n).countP (fun a => ¬ P a) :=
    List.length_eq_countP_add_countP P
  rw [List.length_finRange] at h2
  unfold isQuorum count at hP hQ
  omega


/-!
# Proposer step, Acceptor step and Learner step
-/

/-- Le regole del proposer `i`: prende il proprio stato e la rete, restituisce i nuovi. -/
inductive proposer_step (i : Fin n) :
    Proposer n → Network n → ProposerEvent n → Proposer n → Network n → Prop where
  -- fase 1a: apre il ballot successivo e manda `prepare`
  | prepare : ∀ (p : Proposer n) (net : Network n) b,
      b = nextBallot i p.ballot →
      proposer_step i p net (.prepare b)
        { p with ballot := some b, promises := fun _ => false, maxAcc := none, proposed := none }
        { net with pmsgs := update_Fin i (net.pmsgs i ++ [PMessage.prepare b]) net.pmsgs }
  -- fase 1b ricevuta per il ballot corrente da un acceptor nuovo: il voto riportato non batte
  -- quello noto
  | collect_promise : ∀ (p : Proposer n) (net : Network n) a b acc (j : Nat),
      (net.amsgs a)[j]? = some (AMessage.promise b acc) →
      p.ballot = some b →
      p.promises a = false →
      ¬ acc_gt acc p.maxAcc →
      proposer_step i p net (.collect_promise a b acc)
        { p with promises := update_Fin a true p.promises }
        net
  -- come sopra, ma il voto riportato batte quello noto: diventa il nuovo `maxAcc`
  | collect_promise_update : ∀ (p : Proposer n) (net : Network n) a b acc (j : Nat),
      (net.amsgs a)[j]? = some (AMessage.promise b acc) →
      p.ballot = some b →
      p.promises a = false →
      acc_gt acc p.maxAcc →
      proposer_step i p net (.collect_promise a b acc)
        { p with promises := update_Fin a true p.promises, maxAcc := acc }
        net
  -- fase 2a: con una maggioranza di promesse propone il valore scelto, una sola volta per ballot
  | accept : ∀ (p : Proposer n) (net : Network n) b v,
      p.ballot = some b →
      p.proposed = none →
      isQuorum n (count p.promises) →
      proposeValue p.pref p.maxAcc = some v →
      proposer_step i p net (.accept b v)
        { p with proposed := some v }
        { net with pmsgs := update_Fin i (net.pmsgs i ++ [PMessage.propose b v]) net.pmsgs }

/-- Le regole dell'acceptor `a`. -/
inductive acceptor_step (a : Fin n) :
    Acceptor → Network n → AcceptorEvent → Acceptor → Network n → Prop where
  -- fase 1b: `prepare b` (da un proposer `i` qualsiasi) con `b` più alto di ogni ballot promesso:
  -- promette e riporta l'ultimo voto
  | promise : ∀ (ac : Acceptor) (net : Network n) (i : Fin n) b (j : Nat),
      (net.pmsgs i)[j]? = some (PMessage.prepare b) →
      bal_gt b ac.maxBal →
      acceptor_step a ac net (.promise b)
        { ac with maxBal := some b }
        { net with amsgs := update_Fin a (net.amsgs a ++ [AMessage.promise b ac.maxAcc]) net.amsgs }
  -- fase 2b: `propose b v` con `b` non inferiore al ballot promesso: vota e lo comunica
  | vote : ∀ (ac : Acceptor) (net : Network n) (i : Fin n) b v (j : Nat),
      (net.pmsgs i)[j]? = some (PMessage.propose b v) →
      bal_ge b ac.maxBal →
      acceptor_step a ac net (.vote b v)
        { ac with maxBal := some b, maxAcc := some (b, v) }
        { net with amsgs := update_Fin a (net.amsgs a ++ [AMessage.accepted b v]) net.amsgs }

/-- Le regole del learner: la decisione è il passo esterno `decide_rs` di `paxos_step_external`. -/
inductive learner_step :
    Learner n → Network n → LearnerEvent n → Learner n → Network n → Prop where
  -- riceve il voto di `a` per `(b, v)`, se non l'aveva già contato
  | collect_accepted : ∀ (l : Learner n) (net : Network n) a b v (j : Nat),
      (net.amsgs a)[j]? = some (AMessage.accepted b v) →
      l.accepts (b, v) a = false →
      learner_step l net (.collect_accepted a b v)
        { l with accepts := update_Key (b, v) (update_Fin a true (l.accepts (b, v))) l.accepts }
        net


/-!
# Paxos step
-/

/-- Il passo di sistema: un ruolo di un nodo non fermo fa un passo, oppure un nodo si ferma. -/
inductive paxos_step : PaxosState n → PaxosEvent n → PaxosState n → Prop where
  | proposer : ∀ (s : PaxosState n) p' net' e i,
      s.crashed i = false →
      proposer_step i (s.proposers i) s.network e p' net' →
      paxos_step s (.proposer e i)
        { s with proposers := update_Fin i p' s.proposers,
                 network := net' }
  | acceptor : ∀ (s : PaxosState n) ac' net' e a,
      s.crashed a = false →
      acceptor_step a (s.acceptors a) s.network e ac' net' →
      paxos_step s (.acceptor e a)
        { s with acceptors := update_Fin a ac' s.acceptors,
                 network := net' }
  | learner : ∀ (s : PaxosState n) l' net' e l,
      s.crashed l = false →
      learner_step (s.learners l) s.network e l' net' →
      paxos_step s (.learner e l)
        { s with learners := update_Fin l l' s.learners,
                 network := net' }
  -- crash-stop: il nodo `i` si ferma per sempre
  | crash : ∀ (s : PaxosState n) i,
      s.crashed i = false →
      paxos_step s (.crash i)
        { s with crashed := update_Fin i true s.crashed }


/-- Il passo esterno, come `cache_msi_step` in MSI: l'esterno scrive il valore che il partecipante
`i` (non fermo) vuole proporre (una volta sola), oppure il learner di `i` (non fermo) decide `v`,
quando una maggioranza di acceptor lo ha votato in uno stesso ballot, e lo consegna all'esterno
(`decide_rs v`), registrandolo in `rs` (mai consumata, come `extqueue.rs` in MSI). -/
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

/-- L'interfaccia esterna di un partecipante, la stessa per implementazione e spec: il valore che
ha chiesto di proporre e le decisioni consegnate all'esterno (il crash è un guasto interno). -/
structure Iface where
  pref : Option Value
  rs : List Value
deriving DecidableEq, Repr

def PaxosState.iface {n} (s : PaxosState n) (i : Fin n) : Iface :=
  ⟨(s.proposers i).pref, (s.learners i).rs⟩

/-- Etichette del sistema completo: passi interni e passi esterni. -/
inductive PaxosLabel (n : Nat) where
  | int (e : PaxosEvent n)
  | ext (e : PaxosExternalEvent n)
deriving DecidableEq, Repr

inductive paxos_step_all : PaxosState n → PaxosLabel n → PaxosState n → Prop where
  | int : ∀ s e s', paxos_step s e s' → paxos_step_all s (.int e) s'
  | ext : ∀ s e s', paxos_step_external s e s' → paxos_step_all s (.ext e) s'

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem paxos_step_external_congr {n} {s s' s'' : PaxosState n} {t : PaxosExternalEvent n}
    (h : paxos_step_external s t s') (heq : s' = s'') : paxos_step_external s t s'' := heq ▸ h

/-- Trasporto lungo l'uguaglianza dello stato di arrivo. -/
theorem paxos_step_congr {n} {s s' s'' : PaxosState n} {t : PaxosEvent n}
    (h : paxos_step s t s') (heq : s' = s'') : paxos_step s t s'' := heq ▸ h

/-- Estensionalità campo per campo (puntuale sulle funzioni) di `PaxosState`. -/
theorem PaxosState.ext_all {n} {a b : PaxosState n}
    (hp : ∀ k, a.proposers k = b.proposers k)
    (ha : ∀ k, a.acceptors k = b.acceptors k)
    (hl : ∀ k, a.learners k = b.learners k)
    (hpm : ∀ k, a.network.pmsgs k = b.network.pmsgs k)
    (ham : ∀ k, a.network.amsgs k = b.network.amsgs k)
    (hc : ∀ k, a.crashed k = b.crashed k) : a = b := by
  obtain ⟨pa, aa, la, ⟨pma, ama⟩, ca⟩ := a
  obtain ⟨pb, ab, lb, ⟨pmb, amb⟩, cb⟩ := b
  have e1 : pa = pb := funext hp
  have e2 : aa = ab := funext ha
  have e3 : la = lb := funext hl
  have e4 : pma = pmb := funext hpm
  have e5 : ama = amb := funext ham
  have e6 : ca = cb := funext hc
  subst e1 e2 e3 e4 e5 e6
  rfl


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

/-- Un messaggio presente resta presente dopo un `append`: la rete non cancella mai. -/
theorem lst_get_append {α} (l l' : List α) (j : Nat) (a : α) :
    l[j]? = some a → (l ++ l')[j]? = some a := by
  intro h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h


-- define al LTS

structure Paxos.LTS (T : Type) where
  S : Type
  transitions : S → T → S → Prop
  init : S → Prop

def Paxos.LTS.atrans {T} (l : Paxos.LTS T) : l.S → l.S → Prop := fun s s' =>
  ∃ t, l.transitions s t s'

def Paxos.LTS.reachable {T} (l : Paxos.LTS T) : l.S → Prop := fun s =>
  ∀ s_init, l.init s_init → ReflTransGen l.atrans s_init s

def Paxos.LTS.backwards_reachable_from {T} (l : Paxos.LTS T) (s s' : l.S) :=
  ReflTransGen (Function.swap l.atrans) s s'

theorem Paxos.backwards_reachable_not_init {T} {l : Paxos.LTS T} {s} :
  (∀ s_init, l.init s_init → l.backwards_reachable_from s s_init) ↔ l.reachable s := by
  grind [Paxos.LTS.reachable, Paxos.LTS.backwards_reachable_from, Relation.reflTransGen_swap]


/-- Il sistema completo: passi interni ed esterni (a differenza di `MSI`, dove `reachable` usa solo
i passi interni: qui senza richieste esterne nessun valore verrebbe mai proposto). -/
def Paxos {n : Nat} : Paxos.LTS (PaxosLabel n) where
  S := PaxosState n
  transitions := paxos_step_all
  init s := paxos_init s


/-- `default` è uno stato iniziale. -/
theorem paxos_init_default {n} : paxos_init (default : PaxosState n) :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl,
   fun _ => ⟨rfl, rfl⟩⟩

/-- Ogni stato iniziale è `default`. -/
theorem eq_default_of_init {n} {s : PaxosState n} (h : paxos_init s) : s = default := by
  obtain ⟨hp, ha, hl, hc, hn⟩ := h
  apply PaxosState.ext_all
  · intro k
    have h := hp k
    generalize s.proposers k = p at h ⊢
    obtain ⟨b, pr, m, po, pf⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    try dsimp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl
  · intro k
    have h := ha k
    generalize s.acceptors k = p at h ⊢
    obtain ⟨b, m⟩ := p
    obtain ⟨h1, h2⟩ := h
    try dsimp only at h1 h2
    subst h1 h2
    rfl
  · intro k
    have h := hl k
    generalize s.learners k = p at h ⊢
    obtain ⟨ac, d, rs⟩ := p
    obtain ⟨h1, h2, h3⟩ := h
    try dsimp only at h1 h2 h3
    subst h1 h2 h3
    rfl
  · intro k; exact (hn k).1
  · intro k; exact (hn k).2
  · intro k; exact hc k


/-! ## Crash-stop

Un nodo fermo resta fermo e il suo stato non cambia più: nessuna regola rimette `crashed` a
`false` e ogni passo di un ruolo chiede `crashed = false`. -/

theorem crashed_step {n} {s s' : PaxosState n} {t : PaxosEvent n} {i : Fin n}
    (hc : s.crashed i = true) (h : paxos_step s t s') : s'.crashed i = true := by
  cases h with
  | proposer p' net' e i' hc' hp => exact hc
  | acceptor ac' net' e a hc' ha => exact hc
  | learner l' net' e l hc' hl => exact hc
  | crash i' hc' =>
      by_cases hii : i = i'
      · subst hii; simp [update_Fin_gss]
      · simp [update_Fin_gso2 _ _ _ _ hii, hc]

theorem crashed_frozen {n} {s s' : PaxosState n} {t : PaxosEvent n} {i : Fin n}
    (hc : s.crashed i = true) (h : paxos_step s t s') :
    s'.proposers i = s.proposers i ∧ s'.acceptors i = s.acceptors i
      ∧ s'.learners i = s.learners i := by
  cases h with
  | proposer p' net' e i' hc' hp =>
      have hne : ¬ i = i' := fun heq => by subst heq; simp [hc] at hc'
      exact ⟨by simp [update_Fin_gso2 _ _ _ _ hne], rfl, rfl⟩
  | acceptor ac' net' e a hc' ha =>
      have hne : ¬ i = a := fun heq => by subst heq; simp [hc] at hc'
      exact ⟨rfl, by simp [update_Fin_gso2 _ _ _ _ hne], rfl⟩
  | learner l' net' e l hc' hl =>
      have hne : ¬ i = l := fun heq => by subst heq; simp [hc] at hc'
      exact ⟨rfl, rfl, by simp [update_Fin_gso2 _ _ _ _ hne]⟩
  | crash i' hc' => exact ⟨rfl, rfl, rfl⟩

theorem crashed_step_ext {n} {s s' : PaxosState n} {t : PaxosExternalEvent n} {i : Fin n}
    (hc : s.crashed i = true) (h : paxos_step_external s t s') : s'.crashed i = true := by
  cases h <;> exact hc

theorem crashed_frozen_ext {n} {s s' : PaxosState n} {t : PaxosExternalEvent n} {i : Fin n}
    (hc : s.crashed i = true) (h : paxos_step_external s t s') :
    s'.proposers i = s.proposers i ∧ s'.acceptors i = s.acceptors i
      ∧ s'.learners i = s.learners i := by
  cases h with
  | propose_rq i' v hc' hp =>
      have hne : ¬ i = i' := fun heq => by subst heq; simp [hc] at hc'
      exact ⟨by simp [update_Fin_gso2 _ _ _ _ hne], rfl, rfl⟩
  | decide_rs i' b v hc' hd hq =>
      have hne : ¬ i = i' := fun heq => by subst heq; simp [hc] at hc'
      exact ⟨rfl, rfl, by simp [update_Fin_gso2 _ _ _ _ hne]⟩

theorem crashed_reach {n} {s s' : PaxosState n} {i : Fin n}
    (h : ReflTransGen Paxos.atrans s s') (hc : s.crashed i = true) : s'.crashed i = true := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih =>
    obtain ⟨t, ht⟩ := hstep
    cases ht
    · exact crashed_step ih ‹_›
    · exact crashed_step_ext ih ‹_›


/-! ## Sicurezza

Un valore è *scelto* se una maggioranza di acceptor lo ha votato in uno stesso ballot (i
messaggi `accepted` restano nelle outbox, quindi si legge direttamente lì, come in `Paxos.tla`).
La proprietà di sicurezza di Paxos è che al più un valore viene scelto; quella osservabile
(la `correctness` del modello di Lorenzo) è che due learner non decidono valori diversi. -/

/-- `v` è scelto in `s`: c'è un ballot `b` votato per `v` da una maggioranza di acceptor. -/
def chosen {n} (s : PaxosState n) (v : Value) : Prop :=
  ∃ b, isQuorum n (count (fun a => decide (AMessage.accepted b v ∈ s.network.amsgs a)))

/-- Agreement: al più un valore è scelto. -/
def agreement {n} (s : PaxosState n) : Prop :=
  ∀ v w, chosen s v → chosen s w → v = w

/-- Correttezza: due learner che hanno deciso, hanno deciso lo stesso valore. -/
def correctness {n} (s : PaxosState n) : Prop :=
  ∀ i j v w, (s.learners i).decision = some v → (s.learners j).decision = some w → v = w

/-- Stato cattivo: due learner hanno deciso valori diversi. -/
def paxosBad {n} (s : PaxosState n) : Prop :=
  ∃ i j v w, (s.learners i).decision = some v ∧ (s.learners j).decision = some w ∧ v ≠ w


/-! ## Un'esecuzione

Il modello non è vuoto: con un solo partecipante, l'esterno chiede di proporre `7`, il protocollo
fa sei passi interni (1a, 1b, raccolta della promessa, 2a, 2b, raccolta del voto) e con il passo
esterno `decide_rs 7` decide e consegna all'esterno la decisione `7`. -/
theorem decision_reachable_one :
    ∃ s : PaxosState 1, ReflTransGen Paxos.atrans (default : PaxosState 1) s
      ∧ (s.learners 0).decision = some 7 ∧ (s.learners 0).rs = [7] := by
  -- l'esterno chiede al partecipante `0` di proporre `7`
  have c0 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail ReflTransGen.refl (Exists.intro (.ext (.part (.propose_rq 7) 0))
      (paxos_step_all.ext _ _ _ (paxos_step_external.propose_rq _ 0 7 rfl rfl)))
  -- fase 1a
  have c1 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c0 (Exists.intro (.int (.proposer (.prepare 0) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl (proposer_step.prepare _ _ 0 rfl))))
  -- fase 1b
  have c2 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c1 (Exists.intro (.int (.acceptor (.promise 0) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.promise _ _ 0 0 0 rfl trivial))))
  -- raccolta della promessa
  have c3 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c2 (Exists.intro (.int (.proposer (.collect_promise 0 0 none) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl
        (proposer_step.collect_promise _ _ 0 0 none 0 rfl rfl rfl (fun h => h)))))
  -- fase 2a
  have c4 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c3 (Exists.intro (.int (.proposer (.accept 0 7) 0))
      (paxos_step_all.int _ _ _ (paxos_step.proposer _ _ _ _ 0 rfl
        (proposer_step.accept _ _ 0 7 rfl rfl (by unfold isQuorum count; decide) rfl))))
  -- fase 2b
  have c5 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c4 (Exists.intro (.int (.acceptor (.vote 0 7) 0))
      (paxos_step_all.int _ _ _
        (paxos_step.acceptor _ _ _ _ 0 rfl (acceptor_step.vote _ _ 0 0 7 1 rfl (Nat.le_refl 0)))))
  -- raccolta del voto
  have c6 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c5 (Exists.intro (.int (.learner (.collect_accepted 0 0 7) 0))
      (paxos_step_all.int _ _ _ (paxos_step.learner _ _ _ _ 0 rfl
        (learner_step.collect_accepted _ _ 0 0 7 1 rfl (by decide)))))
  -- decisione, consegnata all'esterno
  have c7 : ReflTransGen Paxos.atrans (default : PaxosState 1) _ :=
    ReflTransGen.tail c6 (Exists.intro (.ext (.part (.decide_rs 7) 0))
      (paxos_step_all.ext _ _ _
        (paxos_step_external.decide_rs _ 0 0 7 rfl rfl (by unfold isQuorum count; decide))))
  exact ⟨_, c7, rfl, rfl⟩


/-! # Commutazione: infrastruttura

Stati di arrivo espliciti (uno per regola), lemmi di inversione (`*_inv`) e di costruzione (`mk_*`),
come in `MSI.lean`. -/

/-! ### Stati di arrivo espliciti -/

def prepareSt {n} (s : PaxosState n) (i : Fin n) (b : Ballot) : PaxosState n :=
  { s with proposers := update_Fin i
             { s.proposers i with ballot := some b, promises := fun _ => false, maxAcc := none, proposed := none }
             s.proposers,
           network := { s.network with
                        pmsgs := update_Fin i (s.network.pmsgs i ++ [PMessage.prepare b]) s.network.pmsgs } }

def collectSt {n} (s : PaxosState n) (i a : Fin n) : PaxosState n :=
  { s with proposers := update_Fin i { s.proposers i with
                          promises := update_Fin a true (s.proposers i).promises } s.proposers }

def collectUpdSt {n} (s : PaxosState n) (i a : Fin n) (acc : Option (Ballot × Value)) : PaxosState n :=
  { s with proposers := update_Fin i { s.proposers i with
                          promises := update_Fin a true (s.proposers i).promises, maxAcc := acc } s.proposers }

def acceptSt {n} (s : PaxosState n) (i : Fin n) (b : Ballot) (v : Value) : PaxosState n :=
  { s with proposers := update_Fin i { s.proposers i with proposed := some v } s.proposers,
           network := { s.network with
                        pmsgs := update_Fin i (s.network.pmsgs i ++ [PMessage.propose b v]) s.network.pmsgs } }

def promiseSt {n} (s : PaxosState n) (a : Fin n) (b : Ballot) : PaxosState n :=
  { s with acceptors := update_Fin a { s.acceptors a with maxBal := some b } s.acceptors,
           network := { s.network with
                        amsgs := update_Fin a (s.network.amsgs a ++ [AMessage.promise b (s.acceptors a).maxAcc])
                                            s.network.amsgs } }

def voteSt {n} (s : PaxosState n) (a : Fin n) (b : Ballot) (v : Value) : PaxosState n :=
  { s with acceptors := update_Fin a { s.acceptors a with maxBal := some b, maxAcc := some (b, v) } s.acceptors,
           network := { s.network with
                        amsgs := update_Fin a (s.network.amsgs a ++ [AMessage.accepted b v]) s.network.amsgs } }

def lcollectSt {n} (s : PaxosState n) (l a : Fin n) (b : Ballot) (v : Value) : PaxosState n :=
  { s with learners := update_Fin l { s.learners l with
                         accepts := update_Key (b, v) (update_Fin a true ((s.learners l).accepts (b, v)))
                                               (s.learners l).accepts } s.learners }

def decideSt {n} (s : PaxosState n) (l : Fin n) (v : Value) : PaxosState n :=
  { s with learners := update_Fin l { s.learners l with decision := some v,
                                                        rs := (s.learners l).rs ++ [v] } s.learners }

def proposeRqSt {n} (s : PaxosState n) (i : Fin n) (v : Value) : PaxosState n :=
  { s with proposers := update_Fin i { s.proposers i with pref := some v } s.proposers }

def crashSt {n} (s : PaxosState n) (i : Fin n) : PaxosState n :=
  { s with crashed := update_Fin i true s.crashed }

/-! ### Lemmi di costruzione -/

theorem mk_prepare {n} {s : PaxosState n} {i : Fin n} {b : Ballot}
    (hc : s.crashed i = false) (hb : b = nextBallot i (s.proposers i).ballot) :
    paxos_step s (.proposer (.prepare b) i) (prepareSt s i b) :=
  paxos_step.proposer s _ _ _ i hc (proposer_step.prepare _ _ b hb)

theorem mk_collect {n} {s : PaxosState n} {i a : Fin n} {b : Ballot} {acc : Option (Ballot × Value)}
    {j : Nat} (hc : s.crashed i = false)
    (hj : (s.network.amsgs a)[j]? = some (AMessage.promise b acc))
    (hb : (s.proposers i).ballot = some b) (ha : (s.proposers i).promises a = false)
    (hlt : ¬ acc_gt acc (s.proposers i).maxAcc) :
    paxos_step s (.proposer (.collect_promise a b acc) i) (collectSt s i a) :=
  paxos_step.proposer s _ _ _ i hc (proposer_step.collect_promise _ _ a b acc j hj hb ha hlt)

theorem mk_collectUpd {n} {s : PaxosState n} {i a : Fin n} {b : Ballot} {acc : Option (Ballot × Value)}
    {j : Nat} (hc : s.crashed i = false)
    (hj : (s.network.amsgs a)[j]? = some (AMessage.promise b acc))
    (hb : (s.proposers i).ballot = some b) (ha : (s.proposers i).promises a = false)
    (hgt : acc_gt acc (s.proposers i).maxAcc) :
    paxos_step s (.proposer (.collect_promise a b acc) i) (collectUpdSt s i a acc) :=
  paxos_step.proposer s _ _ _ i hc (proposer_step.collect_promise_update _ _ a b acc j hj hb ha hgt)

theorem mk_accept {n} {s : PaxosState n} {i : Fin n} {b : Ballot} {v : Value}
    (hc : s.crashed i = false) (hb : (s.proposers i).ballot = some b)
    (hp : (s.proposers i).proposed = none) (hq : isQuorum n (count (s.proposers i).promises))
    (hv : proposeValue (s.proposers i).pref (s.proposers i).maxAcc = some v) :
    paxos_step s (.proposer (.accept b v) i) (acceptSt s i b v) :=
  paxos_step.proposer s _ _ _ i hc (proposer_step.accept _ _ b v hb hp hq hv)

theorem mk_promise {n} {s : PaxosState n} {a i : Fin n} {b : Ballot} {j : Nat}
    (hc : s.crashed a = false) (hj : (s.network.pmsgs i)[j]? = some (PMessage.prepare b))
    (hb : bal_gt b (s.acceptors a).maxBal) :
    paxos_step s (.acceptor (.promise b) a) (promiseSt s a b) :=
  paxos_step.acceptor s _ _ _ a hc (acceptor_step.promise _ _ i b j hj hb)

theorem mk_vote {n} {s : PaxosState n} {a i : Fin n} {b : Ballot} {v : Value} {j : Nat}
    (hc : s.crashed a = false) (hj : (s.network.pmsgs i)[j]? = some (PMessage.propose b v))
    (hb : bal_ge b (s.acceptors a).maxBal) :
    paxos_step s (.acceptor (.vote b v) a) (voteSt s a b v) :=
  paxos_step.acceptor s _ _ _ a hc (acceptor_step.vote _ _ i b v j hj hb)

theorem mk_lcollect {n} {s : PaxosState n} {l a : Fin n} {b : Ballot} {v : Value} {j : Nat}
    (hc : s.crashed l = false) (hj : (s.network.amsgs a)[j]? = some (AMessage.accepted b v))
    (ha : (s.learners l).accepts (b, v) a = false) :
    paxos_step s (.learner (.collect_accepted a b v) l) (lcollectSt s l a b v) :=
  paxos_step.learner s _ _ _ l hc (learner_step.collect_accepted _ _ a b v j hj ha)

theorem mk_crash {n} {s : PaxosState n} {i : Fin n} (hc : s.crashed i = false) :
    paxos_step s (.crash i) (crashSt s i) :=
  paxos_step.crash s i hc

theorem mk_propose_rq {n} {s : PaxosState n} {i : Fin n} {v : Value}
    (hc : s.crashed i = false) (hp : (s.proposers i).pref = none) :
    paxos_step_external s (.part (.propose_rq v) i) (proposeRqSt s i v) :=
  paxos_step_external.propose_rq s i v hc hp

theorem mk_decide_rs {n} {s : PaxosState n} {l : Fin n} {b : Ballot} {v : Value}
    (hc : s.crashed l = false) (hd : (s.learners l).decision = none)
    (hq : isQuorum n (count ((s.learners l).accepts (b, v)))) :
    paxos_step_external s (.part (.decide_rs v) l) (decideSt s l v) :=
  paxos_step_external.decide_rs s l b v hc hd hq

/-! ### Lemmi di inversione -/

theorem prepare_inv {n} {s s' : PaxosState n} {i : Fin n} {b : Ballot}
    (h : paxos_step s (.proposer (.prepare b) i) s') :
    s.crashed i = false ∧ b = nextBallot i (s.proposers i).ballot ∧ s' = prepareSt s i b := by
  cases h with
  | proposer p' net' e i' hc hp =>
    cases hp with
    | prepare => exact ⟨hc, ‹_›, rfl⟩

theorem collect_inv {n} {s s' : PaxosState n} {i a : Fin n} {b : Ballot} {acc : Option (Ballot × Value)}
    (h : paxos_step s (.proposer (.collect_promise a b acc) i) s') :
    s.crashed i = false ∧ (∃ j : Nat, (s.network.amsgs a)[j]? = some (AMessage.promise b acc))
      ∧ (s.proposers i).ballot = some b ∧ (s.proposers i).promises a = false
      ∧ ((¬ acc_gt acc (s.proposers i).maxAcc ∧ s' = collectSt s i a)
         ∨ (acc_gt acc (s.proposers i).maxAcc ∧ s' = collectUpdSt s i a acc)) := by
  cases h with
  | proposer p' net' e i' hc hp =>
    cases hp with
    | collect_promise => exact ⟨hc, ⟨_, ‹_›⟩, ‹_›, ‹_›, Or.inl ⟨‹_›, rfl⟩⟩
    | collect_promise_update => exact ⟨hc, ⟨_, ‹_›⟩, ‹_›, ‹_›, Or.inr ⟨‹_›, rfl⟩⟩

theorem accept_inv {n} {s s' : PaxosState n} {i : Fin n} {b : Ballot} {v : Value}
    (h : paxos_step s (.proposer (.accept b v) i) s') :
    s.crashed i = false ∧ (s.proposers i).ballot = some b ∧ (s.proposers i).proposed = none
      ∧ isQuorum n (count (s.proposers i).promises)
      ∧ proposeValue (s.proposers i).pref (s.proposers i).maxAcc = some v
      ∧ s' = acceptSt s i b v := by
  cases h with
  | proposer p' net' e i' hc hp =>
    cases hp with
    | accept => exact ⟨hc, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

theorem promise_inv {n} {s s' : PaxosState n} {a : Fin n} {b : Ballot}
    (h : paxos_step s (.acceptor (.promise b) a) s') :
    s.crashed a = false ∧ (∃ (i : Fin n) (j : Nat), (s.network.pmsgs i)[j]? = some (PMessage.prepare b))
      ∧ bal_gt b (s.acceptors a).maxBal ∧ s' = promiseSt s a b := by
  cases h with
  | acceptor ac' net' e a' hc ha =>
    cases ha with
    | promise => exact ⟨hc, ⟨_, _, ‹_›⟩, ‹_›, rfl⟩

theorem vote_inv {n} {s s' : PaxosState n} {a : Fin n} {b : Ballot} {v : Value}
    (h : paxos_step s (.acceptor (.vote b v) a) s') :
    s.crashed a = false ∧ (∃ (i : Fin n) (j : Nat), (s.network.pmsgs i)[j]? = some (PMessage.propose b v))
      ∧ bal_ge b (s.acceptors a).maxBal ∧ s' = voteSt s a b v := by
  cases h with
  | acceptor ac' net' e a' hc ha =>
    cases ha with
    | vote => exact ⟨hc, ⟨_, _, ‹_›⟩, ‹_›, rfl⟩

theorem lcollect_inv {n} {s s' : PaxosState n} {l a : Fin n} {b : Ballot} {v : Value}
    (h : paxos_step s (.learner (.collect_accepted a b v) l) s') :
    s.crashed l = false ∧ (∃ j : Nat, (s.network.amsgs a)[j]? = some (AMessage.accepted b v))
      ∧ (s.learners l).accepts (b, v) a = false ∧ s' = lcollectSt s l a b v := by
  cases h with
  | learner l' net' e l₀ hc hl =>
    cases hl with
    | collect_accepted => exact ⟨hc, ⟨_, ‹_›⟩, ‹_›, rfl⟩

theorem crash_inv {n} {s s' : PaxosState n} {i : Fin n}
    (h : paxos_step s (.crash i) s') : s.crashed i = false ∧ s' = crashSt s i := by
  cases h with
  | crash => exact ⟨‹_›, rfl⟩

theorem propose_rq_inv {n} {s s' : PaxosState n} {i : Fin n} {v : Value}
    (h : paxos_step_external s (.part (.propose_rq v) i) s') :
    s.crashed i = false ∧ (s.proposers i).pref = none ∧ s' = proposeRqSt s i v := by
  cases h
  exact ⟨‹_›, ‹_›, rfl⟩

theorem decide_rs_inv {n} {s s' : PaxosState n} {l : Fin n} {v : Value}
    (h : paxos_step_external s (.part (.decide_rs v) l) s') :
    s.crashed l = false ∧ (s.learners l).decision = none
      ∧ (∃ b, isQuorum n (count ((s.learners l).accepts (b, v)))) ∧ s' = decideSt s l v := by
  cases h
  exact ⟨‹_›, ‹_›, ⟨_, ‹_›⟩, rfl⟩


/-! # Invarianti induttivi

`invE`: proprietà strutturali (unicità di promesse e proposte per ballot, voto ⇒ proposta,
promessa che riporta un voto ⇒ voto, monotonia dei ballot, decisione ⇒ quorum). `invS`: la
sicurezza di Paxos (semantica delle promesse, stato del proposer, proposte sicure `safeAt`).
Entrambi valgono in `default` e sono conservati da `paxos_step`, quindi valgono in ogni stato
raggiungibile (`inv_of_reachable`); da `invS` segue `agreement` (`agreement_of_inv`). I lemmi
ponte `not_reachable_of_*` sono le vie d'uscita `¬ Paxos.reachable s` dei teoremi di commutazione,
come `badView_unreachable` in `MSI.lean`. -/

@[simp] theorem Proposer.default_ballot {n} : (default : Proposer n).ballot = none := rfl
@[simp] theorem Proposer.default_promises {n} : (default : Proposer n).promises = fun _ => false := rfl
@[simp] theorem Proposer.default_maxAcc {n} : (default : Proposer n).maxAcc = none := rfl
@[simp] theorem Proposer.default_proposed {n} : (default : Proposer n).proposed = none := rfl
@[simp] theorem Proposer.default_pref {n} : (default : Proposer n).pref = none := rfl
@[simp] theorem Acceptor.default_maxBal : (default : Acceptor).maxBal = none := rfl
@[simp] theorem Acceptor.default_maxAcc : (default : Acceptor).maxAcc = none := rfl
@[simp] theorem Learner.default_accepts {n} : (default : Learner n).accepts = fun _ _ => false := rfl
@[simp] theorem Learner.default_decision {n} : (default : Learner n).decision = none := rfl
@[simp] theorem Learner.default_rs {n} : (default : Learner n).rs = [] := rfl
@[simp] theorem PaxosState.default_proposers {n} (i : Fin n) : (default : PaxosState n).proposers i = default := rfl
@[simp] theorem PaxosState.default_acceptors {n} (i : Fin n) : (default : PaxosState n).acceptors i = default := rfl
@[simp] theorem PaxosState.default_learners {n} (i : Fin n) : (default : PaxosState n).learners i = default := rfl
@[simp] theorem PaxosState.default_pmsgs {n} (i : Fin n) : (default : PaxosState n).network.pmsgs i = [] := rfl
@[simp] theorem PaxosState.default_amsgs {n} (i : Fin n) : (default : PaxosState n).network.amsgs i = [] := rfl
@[simp] theorem PaxosState.default_crashed {n} (i : Fin n) : (default : PaxosState n).crashed i = false := rfl

/-- Invarianti strutturali. -/
structure invE (s : PaxosState n) : Prop where
  ballot_owner : ∀ i b, (s.proposers i).ballot = some b → b % n = i.val
  propose_owner : ∀ i b v, PMessage.propose b v ∈ s.network.pmsgs i → b % n = i.val
  propose_le : ∀ i b v, PMessage.propose b v ∈ s.network.pmsgs i →
      ∃ b₀, (s.proposers i).ballot = some b₀ ∧ b ≤ b₀
  propose_current : ∀ i b v, PMessage.propose b v ∈ s.network.pmsgs i →
      (s.proposers i).ballot = some b → (s.proposers i).proposed = some v
  propose_unique : ∀ i b v v', PMessage.propose b v ∈ s.network.pmsgs i →
      PMessage.propose b v' ∈ s.network.pmsgs i → v = v'
  promise_le : ∀ a b acc, AMessage.promise b acc ∈ s.network.amsgs a →
      ∃ m, (s.acceptors a).maxBal = some m ∧ b ≤ m
  promise_unique : ∀ a b acc acc', AMessage.promise b acc ∈ s.network.amsgs a →
      AMessage.promise b acc' ∈ s.network.amsgs a → acc = acc'
  maxAcc_le : ∀ a b v, (s.acceptors a).maxAcc = some (b, v) →
      ∃ m, (s.acceptors a).maxBal = some m ∧ b ≤ m
  maxAcc_vote : ∀ a b v, (s.acceptors a).maxAcc = some (b, v) →
      AMessage.accepted b v ∈ s.network.amsgs a
  vote_le_maxAcc : ∀ a b v, AMessage.accepted b v ∈ s.network.amsgs a →
      ∃ b₀ v₀, (s.acceptors a).maxAcc = some (b₀, v₀) ∧ b ≤ b₀
  vote_propose : ∀ a b v, AMessage.accepted b v ∈ s.network.amsgs a →
      ∃ i, PMessage.propose b v ∈ s.network.pmsgs i
  report_vote : ∀ a b b' v, AMessage.promise b (some (b', v)) ∈ s.network.amsgs a →
      AMessage.accepted b' v ∈ s.network.amsgs a
  accepts_vote : ∀ l b v a, (s.learners l).accepts (b, v) a = true →
      AMessage.accepted b v ∈ s.network.amsgs a
  decision_quorum : ∀ l v, (s.learners l).decision = some v →
      ∃ b, isQuorum n (count ((s.learners l).accepts (b, v)))

/-- Una proposta `(b, v)` è *sicura* rispetto alla rete: un quorum `Q` ha promesso per `b`, ogni
promessa del quorum riporta un voto che non batte `m`, `m` (se c'è) è riportato da qualcuno del
quorum, e se `m = some (b₀, w)` allora `v = w` (con `m = none` il valore è libero: è quello chiesto
dall'esterno). È stabile: la rete non cancella mai. -/
def safeAt {n} (net : Network n) (b : Ballot) (v : Value) : Prop :=
  ∃ (Q : Fin n → Bool) (m : Option (Ballot × Value)),
    isQuorum n (count Q) ∧
    (∀ a, Q a = true → ∃ acc, AMessage.promise b acc ∈ net.amsgs a ∧ ¬ acc_gt acc m) ∧
    (∀ x, m = some x → ∃ a, Q a = true ∧ AMessage.promise b (some x) ∈ net.amsgs a) ∧
    (∀ x, m = some x → v = x.2)

/-- Invarianti di sicurezza. -/
structure invS (s : PaxosState n) : Prop where
  promise_none : ∀ a b, AMessage.promise b none ∈ s.network.amsgs a →
      ∀ b' v, AMessage.accepted b' v ∈ s.network.amsgs a → b ≤ b'
  promise_some : ∀ a b b₀ v₀, AMessage.promise b (some (b₀, v₀)) ∈ s.network.amsgs a →
      b₀ < b ∧ ∀ b' v, AMessage.accepted b' v ∈ s.network.amsgs a → b' ≤ b₀ ∨ b ≤ b'
  promises_msg : ∀ i a b, (s.proposers i).ballot = some b → (s.proposers i).promises a = true →
      ∃ acc, AMessage.promise b acc ∈ s.network.amsgs a ∧ ¬ acc_gt acc (s.proposers i).maxAcc
  maxAcc_msg : ∀ i b x, (s.proposers i).ballot = some b → (s.proposers i).maxAcc = some x →
      ∃ a, (s.proposers i).promises a = true ∧ AMessage.promise b (some x) ∈ s.network.amsgs a
  propose_safe : ∀ i b v, PMessage.propose b v ∈ s.network.pmsgs i → safeAt s.network b v

theorem invE_default {n} : invE (default : PaxosState n) where
  ballot_owner := fun _ _ h => by simp at h
  propose_owner := fun _ _ _ h => by simp at h
  propose_le := fun _ _ _ h => by simp at h
  propose_current := fun _ _ _ h => by simp at h
  propose_unique := fun _ _ _ _ h => by simp at h
  promise_le := fun _ _ _ h => by simp at h
  promise_unique := fun _ _ _ _ h => by simp at h
  maxAcc_le := fun _ _ _ h => by simp at h
  maxAcc_vote := fun _ _ _ h => by simp at h
  vote_le_maxAcc := fun _ _ _ h => by simp at h
  vote_propose := fun _ _ _ h => by simp at h
  report_vote := fun _ _ _ _ h => by simp at h
  accepts_vote := fun _ _ _ _ h => by simp at h
  decision_quorum := fun _ _ h => by simp at h

theorem invS_default {n} : invS (default : PaxosState n) where
  promise_none := fun _ _ h => by simp at h
  promise_some := fun _ _ _ _ h => by simp at h
  promises_msg := fun _ _ _ _ h => by simp at h
  maxAcc_msg := fun _ _ _ _ h => by simp at h
  propose_safe := fun _ _ _ h => by simp at h

/-- Un messaggio presente resta presente dopo un `append` in un'outbox qualsiasi. -/
theorem invE_aux_mem_app {α : Type} {n} {f : Fin n → List α} {i k : Fin n} {x m : α}
    (h : m ∈ f k) : m ∈ update_Fin i (f i ++ [x]) f k := by
  by_cases hk : i = k
  · subst hk; simp only [update_Fin_gss, List.mem_append]; exact Or.inl h
  · simp only [update_Fin_gso _ _ _ _ hk]; exact h

/-- Il messaggio appena aggiunto è nell'outbox. -/
theorem invE_aux_mem_app_self {α : Type} {n} {f : Fin n → List α} {i : Fin n} {x : α} :
    x ∈ update_Fin i (f i ++ [x]) f i := by
  simp

/-- Un messaggio in un'outbox dopo un `append` era già presente oppure è quello aggiunto. -/
theorem invE_aux_mem_app_inv {α : Type} {n} {f : Fin n → List α} {i k : Fin n} {x m : α}
    (h : m ∈ update_Fin i (f i ++ [x]) f k) : m ∈ f k ∨ (i = k ∧ m = x) := by
  by_cases hk : i = k
  · subst hk
    simp only [update_Fin_gss, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · rw [update_Fin_gso _ _ _ _ hk] at h
    exact Or.inl h

/-- Passi che cambiano solo `promises`/`maxAcc` di un proposer (`collect_promise`). -/
theorem invE_aux_prop {n} {s : PaxosState n} {i : Fin n} {p : Proposer n} (hE : invE s)
    (hb : p.ballot = (s.proposers i).ballot) (hp : p.proposed = (s.proposers i).proposed) :
    invE { s with proposers := update_Fin i p s.proposers } := by
  refine { hE with ballot_owner := ?_, propose_le := ?_, propose_current := ?_ }
  · intro k b hk
    by_cases hki : i = k
    · subst hki; simp only [update_Fin_gss] at hk; rw [hb] at hk; exact hE.ballot_owner _ _ hk
    · simp only [update_Fin_gso _ _ _ _ hki] at hk; exact hE.ballot_owner _ _ hk
  · intro k b v hm
    by_cases hki : i = k
    · subst hki; simp only [update_Fin_gss]; rw [hb]; exact hE.propose_le _ _ _ hm
    · simp only [update_Fin_gso _ _ _ _ hki]; exact hE.propose_le _ _ _ hm
  · intro k b v hm hk
    by_cases hki : i = k
    · subst hki; simp only [update_Fin_gss] at hk ⊢; rw [hb] at hk; rw [hp]
      exact hE.propose_current _ _ _ hm hk
    · simp only [update_Fin_gso _ _ _ _ hki] at hk ⊢; exact hE.propose_current _ _ _ hm hk

theorem invE_prepare_aux {n} {s : PaxosState n} {i : Fin n} {b : Ballot}
    (hE : invE s) (hb : b = nextBallot i (s.proposers i).ballot) : invE (prepareSt s i b) := by
  have hn : 0 < n := i.pos
  have hbmod : b % n = i.val := by
    rw [hb]
    cases hb0 : (s.proposers i).ballot with
    | none => simp only [nextBallot]; exact Nat.mod_eq_of_lt i.isLt
    | some b₀ => simp only [nextBallot]; rw [Nat.add_mod_right]; exact hE.ballot_owner i b₀ hb0
  have hlt : ∀ b₀, (s.proposers i).ballot = some b₀ → b₀ < b := by
    intro b₀ hb0; rw [hb, hb0]; simp only [nextBallot]; unfold Ballot at *; omega
  have hold : ∀ b' v, PMessage.propose b' v ∈ s.network.pmsgs i → b' < b := by
    intro b' v hm
    obtain ⟨b₀, hb₀, hle⟩ := hE.propose_le i b' v hm
    have := hlt b₀ hb₀; unfold Ballot at *; omega
  refine { hE with ballot_owner := ?_, propose_owner := ?_, propose_le := ?_,
                   propose_current := ?_, propose_unique := ?_, vote_propose := ?_ }
  · intro k b' hk
    by_cases hki : i = k
    · subst hki
      simp only [prepareSt, update_Fin_gss, Option.some.injEq] at hk
      rw [← hk]; exact hbmod
    · simp only [prepareSt, update_Fin_gso _ _ _ _ hki] at hk
      exact hE.ballot_owner k b' hk
  · intro k b' v hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact hE.propose_owner _ _ _ hm
    · cases he
  · intro k b' v hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hki : i = k
      · subst hki
        simp only [prepareSt, update_Fin_gss]
        exact ⟨b, rfl, Nat.le_of_lt (hold _ _ hm)⟩
      · simp only [prepareSt, update_Fin_gso _ _ _ _ hki]
        exact hE.propose_le k b' v hm
    · cases he
  · intro k b' v hm hk
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hki : i = k
      · subst hki
        simp only [prepareSt, update_Fin_gss, Option.some.injEq] at hk
        have := hold _ _ hm; unfold Ballot at *; omega
      · simp only [prepareSt, update_Fin_gso _ _ _ _ hki] at hk ⊢
        exact hE.propose_current k b' v hm hk
    · cases he
  · intro k b' v v' hm hm'
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · rcases invE_aux_mem_app_inv hm' with hm' | ⟨_, he'⟩
      · exact hE.propose_unique _ _ _ _ hm hm'
      · cases he'
    · cases he
  · intro a b' v hm
    obtain ⟨k, hk⟩ := hE.vote_propose a b' v hm
    exact ⟨k, invE_aux_mem_app hk⟩

theorem invE_accept_aux {n} {s : PaxosState n} {i : Fin n} {b : Ballot} {v : Value}
    (hE : invE s) (hb : (s.proposers i).ballot = some b) (hp : (s.proposers i).proposed = none) :
    invE (acceptSt s i b v) := by
  have hnew : ∀ v', PMessage.propose b v' ∈ s.network.pmsgs i → False := by
    intro v' hm
    have := hE.propose_current i b v' hm hb
    rw [hp] at this; cases this
  refine { hE with ballot_owner := ?_, propose_owner := ?_, propose_le := ?_,
                   propose_current := ?_, propose_unique := ?_, vote_propose := ?_ }
  · intro k b' hk
    by_cases hki : i = k
    · subst hki; simp only [acceptSt, update_Fin_gss] at hk; exact hE.ballot_owner _ _ hk
    · simp only [acceptSt, update_Fin_gso _ _ _ _ hki] at hk; exact hE.ballot_owner _ _ hk
  · intro k b' v' hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact hE.propose_owner _ _ _ hm
    · cases he; exact hE.ballot_owner _ _ hb
  · intro k b' v' hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hki : i = k
      · subst hki; simp only [acceptSt, update_Fin_gss]; exact hE.propose_le _ _ _ hm
      · simp only [acceptSt, update_Fin_gso _ _ _ _ hki]; exact hE.propose_le _ _ _ hm
    · cases he; simp only [acceptSt, update_Fin_gss]; exact ⟨_, hb, le_rfl⟩
  · intro k b' v' hm hk
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hki : i = k
      · subst hki
        simp only [acceptSt, update_Fin_gss] at hk ⊢
        rw [hb, Option.some.injEq] at hk
        subst hk
        exact absurd hm (hnew _)
      · simp only [acceptSt, update_Fin_gso _ _ _ _ hki] at hk ⊢
        exact hE.propose_current _ _ _ hm hk
    · cases he; simp only [acceptSt, update_Fin_gss]
  · intro k b' v₁ v₂ hm hm'
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · rcases invE_aux_mem_app_inv hm' with hm' | ⟨rfl, he'⟩
      · exact hE.propose_unique _ _ _ _ hm hm'
      · cases he'; exact absurd hm (hnew _)
    · cases he
      rcases invE_aux_mem_app_inv hm' with hm' | ⟨_, he'⟩
      · exact absurd hm' (hnew _)
      · cases he'; rfl
  · intro a b' v' hm
    obtain ⟨k, hk⟩ := hE.vote_propose a b' v' hm
    exact ⟨k, invE_aux_mem_app hk⟩

theorem invE_promise_aux {n} {s : PaxosState n} {a : Fin n} {b : Ballot}
    (hE : invE s) (hbal : bal_gt b (s.acceptors a).maxBal) : invE (promiseSt s a b) := by
  have hold : ∀ b' acc, AMessage.promise b' acc ∈ s.network.amsgs a → b' < b := by
    intro b' acc hm
    obtain ⟨m, hm', hle⟩ := hE.promise_le a b' acc hm
    rw [hm'] at hbal; simp only [bal_gt] at hbal; unfold Ballot at *; omega
  refine { hE with promise_le := ?_, promise_unique := ?_, maxAcc_le := ?_, maxAcc_vote := ?_,
                   vote_le_maxAcc := ?_, vote_propose := ?_, report_vote := ?_, accepts_vote := ?_ }
  · intro k b' acc hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hka : a = k
      · subst hka; simp only [promiseSt, update_Fin_gss]
        exact ⟨b, rfl, Nat.le_of_lt (hold _ _ hm)⟩
      · simp only [promiseSt, update_Fin_gso _ _ _ _ hka]; exact hE.promise_le _ _ _ hm
    · cases he; simp only [promiseSt, update_Fin_gss]; exact ⟨_, rfl, le_rfl⟩
  · intro k b' acc acc' hm hm'
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · rcases invE_aux_mem_app_inv hm' with hm' | ⟨rfl, he'⟩
      · exact hE.promise_unique _ _ _ _ hm hm'
      · cases he'; have := hold _ _ hm; unfold Ballot at *; omega
    · cases he
      rcases invE_aux_mem_app_inv hm' with hm' | ⟨_, he'⟩
      · have := hold _ _ hm'; unfold Ballot at *; omega
      · cases he'; rfl
  · intro k b' v hk
    by_cases hka : a = k
    · subst hka
      simp only [promiseSt, update_Fin_gss] at hk ⊢
      obtain ⟨m, hm, hle⟩ := hE.maxAcc_le _ _ _ hk
      rw [hm] at hbal; simp only [bal_gt] at hbal
      exact ⟨b, rfl, by unfold Ballot at *; omega⟩
    · simp only [promiseSt, update_Fin_gso _ _ _ _ hka] at hk ⊢
      exact hE.maxAcc_le _ _ _ hk
  · intro k b' v hk
    by_cases hka : a = k
    · subst hka
      simp only [promiseSt, update_Fin_gss] at hk
      exact invE_aux_mem_app (hE.maxAcc_vote _ _ _ hk)
    · simp only [promiseSt, update_Fin_gso _ _ _ _ hka] at hk
      exact invE_aux_mem_app (hE.maxAcc_vote _ _ _ hk)
  · intro k b' v hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hka : a = k
      · subst hka; simp only [promiseSt, update_Fin_gss]; exact hE.vote_le_maxAcc _ _ _ hm
      · simp only [promiseSt, update_Fin_gso _ _ _ _ hka]; exact hE.vote_le_maxAcc _ _ _ hm
    · cases he
  · intro k b' v hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact hE.vote_propose _ _ _ hm
    · cases he
  · intro k b₁ b' v hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact invE_aux_mem_app (hE.report_vote _ _ _ _ hm)
    · injection he with h1 h2
      exact invE_aux_mem_app (hE.maxAcc_vote _ _ _ h2.symm)
  · intro l b' v k hk
    exact invE_aux_mem_app (hE.accepts_vote _ _ _ _ hk)

theorem invE_vote_aux {n} {s : PaxosState n} {a i : Fin n} {b : Ballot} {v : Value} {j : Nat}
    (hE : invE s) (hj : (s.network.pmsgs i)[j]? = some (PMessage.propose b v))
    (hbal : bal_ge b (s.acceptors a).maxBal) : invE (voteSt s a b v) := by
  have hprop : PMessage.propose b v ∈ s.network.pmsgs i := List.mem_of_getElem? hj
  have hold : ∀ b' acc, AMessage.promise b' acc ∈ s.network.amsgs a → b' ≤ b := by
    intro b' acc hm
    obtain ⟨m, hm', hle⟩ := hE.promise_le a b' acc hm
    rw [hm'] at hbal; simp only [bal_ge] at hbal; unfold Ballot at *; omega
  have holdv : ∀ b' v', AMessage.accepted b' v' ∈ s.network.amsgs a → b' ≤ b := by
    intro b' v' hm
    obtain ⟨b₀, v₀, h₀, hle⟩ := hE.vote_le_maxAcc a b' v' hm
    obtain ⟨m, hm', hle'⟩ := hE.maxAcc_le a b₀ v₀ h₀
    rw [hm'] at hbal; simp only [bal_ge] at hbal; unfold Ballot at *; omega
  refine { hE with promise_le := ?_, promise_unique := ?_, maxAcc_le := ?_, maxAcc_vote := ?_,
                   vote_le_maxAcc := ?_, vote_propose := ?_, report_vote := ?_, accepts_vote := ?_ }
  · intro k b' acc hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hka : a = k
      · subst hka; simp only [voteSt, update_Fin_gss]; exact ⟨b, rfl, hold _ _ hm⟩
      · simp only [voteSt, update_Fin_gso _ _ _ _ hka]; exact hE.promise_le _ _ _ hm
    · cases he
  · intro k b' acc acc' hm hm'
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · rcases invE_aux_mem_app_inv hm' with hm' | ⟨rfl, he'⟩
      · exact hE.promise_unique _ _ _ _ hm hm'
      · cases he'
    · cases he
  · intro k b' v' hk
    by_cases hka : a = k
    · subst hka
      simp only [voteSt, update_Fin_gss, Option.some.injEq, Prod.mk.injEq] at hk ⊢
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨_, rfl, le_rfl⟩
    · simp only [voteSt, update_Fin_gso _ _ _ _ hka] at hk ⊢
      exact hE.maxAcc_le _ _ _ hk
  · intro k b' v' hk
    by_cases hka : a = k
    · subst hka
      simp only [voteSt, update_Fin_gss, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact invE_aux_mem_app_self
    · simp only [voteSt, update_Fin_gso _ _ _ _ hka] at hk
      exact invE_aux_mem_app (hE.maxAcc_vote _ _ _ hk)
  · intro k b' v' hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · by_cases hka : a = k
      · subst hka; simp only [voteSt, update_Fin_gss]; exact ⟨b, v, rfl, holdv _ _ hm⟩
      · simp only [voteSt, update_Fin_gso _ _ _ _ hka]; exact hE.vote_le_maxAcc _ _ _ hm
    · cases he; simp only [voteSt, update_Fin_gss]; exact ⟨_, _, rfl, le_rfl⟩
  · intro k b' v' hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact hE.vote_propose _ _ _ hm
    · cases he; exact ⟨i, hprop⟩
  · intro k b₁ b' v' hm
    rcases invE_aux_mem_app_inv hm with hm | ⟨rfl, he⟩
    · exact invE_aux_mem_app (hE.report_vote _ _ _ _ hm)
    · cases he
  · intro l b' v' k hk
    exact invE_aux_mem_app (hE.accepts_vote _ _ _ _ hk)

theorem invE_lcollect_aux {n} {s : PaxosState n} {l a : Fin n} {b : Ballot} {v : Value} {j : Nat}
    (hE : invE s) (hj : (s.network.amsgs a)[j]? = some (AMessage.accepted b v)) :
    invE (lcollectSt s l a b v) := by
  have hacc : AMessage.accepted b v ∈ s.network.amsgs a := List.mem_of_getElem? hj
  refine { hE with accepts_vote := ?_, decision_quorum := ?_ }
  · intro k b' v' a' hk
    by_cases hkl : l = k
    · subst hkl
      simp only [lcollectSt, update_Fin_gss] at hk
      by_cases hbv : (b', v') = (b, v)
      · rw [hbv, update_Key_gss] at hk
        simp only [Prod.mk.injEq] at hbv
        obtain ⟨rfl, rfl⟩ := hbv
        by_cases haa : a = a'
        · subst haa; exact hacc
        · rw [update_Fin_gso _ _ _ _ haa] at hk
          exact hE.accepts_vote _ _ _ _ hk
      · rw [update_Key_gso2 _ _ _ _ hbv] at hk
        exact hE.accepts_vote _ _ _ _ hk
    · simp only [lcollectSt, update_Fin_gso _ _ _ _ hkl] at hk
      exact hE.accepts_vote _ _ _ _ hk
  · intro k v' hd
    by_cases hkl : l = k
    · subst hkl
      simp only [lcollectSt, update_Fin_gss] at hd ⊢
      obtain ⟨b₀, hq⟩ := hE.decision_quorum _ _ hd
      refine ⟨b₀, ?_⟩
      by_cases hbv : (b₀, v') = (b, v)
      · rw [hbv, update_Key_gss]
        rw [hbv] at hq
        have := count_le_update ((s.learners l).accepts (b, v)) a
        unfold isQuorum at hq ⊢
        omega
      · rw [update_Key_gso2 _ _ _ _ hbv]; exact hq
    · simp only [lcollectSt, update_Fin_gso _ _ _ _ hkl] at hd ⊢
      exact hE.decision_quorum _ _ hd

theorem invE_decide_aux {n} {s : PaxosState n} {l : Fin n} {b : Ballot} {v : Value}
    (hE : invE s) (hq : isQuorum n (count ((s.learners l).accepts (b, v)))) :
    invE (decideSt s l v) := by
  refine { hE with accepts_vote := ?_, decision_quorum := ?_ }
  · intro k b' v' a' hk
    by_cases hkl : l = k
    · subst hkl; simp only [decideSt, update_Fin_gss] at hk; exact hE.accepts_vote _ _ _ _ hk
    · simp only [decideSt, update_Fin_gso _ _ _ _ hkl] at hk; exact hE.accepts_vote _ _ _ _ hk
  · intro k v' hd
    by_cases hkl : l = k
    · subst hkl
      simp only [decideSt, update_Fin_gss, Option.some.injEq] at hd ⊢
      subst hd
      exact ⟨b, hq⟩
    · simp only [decideSt, update_Fin_gso _ _ _ _ hkl] at hd ⊢
      exact hE.decision_quorum _ _ hd

theorem invE_crash_aux {n} {s : PaxosState n} {i : Fin n} (hE : invE s) : invE (crashSt s i) :=
  { hE with }

/-- `invE` è conservato da ogni passo. -/
theorem invE_step {n} {s s' : PaxosState n} {t : PaxosEvent n}
    (hE : invE s) (h : paxos_step s t s') : invE s' := by
  cases t with
  | proposer e i =>
    cases e with
    | prepare b =>
      obtain ⟨hc, hb, rfl⟩ := prepare_inv h
      exact invE_prepare_aux hE hb
    | collect_promise a b acc =>
      obtain ⟨hc, ⟨j, hj⟩, hb, ha, hcase⟩ := collect_inv h
      rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
      · exact invE_aux_prop hE rfl rfl
      · exact invE_aux_prop hE rfl rfl
    | accept b v =>
      obtain ⟨hc, hb, hp, hq, hv, rfl⟩ := accept_inv h
      exact invE_accept_aux hE hb hp
  | acceptor e a =>
    cases e with
    | promise b =>
      obtain ⟨hc, ⟨i, j, hj⟩, hbal, rfl⟩ := promise_inv h
      exact invE_promise_aux hE hbal
    | vote b v =>
      obtain ⟨hc, ⟨i, j, hj⟩, hbal, rfl⟩ := vote_inv h
      exact invE_vote_aux hE hj hbal
  | learner e l =>
    cases e with
    | collect_accepted a b v =>
      obtain ⟨hc, ⟨j, hj⟩, ha, rfl⟩ := lcollect_inv h
      exact invE_lcollect_aux hE hj
  | crash i =>
    obtain ⟨hc, rfl⟩ := crash_inv h
    exact invE_crash_aux hE

/-- `safeAt` è monotono rispetto alla rete (le outbox non perdono mai messaggi). -/
theorem invS_step_aux_safeAt_mono {n} {net net' : Network n} {b : Ballot} {v : Value}
    (h : ∀ a m, m ∈ net.amsgs a → m ∈ net'.amsgs a) (hs : safeAt net b v) : safeAt net' b v := by
  obtain ⟨Q, m, hQ, h1, h2, h3⟩ := hs
  refine ⟨Q, m, hQ, ?_, ?_, h3⟩
  · intro a ha
    obtain ⟨acc, hm, hlt⟩ := h1 a ha
    exact ⟨acc, h _ _ hm, hlt⟩
  · intro x hx
    obtain ⟨a, ha, hm⟩ := h2 x hx
    exact ⟨a, ha, h _ _ hm⟩

/-- Un messaggio presente resta presente dopo un `append` in una outbox qualsiasi. -/
theorem invS_step_aux_mem_append {α : Type} {n} (f : Fin n → List α) (a a' : Fin n) (l : List α)
    {m : α} (h : m ∈ f a') : m ∈ update_Fin a (f a ++ l) f a' := by
  by_cases hk : a' = a
  · subst hk; simp only [update_Fin_gss]; exact List.mem_append_left _ h
  · simp only [update_Fin_gso2 _ _ _ _ hk]; exact h

/-- Un messaggio nella outbox dopo un `append` di `[x]`: o c'era già, o è `x` nella outbox toccata. -/
theorem invS_step_aux_mem_append_elim {α : Type} {n} (f : Fin n → List α) (a a' : Fin n) (x : α)
    {m : α} (h : m ∈ update_Fin a (f a ++ [x]) f a') : m ∈ f a' ∨ (a' = a ∧ m = x) := by
  by_cases hk : a' = a
  · subst hk
    simp only [update_Fin_gss] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, List.mem_singleton.mp h⟩
  · simp only [update_Fin_gso2 _ _ _ _ hk] at h
    exact Or.inl h

theorem invS_step_aux_acc_gt_irrefl (acc : Option (Ballot × Value)) : ¬ acc_gt acc acc := by
  rcases acc with _ | ⟨b, v⟩ <;> simp [acc_gt]

theorem invS_step_aux_acc_gt_upd {acc acc' old : Option (Ballot × Value)}
    (h1 : acc_gt acc old) (h2 : ¬ acc_gt acc' old) : ¬ acc_gt acc' acc := by
  rcases acc with _ | ⟨b, v⟩ <;> rcases acc' with _ | ⟨b', v'⟩ <;> rcases old with _ | ⟨b₀, v₀⟩
    <;> simp [acc_gt] at *
  exact Nat.le_trans h2 (Nat.le_of_lt h1)

/-- `invS` è conservato da ogni passo (usando `invE` sullo stato di partenza). -/
theorem invS_step {n} {s s' : PaxosState n} {t : PaxosEvent n}
    (hE : invE s) (hS : invS s) (h : paxos_step s t s') : invS s' := by
  cases t with
  | proposer e i =>
    cases e with
    | prepare b =>
      obtain ⟨hc, hb, rfl⟩ := prepare_inv h
      refine ⟨hS.promise_none, hS.promise_some, ?_, ?_, ?_⟩
      · intro i' a b' hb' hp'
        simp only [prepareSt] at hb' hp' ⊢
        by_cases hi : i' = i
        · subst hi
          simp only [update_Fin_gss] at hp'
          simp at hp'
        · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hp' ⊢
          exact hS.promises_msg i' a b' hb' hp'
      · intro i' b' x hb' hx
        simp only [prepareSt] at hb' hx ⊢
        by_cases hi : i' = i
        · subst hi
          simp only [update_Fin_gss] at hx
          simp at hx
        · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hx ⊢
          exact hS.maxAcc_msg i' b' x hb' hx
      · intro i' b' v hm
        simp only [prepareSt] at hm ⊢
        have hm' : PMessage.propose b' v ∈ s.network.pmsgs i' := by
          rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm | ⟨_, hm⟩
          · exact hm
          · cases hm
        exact invS_step_aux_safeAt_mono (fun _ _ hm => hm) (hS.propose_safe i' b' v hm')
    | collect_promise a b acc =>
      obtain ⟨hc, ⟨j, hj⟩, hb, ha, hcase⟩ := collect_inv h
      have hjm := List.mem_of_getElem? hj
      rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
      · refine ⟨hS.promise_none, hS.promise_some, ?_, ?_, hS.propose_safe⟩
        · intro i' a' b' hb' hp'
          simp only [collectSt] at hb' hp' ⊢
          by_cases hi : i' = i
          · subst hi
            simp only [update_Fin_gss] at hb' hp' ⊢
            by_cases haa : a' = a
            · subst haa
              rw [hb] at hb'; injection hb' with hb'; subst hb'
              exact ⟨acc, hjm, hlt⟩
            · simp only [update_Fin_gso2 _ _ _ _ haa] at hp'
              exact hS.promises_msg _ a' b' hb' hp'
          · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hp' ⊢
            exact hS.promises_msg i' a' b' hb' hp'
        · intro i' b' x hb' hx
          simp only [collectSt] at hb' hx ⊢
          by_cases hi : i' = i
          · subst hi
            simp only [update_Fin_gss] at hb' hx ⊢
            obtain ⟨a', hp', hm⟩ := hS.maxAcc_msg _ b' x hb' hx
            refine ⟨a', ?_, hm⟩
            by_cases haa : a' = a
            · subst haa; simp only [update_Fin_gss]
            · simp only [update_Fin_gso2 _ _ _ _ haa]; exact hp'
          · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hx ⊢
            exact hS.maxAcc_msg i' b' x hb' hx
      · refine ⟨hS.promise_none, hS.promise_some, ?_, ?_, hS.propose_safe⟩
        · intro i' a' b' hb' hp'
          simp only [collectUpdSt] at hb' hp' ⊢
          by_cases hi : i' = i
          · subst hi
            simp only [update_Fin_gss] at hb' hp' ⊢
            rw [hb] at hb'; injection hb' with hb'; subst hb'
            by_cases haa : a' = a
            · subst haa
              exact ⟨acc, hjm, invS_step_aux_acc_gt_irrefl acc⟩
            · simp only [update_Fin_gso2 _ _ _ _ haa] at hp'
              obtain ⟨acc', hm, hlt'⟩ := hS.promises_msg _ a' _ hb hp'
              exact ⟨acc', hm, invS_step_aux_acc_gt_upd hgt hlt'⟩
          · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hp' ⊢
            exact hS.promises_msg i' a' b' hb' hp'
        · intro i' b' x hb' hx
          simp only [collectUpdSt] at hb' hx ⊢
          by_cases hi : i' = i
          · subst hi
            simp only [update_Fin_gss] at hb' hx ⊢
            rw [hb] at hb'; injection hb' with hb'; subst hb'
            subst hx
            exact ⟨a, by simp only [update_Fin_gss], hjm⟩
          · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hx ⊢
            exact hS.maxAcc_msg i' b' x hb' hx
    | accept b v =>
      obtain ⟨hc, hb, hp, hq, hv, rfl⟩ := accept_inv h
      refine ⟨hS.promise_none, hS.promise_some, ?_, ?_, ?_⟩
      · intro i' a' b' hb' hp'
        simp only [acceptSt] at hb' hp' ⊢
        by_cases hi : i' = i
        · subst hi
          simp only [update_Fin_gss] at hb' hp' ⊢
          exact hS.promises_msg _ a' b' hb' hp'
        · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hp' ⊢
          exact hS.promises_msg i' a' b' hb' hp'
      · intro i' b' x hb' hx
        simp only [acceptSt] at hb' hx ⊢
        by_cases hi : i' = i
        · subst hi
          simp only [update_Fin_gss] at hb' hx ⊢
          exact hS.maxAcc_msg _ b' x hb' hx
        · simp only [update_Fin_gso2 _ _ _ _ hi] at hb' hx ⊢
          exact hS.maxAcc_msg i' b' x hb' hx
      · intro i' b' v' hm
        simp only [acceptSt] at hm ⊢
        rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm | ⟨hi, hm⟩
        · exact invS_step_aux_safeAt_mono (fun _ _ hm => hm) (hS.propose_safe i' b' v' hm)
        · injection hm with hb1 hv1
          subst hi; subst hb1; subst hv1
          refine ⟨(s.proposers _).promises, (s.proposers _).maxAcc, hq, ?_, ?_, proposeValue_some hv⟩
          · intro a ha; exact hS.promises_msg _ a _ hb ha
          · intro x hx; exact hS.maxAcc_msg _ _ x hb hx
  | acceptor e a =>
    cases e with
    | promise b =>
      obtain ⟨hc, ⟨i, j, hj⟩, hbal, rfl⟩ := promise_inv h
      have hmono : ∀ a' m, m ∈ s.network.amsgs a' → m ∈ (promiseSt s a b).network.amsgs a' := by
        intro a' m hm
        simp only [promiseSt]
        exact invS_step_aux_mem_append _ _ _ _ hm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a' b' hm b'' v' hv
        simp only [promiseSt] at hm hv
        rcases invS_step_aux_mem_append_elim _ _ _ _ hv with hv₁ | ⟨_, hv₁⟩
        · rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm₁ | ⟨haa, hm₁⟩
          · exact hS.promise_none a' b' hm₁ b'' v' hv₁
          · subst haa
            injection hm₁ with hb1 hacc
            obtain ⟨b₀, v₀, hacc', _⟩ := hE.vote_le_maxAcc _ b'' v' hv₁
            rw [hacc'] at hacc; cases hacc
        · cases hv₁
      · intro a' b' b₀ v₀ hm
        simp only [promiseSt] at hm ⊢
        rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm₁ | ⟨haa, hm₁⟩
        · obtain ⟨hlt, hall⟩ := hS.promise_some a' b' b₀ v₀ hm₁
          refine ⟨hlt, ?_⟩
          intro b'' v' hv
          rcases invS_step_aux_mem_append_elim _ _ _ _ hv with hv₁ | ⟨_, hv₁⟩
          · exact hall b'' v' hv₁
          · cases hv₁
        · subst haa
          injection hm₁ with hb1 hacc
          subst hb1
          obtain ⟨m, hmb, hle⟩ := hE.maxAcc_le _ b₀ v₀ hacc.symm
          rw [hmb] at hbal
          simp only [bal_gt] at hbal
          refine ⟨Nat.lt_of_le_of_lt hle hbal, ?_⟩
          intro b'' v' hv
          rcases invS_step_aux_mem_append_elim _ _ _ _ hv with hv₁ | ⟨_, hv₁⟩
          · obtain ⟨b₁, v₁, hacc₁, hle₁⟩ := hE.vote_le_maxAcc _ b'' v' hv₁
            rw [← hacc] at hacc₁
            injection hacc₁ with hacc₁
            injection hacc₁ with hb2 _
            left; rw [hb2]; exact hle₁
          · cases hv₁
      · intro i' a' b' hb' hp'
        obtain ⟨acc, hm, hlt⟩ := hS.promises_msg i' a' b' hb' hp'
        exact ⟨acc, hmono a' _ hm, hlt⟩
      · intro i' b' x hb' hx
        obtain ⟨a', hp', hm⟩ := hS.maxAcc_msg i' b' x hb' hx
        exact ⟨a', hp', hmono a' _ hm⟩
      · intro i' b' v' hm
        exact invS_step_aux_safeAt_mono hmono (hS.propose_safe i' b' v' hm)
    | vote b v =>
      obtain ⟨hc, ⟨i, j, hj⟩, hbal, rfl⟩ := vote_inv h
      have hmono : ∀ a' m, m ∈ s.network.amsgs a' → m ∈ (voteSt s a b v).network.amsgs a' := by
        intro a' m hm
        simp only [voteSt]
        exact invS_step_aux_mem_append _ _ _ _ hm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a' b' hm b'' v' hv
        simp only [voteSt] at hm hv
        rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm₁ | ⟨_, hm₁⟩
        · rcases invS_step_aux_mem_append_elim _ _ _ _ hv with hv₁ | ⟨haa, hv₁⟩
          · exact hS.promise_none a' b' hm₁ b'' v' hv₁
          · subst haa
            injection hv₁ with hb1 _
            subst hb1
            obtain ⟨m, hmb, hle⟩ := hE.promise_le _ b' none hm₁
            rw [hmb] at hbal
            simp only [bal_ge] at hbal
            exact Nat.le_trans hle hbal
        · cases hm₁
      · intro a' b' b₀ v₀ hm
        simp only [voteSt] at hm ⊢
        rcases invS_step_aux_mem_append_elim _ _ _ _ hm with hm₁ | ⟨_, hm₁⟩
        · obtain ⟨hlt, hall⟩ := hS.promise_some a' b' b₀ v₀ hm₁
          refine ⟨hlt, ?_⟩
          intro b'' v' hv
          rcases invS_step_aux_mem_append_elim _ _ _ _ hv with hv₁ | ⟨haa, hv₁⟩
          · exact hall b'' v' hv₁
          · subst haa
            injection hv₁ with hb1 _
            subst hb1
            obtain ⟨m, hmb, hle⟩ := hE.promise_le _ b' _ hm₁
            rw [hmb] at hbal
            simp only [bal_ge] at hbal
            exact Or.inr (Nat.le_trans hle hbal)
        · cases hm₁
      · intro i' a' b' hb' hp'
        obtain ⟨acc, hm, hlt⟩ := hS.promises_msg i' a' b' hb' hp'
        exact ⟨acc, hmono a' _ hm, hlt⟩
      · intro i' b' x hb' hx
        obtain ⟨a', hp', hm⟩ := hS.maxAcc_msg i' b' x hb' hx
        exact ⟨a', hp', hmono a' _ hm⟩
      · intro i' b' v' hm
        exact invS_step_aux_safeAt_mono hmono (hS.propose_safe i' b' v' hm)
  | learner e l =>
    cases e with
    | collect_accepted a b v =>
      obtain ⟨_, _, _, rfl⟩ := lcollect_inv h
      exact ⟨hS.promise_none, hS.promise_some, hS.promises_msg, hS.maxAcc_msg, hS.propose_safe⟩
  | crash i =>
    obtain ⟨_, rfl⟩ := crash_inv h
    exact ⟨hS.promise_none, hS.promise_some, hS.promises_msg, hS.maxAcc_msg, hS.propose_safe⟩

/-- `invE` è conservato dai passi esterni. -/
theorem invE_step_ext {n} {s s' : PaxosState n} {t : PaxosExternalEvent n}
    (hE : invE s) (h : paxos_step_external s t s') : invE s' := by
  cases t with
  | part e i =>
    cases e with
    | propose_rq v =>
      obtain ⟨hc, hp, rfl⟩ := propose_rq_inv h
      refine ⟨?_, hE.propose_owner, ?_, ?_, hE.propose_unique, hE.promise_le, hE.promise_unique,
        hE.maxAcc_le, hE.maxAcc_vote, hE.vote_le_maxAcc, hE.vote_propose, hE.report_vote,
        hE.accepts_vote, hE.decision_quorum⟩
      · intro k b hb
        simp only [proposeRqSt] at hb
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hb; exact hE.ballot_owner _ b hb
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hb; exact hE.ballot_owner k b hb
      · intro k b w hm
        simp only [proposeRqSt] at hm ⊢
        obtain ⟨b₀, hb₀, hle⟩ := hE.propose_le k b w hm
        refine ⟨b₀, ?_, hle⟩
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss]; exact hb₀
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact hb₀
      · intro k b w hm hb
        simp only [proposeRqSt] at hm hb ⊢
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hb ⊢; exact hE.propose_current _ b w hm hb
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hb ⊢; exact hE.propose_current k b w hm hb
    | decide_rs v =>
      obtain ⟨hc, hd, ⟨b, hq⟩, rfl⟩ := decide_rs_inv h
      exact invE_decide_aux hE hq

/-- `invS` è conservato dai passi esterni. -/
theorem invS_step_ext {n} {s s' : PaxosState n} {t : PaxosExternalEvent n}
    (hS : invS s) (h : paxos_step_external s t s') : invS s' := by
  cases t with
  | part e i =>
    cases e with
    | propose_rq v =>
      obtain ⟨hc, hp, rfl⟩ := propose_rq_inv h
      refine ⟨hS.promise_none, hS.promise_some, ?_, ?_, hS.propose_safe⟩
      · intro k a b hb hpr
        simp only [proposeRqSt] at hb hpr ⊢
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hb hpr ⊢; exact hS.promises_msg _ a b hb hpr
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hb hpr ⊢; exact hS.promises_msg k a b hb hpr
      · intro k b x hb hx
        simp only [proposeRqSt] at hb hx ⊢
        by_cases hk : k = i
        · subst hk; simp only [update_Fin_gss] at hb hx ⊢; exact hS.maxAcc_msg _ b x hb hx
        · simp only [update_Fin_gso2 _ _ _ _ hk] at hb hx ⊢; exact hS.maxAcc_msg k b x hb hx
    | decide_rs v =>
      obtain ⟨_, _, _, rfl⟩ := decide_rs_inv h
      exact ⟨hS.promise_none, hS.promise_some, hS.promises_msg, hS.maxAcc_msg, hS.propose_safe⟩

/-- Ogni stato raggiungibile soddisfa gli invarianti. -/
theorem inv_of_reachable {n} {s : PaxosState n} (h : Paxos.reachable s) : invE s ∧ invS s := by
  have key : ∀ x, ReflTransGen Paxos.atrans (default : PaxosState n) x → invE x ∧ invS x := by
    intro x hx
    induction hx with
    | refl => exact ⟨invE_default, invS_default⟩
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      cases ht
      · exact ⟨invE_step ih.1 ‹_›, invS_step ih.1 ih.2 ‹_›⟩
      · exact ⟨invE_step_ext ih.1 ‹_›, invS_step_ext ih.2 ‹_›⟩
  exact key s (h _ paxos_init_default)

/-- Un quorum non è vuoto: c'è almeno un indice che soddisfa `P`. -/
theorem agreement_of_inv_aux1 {n} (P : Fin n → Bool) (hq : isQuorum n (count P)) :
    ∃ a, P a = true := by
  unfold isQuorum count at hq
  by_contra hno
  push Not at hno
  have h0 : (List.finRange n).countP P = 0 := by
    rw [List.countP_eq_zero]
    intro a _
    simp [hno a]
  omega

/-- Lemma chiave: se `(b₁, v₁)` è votato da un quorum, ogni proposta con ballot `b₂ ≥ b₁`
porta il valore `v₁` (induzione forte su `b₂`). -/
theorem agreement_of_inv_aux2 {n} {s : PaxosState n} (hE : invE s) (hS : invS s)
    (b₁ : Ballot) (v₁ : Value)
    (hq : isQuorum n (count (fun a => decide (AMessage.accepted b₁ v₁ ∈ s.network.amsgs a)))) :
    ∀ b₂ v₂ (i : Fin n), PMessage.propose b₂ v₂ ∈ s.network.pmsgs i → b₁ ≤ b₂ → v₂ = v₁ := by
  intro b₂
  induction b₂ using Nat.strong_induction_on with
  | _ b₂ ih =>
  intro v₂ i hp hle
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · subst heq
    obtain ⟨a, ha⟩ := agreement_of_inv_aux1 _ hq
    simp only [decide_eq_true_eq] at ha
    obtain ⟨i', hi'⟩ := hE.vote_propose a b₁ v₁ ha
    have e₁ := hE.propose_owner i b₁ v₂ hp
    have e₂ := hE.propose_owner i' b₁ v₁ hi'
    have hii : i = i' := Fin.ext (e₁.symm.trans e₂)
    subst hii
    exact hE.propose_unique i b₁ v₂ v₁ hp hi'
  · obtain ⟨Q, m, hQ, hprom, hmax, hv⟩ := hS.propose_safe i b₂ v₂ hp
    obtain ⟨a, haQ, hav⟩ := quorum_intersect Q _ hQ hq
    simp only [decide_eq_true_eq] at hav
    obtain ⟨acc, hacc, hngt⟩ := hprom a haQ
    cases acc with
    | none =>
      have := hS.promise_none a b₂ hacc b₁ v₁ hav
      exact absurd (Nat.lt_of_lt_of_le hlt this) (Nat.lt_irrefl _)
    | some p =>
      rcases p with ⟨b₀, v₀⟩
      obtain ⟨hb₀, hall⟩ := hS.promise_some a b₂ b₀ v₀ hacc
      have h₁₀ : b₁ ≤ b₀ := by
        rcases hall b₁ v₁ hav with h | h
        · exact h
        · exact absurd (Nat.lt_of_lt_of_le hlt h) (Nat.lt_irrefl _)
      cases m with
      | none => simp [acc_gt] at hngt
      | some q =>
        rcases q with ⟨bs, vs⟩
        simp only [acc_gt, not_lt] at hngt
        obtain ⟨a', ha'Q, ha'p⟩ := hmax (bs, vs) rfl
        obtain ⟨hbs, _⟩ := hS.promise_some a' b₂ bs vs ha'p
        have hvote := hE.report_vote a' b₂ bs vs ha'p
        obtain ⟨i'', hi''⟩ := hE.vote_propose a' bs vs hvote
        have hvs := ih bs hbs vs i'' hi'' (Nat.le_trans h₁₀ hngt)
        exact (hv (bs, vs) rfl).trans hvs

/-- **Sicurezza di Paxos**: dagli invarianti segue che al più un valore è scelto. -/
theorem agreement_of_inv {n} {s : PaxosState n} (hE : invE s) (hS : invS s) : agreement s := by
  intro v w ⟨b, hq⟩ ⟨b', hq'⟩
  rcases le_total b b' with h | h
  · obtain ⟨a', ha'⟩ := agreement_of_inv_aux1 _ hq'
    simp only [decide_eq_true_eq] at ha'
    obtain ⟨i, hi⟩ := hE.vote_propose a' b' w ha'
    exact (agreement_of_inv_aux2 hE hS b v hq b' w i hi h).symm
  · obtain ⟨a', ha'⟩ := agreement_of_inv_aux1 _ hq
    simp only [decide_eq_true_eq] at ha'
    obtain ⟨i, hi⟩ := hE.vote_propose a' b v ha'
    exact agreement_of_inv_aux2 hE hS b' w hq' b v i hi h

theorem agreement_of_reachable {n} {s : PaxosState n} (h : Paxos.reachable s) : agreement s :=
  let ⟨hE, hS⟩ := inv_of_reachable h
  agreement_of_inv hE hS

/-- Un quorum di voti raccolti da un learner è un quorum di voti in rete. -/
theorem chosen_of_quorum {n} {s : PaxosState n} (hE : invE s) {l : Fin n} {b : Ballot} {v : Value}
    (hq : isQuorum n (count ((s.learners l).accepts (b, v)))) : chosen s v := by
  refine ⟨b, ?_⟩
  unfold isQuorum at hq ⊢
  have := count_mono (S := (s.learners l).accepts (b, v))
    (T := fun a => decide (AMessage.accepted b v ∈ s.network.amsgs a))
    (fun a ha => by simpa using hE.accepts_vote l b v a ha)
  omega

theorem correctness_of_reachable {n} {s : PaxosState n} (h : Paxos.reachable s) : correctness s := by
  intro i j v w hi hj
  obtain ⟨hE, hS⟩ := inv_of_reachable h
  obtain ⟨b, hb⟩ := hE.decision_quorum i v hi
  obtain ⟨b', hb'⟩ := hE.decision_quorum j w hj
  exact agreement_of_inv hE hS v w (chosen_of_quorum hE hb) (chosen_of_quorum hE hb')

/-! ### Lemmi ponte verso `¬ Paxos.reachable s` -/

/-- Un acceptor manda al più una promessa per ballot. -/
theorem not_reachable_of_two_promises {n} {s : PaxosState n} {a : Fin n} {b : Ballot}
    {acc acc' : Option (Ballot × Value)}
    (h₁ : AMessage.promise b acc ∈ s.network.amsgs a) (h₂ : AMessage.promise b acc' ∈ s.network.amsgs a)
    (hne : acc ≠ acc') : ¬ Paxos.reachable s :=
  fun hr => hne ((inv_of_reachable hr).1.promise_unique a b acc acc' h₁ h₂)

/-- Per ogni ballot c'è al più un valore proposto (da un solo proposer). -/
theorem not_reachable_of_two_proposes {n} {s : PaxosState n} {i i' : Fin n} {b : Ballot} {v v' : Value}
    (h₁ : PMessage.propose b v ∈ s.network.pmsgs i) (h₂ : PMessage.propose b v' ∈ s.network.pmsgs i')
    (hne : v ≠ v') : ¬ Paxos.reachable s := by
  intro hr
  obtain ⟨hE, _⟩ := inv_of_reachable hr
  have e₁ := hE.propose_owner i b v h₁
  have e₂ := hE.propose_owner i' b v' h₂
  have hii : i = i' := Fin.ext (e₁.symm.trans e₂)
  subst hii
  exact hne (hE.propose_unique i b v v' h₁ h₂)

/-- Due voti nello stesso ballot hanno lo stesso valore. -/
theorem not_reachable_of_two_votes {n} {s : PaxosState n} {a a' : Fin n} {b : Ballot} {v v' : Value}
    (h₁ : AMessage.accepted b v ∈ s.network.amsgs a) (h₂ : AMessage.accepted b v' ∈ s.network.amsgs a')
    (hne : v ≠ v') : ¬ Paxos.reachable s := by
  intro hr
  obtain ⟨hE, _⟩ := inv_of_reachable hr
  obtain ⟨i, p₁⟩ := hE.vote_propose a b v h₁
  obtain ⟨i', p₂⟩ := hE.vote_propose a' b v' h₂
  exact not_reachable_of_two_proposes p₁ p₂ hne hr

/-- Due promesse che riportano voti nello stesso ballot riportano lo stesso valore. -/
theorem not_reachable_of_two_reports {n} {s : PaxosState n} {a a' : Fin n} {b₁ b₂ b : Ballot} {v v' : Value}
    (h₁ : AMessage.promise b₁ (some (b, v)) ∈ s.network.amsgs a)
    (h₂ : AMessage.promise b₂ (some (b, v')) ∈ s.network.amsgs a')
    (hne : v ≠ v') : ¬ Paxos.reachable s := by
  intro hr
  obtain ⟨hE, _⟩ := inv_of_reachable hr
  exact not_reachable_of_two_votes (hE.report_vote a b₁ b v h₁) (hE.report_vote a' b₂ b v' h₂) hne hr

/-- Un learner non raccoglie due quorum per valori diversi (è la sicurezza di Paxos). -/
theorem not_reachable_of_two_quorums {n} {s : PaxosState n} {l : Fin n} {b b' : Ballot} {v v' : Value}
    (h₁ : isQuorum n (count ((s.learners l).accepts (b, v))))
    (h₂ : isQuorum n (count ((s.learners l).accepts (b', v'))))
    (hne : v ≠ v') : ¬ Paxos.reachable s := by
  intro hr
  obtain ⟨hE, hS⟩ := inv_of_reachable hr
  exact hne (agreement_of_inv hE hS v v' (chosen_of_quorum hE h₁) (chosen_of_quorum hE h₂))

/-- Passare da `[j]? = some m` a `m ∈ l` (i lemmi ponte parlano di appartenenza). -/
theorem mem_of_get {α} {l : List α} {j : Nat} {m : α} (h : l[j]? = some m) : m ∈ l :=
  List.mem_of_getElem? h


/-! # Commutazione

Due passi applicati allo stesso stato `s`, una coppia per ognuna delle 36 combinazioni non
ordinate degli 8 eventi: i 7 interni (`prepare`, `collect_promise`, `accept`, `promise`, `vote`,
`collect_accepted`, `crash`) e il passo esterno `decide_rs`. Enunciato di base, come per `MSI`:
diamante, oppure `s' = s''`, oppure `¬ Paxos.reachable s`. Dove il diamante è falso l'enunciato
aggiunge il
percorso: il `collect_promise` è assorbito dal `prepare` dello stesso proposer (che azzera tutto);
`prepare` dopo `accept`, due promesse, promessa e voto, due voti dello stesso acceptor
riconvergono "a meno del messaggio stantio" nell'outbox (la rete non cancella mai, quindi
l'outbox ricorda entrambi gli ordini); `collect_promise` dopo `accept` è sempre possibile ma
può cambiare `maxAcc` dopo la proposta. Il `crash` di un nodo e un passo dello stesso nodo non
commutano mai (crash-stop): con indici distinti c'è il diamante. Le due regole
`collect_promise`/`collect_promise_update` condividono l'evento, quindi un solo teorema le copre. -/

/-! ## Proposer–proposer -/

theorem comm_prepare_prepare {n} {s s' s'' : PaxosState n} {i₁ i₂ : Fin n} {b₁ b₂ : Ballot} :
  paxos_step s (.proposer (.prepare b₁) i₁) s' →
  paxos_step s (.proposer (.prepare b₂) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i₁) s''' ∧
           paxos_step s' (.proposer (.prepare b₂) i₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, hb₂, rfl⟩ := prepare_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    have hb : b₁ = b₂ := hb₁.trans hb₂.symm
    subst hb
    exact Or.inr (Or.inl rfl)
  · refine Or.inl ⟨prepareSt (prepareSt s i₂ b₂) i₁ b₁, mk_prepare hc₁ ?_, ?_⟩
    · simp only [prepareSt, update_Fin_gso2 _ _ _ _ hne]; exact hb₁
    · refine paxos_step_congr (mk_prepare hc₂ ?_) ?_
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hb₂
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k <;> simp only
        · rw [update_Fin_comm _ _ _ _ _ hne]
        · rw [update_Fin_comm _ _ _ _ _ (Ne.symm hne)]

theorem comm_prepare_collect_promise {n} {s s' s'' : PaxosState n} {i₁ i₂ a : Fin n} {b₁ b₂ : Ballot}
    {acc : Option (Ballot × Value)} :
  paxos_step s (.proposer (.prepare b₁) i₁) s' →
  paxos_step s (.proposer (.collect_promise a b₂ acc) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i₁) s''' ∧
           paxos_step s' (.proposer (.collect_promise a b₂ acc) i₂) s''')
  ∨ paxos_step s'' (.proposer (.prepare b₁) i₁) s'
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, ⟨j, hj⟩, hb₂, ha₂, hcase⟩ := collect_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    refine Or.inr (Or.inl ?_)
    rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
    · refine paxos_step_congr (mk_prepare hc₁ ?_) ?_
      · simp only [collectSt, update_Fin_gss]; exact hb₁
      · simp only [prepareSt, collectSt, update_Fin_gss, update_Fin_update_Fin_same]
    · refine paxos_step_congr (mk_prepare hc₁ ?_) ?_
      · simp only [collectUpdSt, update_Fin_gss]; exact hb₁
      · simp only [prepareSt, collectUpdSt, update_Fin_gss, update_Fin_update_Fin_same]
  · rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
    · refine Or.inl ⟨prepareSt (collectSt s i₂ a) i₁ b₁, mk_prepare hc₁ ?_, ?_⟩
      · simp only [collectSt, update_Fin_gso2 _ _ _ _ hne]; exact hb₁
      · refine paxos_step_congr (mk_collect (j := j) hc₂ hj ?_ ?_ ?_) ?_
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hb₂
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact ha₂
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hlt
        · simp only [prepareSt, collectSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne),
            update_Fin_gso2 _ _ _ _ hne]
          refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k <;> simp only
          rw [update_Fin_comm _ _ _ _ _ hne]
    · refine Or.inl ⟨prepareSt (collectUpdSt s i₂ a acc) i₁ b₁, mk_prepare hc₁ ?_, ?_⟩
      · simp only [collectUpdSt, update_Fin_gso2 _ _ _ _ hne]; exact hb₁
      · refine paxos_step_congr (mk_collectUpd (j := j) hc₂ hj ?_ ?_ ?_) ?_
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hb₂
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact ha₂
        · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hgt
        · simp only [prepareSt, collectUpdSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne),
            update_Fin_gso2 _ _ _ _ hne]
          refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k <;> simp only
          rw [update_Fin_comm _ _ _ _ _ hne]

theorem comm_prepare_accept {n} {s s' s'' : PaxosState n} {i₁ i₂ : Fin n} {b₁ b₂ : Ballot} {v : Value} :
  paxos_step s (.proposer (.prepare b₁) i₁) s' →
  paxos_step s (.proposer (.accept b₂ v) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i₁) s''' ∧
           paxos_step s' (.proposer (.accept b₂ v) i₂) s''')
  ∨ (∃ t, paxos_step s'' (.proposer (.prepare b₁) i₁) t ∧
       t = { s' with network := { s'.network with
               pmsgs := update_Fin i₁ (s.network.pmsgs i₁ ++ [PMessage.propose b₂ v, PMessage.prepare b₁])
                                   s.network.pmsgs } })
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, hb₂, hp₂, hq₂, hv₂, rfl⟩ := accept_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    refine Or.inr (Or.inl ⟨prepareSt (acceptSt s i₁ b₂ v) i₁ b₁, mk_prepare hc₁ ?_, ?_⟩)
    · simp only [acceptSt, update_Fin_gss]; exact hb₁
    · simp only [prepareSt, acceptSt, update_Fin_gss, update_Fin_update_Fin_same, List.append_assoc,
        List.cons_append, List.nil_append]
  · refine Or.inl ⟨prepareSt (acceptSt s i₂ b₂ v) i₁ b₁, mk_prepare hc₁ ?_, ?_⟩
    · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne]; exact hb₁
    · refine paxos_step_congr (mk_accept hc₂ ?_ ?_ ?_ ?_) ?_
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hb₂
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hp₂
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hq₂
      · simp only [prepareSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hv₂
      · simp only [prepareSt, acceptSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k <;> simp only
        · rw [update_Fin_comm _ _ _ _ _ hne]
        · rw [update_Fin_comm _ _ _ _ _ (Ne.symm hne)]

/-- Il `maxAcc` del proposer dopo un `collect_promise` (una qualunque delle due regole). -/
def collectMax : Option (Ballot × Value) → Option (Ballot × Value) → Option (Ballot × Value)
  | none, cur => cur
  | some x, none => some x
  | some (b, v), some (b₀, w) => if b₀ < b then some (b, v) else some (b₀, w)

theorem collectMax_of_not_gt {acc cur : Option (Ballot × Value)} (h : ¬ acc_gt acc cur) :
    collectMax acc cur = cur := by
  rcases acc with _ | ⟨b, v⟩ <;> rcases cur with _ | ⟨b₀, w⟩ <;> simp [acc_gt, collectMax] at *
  intro h'; exact absurd (Nat.lt_of_lt_of_le h' h) (Nat.lt_irrefl _)

theorem collectMax_of_gt {acc cur : Option (Ballot × Value)} (h : acc_gt acc cur) :
    collectMax acc cur = acc := by
  rcases acc with _ | ⟨b, v⟩ <;> rcases cur with _ | ⟨b₀, w⟩ <;> simp [acc_gt, collectMax] at *
  intro h'; exact absurd (Nat.lt_of_lt_of_le h h') (Nat.lt_irrefl _)

set_option linter.unusedSimpArgs false in
/-- Due `collect_promise` commutano sul `maxAcc`, salvo due voti riportati nello stesso ballot
con valori diversi. -/
theorem collectMax_comm (acc₁ acc₂ m : Option (Ballot × Value)) :
    collectMax acc₁ (collectMax acc₂ m) = collectMax acc₂ (collectMax acc₁ m)
    ∨ ∃ c v₁ v₂, acc₁ = some (c, v₁) ∧ acc₂ = some (c, v₂) ∧ v₁ ≠ v₂ := by
  rcases acc₁ with _ | ⟨c₁, v₁⟩
  · left; rfl
  rcases acc₂ with _ | ⟨c₂, v₂⟩
  · left; rfl
  by_cases hc : c₁ = c₂
  · subst hc
    by_cases hv : v₁ = v₂
    · subst hv; left; rfl
    · exact Or.inr ⟨c₁, v₁, v₂, rfl, rfl, hv⟩
  · left
    rcases m with _ | ⟨c₀, w⟩ <;> simp only [collectMax] <;> split_ifs <;> (try simp only [collectMax])
      <;> (try split_ifs) <;> first | rfl | (exfalso; simp only [Ballot] at *; omega)

/-- Stato di arrivo di un `collect_promise` con una qualunque delle due regole. -/
def collectAnySt {n} (s : PaxosState n) (i a : Fin n) (acc : Option (Ballot × Value)) : PaxosState n :=
  { s with proposers := update_Fin i { s.proposers i with
                          promises := update_Fin a true (s.proposers i).promises,
                          maxAcc := collectMax acc (s.proposers i).maxAcc } s.proposers }

theorem mk_collectAny {n} {s : PaxosState n} {i a : Fin n} {b : Ballot} {acc : Option (Ballot × Value)}
    {j : Nat} (hc : s.crashed i = false)
    (hj : (s.network.amsgs a)[j]? = some (AMessage.promise b acc))
    (hb : (s.proposers i).ballot = some b) (ha : (s.proposers i).promises a = false) :
    paxos_step s (.proposer (.collect_promise a b acc) i) (collectAnySt s i a acc) := by
  by_cases hgt : acc_gt acc (s.proposers i).maxAcc
  · refine paxos_step_congr (mk_collectUpd (j := j) hc hj hb ha hgt) ?_
    simp only [collectUpdSt, collectAnySt, collectMax_of_gt hgt]
  · refine paxos_step_congr (mk_collect (j := j) hc hj hb ha hgt) ?_
    simp only [collectSt, collectAnySt, collectMax_of_not_gt hgt]

theorem collectAny_inv {n} {s s' : PaxosState n} {i a : Fin n} {b : Ballot} {acc : Option (Ballot × Value)}
    (h : paxos_step s (.proposer (.collect_promise a b acc) i) s') :
    s.crashed i = false ∧ (∃ j : Nat, (s.network.amsgs a)[j]? = some (AMessage.promise b acc))
      ∧ (s.proposers i).ballot = some b ∧ (s.proposers i).promises a = false
      ∧ s' = collectAnySt s i a acc := by
  obtain ⟨hc, hj, hb, ha, hbr⟩ := collect_inv h
  refine ⟨hc, hj, hb, ha, ?_⟩
  rcases hbr with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
  · simp only [collectSt, collectAnySt, collectMax_of_not_gt hlt]
  · simp only [collectUpdSt, collectAnySt, collectMax_of_gt hgt]

theorem comm_collect_promise_collect_promise {n} {s s' s'' : PaxosState n} {i₁ i₂ a₁ a₂ : Fin n}
    {b₁ b₂ : Ballot} {acc₁ acc₂ : Option (Ballot × Value)} :
  paxos_step s (.proposer (.collect_promise a₁ b₁ acc₁) i₁) s' →
  paxos_step s (.proposer (.collect_promise a₂ b₂ acc₂) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a₁ b₁ acc₁) i₁) s''' ∧
           paxos_step s' (.proposer (.collect_promise a₂ b₂ acc₂) i₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j₁, hj₁⟩, hb₁, ha₁, rfl⟩ := collectAny_inv h₁
  obtain ⟨hc₂, ⟨j₂, hj₂⟩, hb₂, ha₂, rfl⟩ := collectAny_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    have hbb : b₁ = b₂ := Option.some.inj (hb₁.symm.trans hb₂)
    subst hbb
    by_cases hae : a₁ = a₂
    · subst hae
      by_cases hacc : acc₁ = acc₂
      · subst hacc; exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (not_reachable_of_two_promises (mem_of_get hj₁) (mem_of_get hj₂) hacc))
    · rcases collectMax_comm acc₁ acc₂ (s.proposers i₁).maxAcc with hcm | ⟨c, v₁, v₂, rfl, rfl, hv⟩
      · refine Or.inl ⟨collectAnySt (collectAnySt s i₁ a₂ acc₂) i₁ a₁ acc₁,
          mk_collectAny (j := j₁) hc₁ hj₁ ?_ ?_, ?_⟩
        · simp only [collectAnySt, update_Fin_gss]; exact hb₁
        · simp only [collectAnySt, update_Fin_gss, update_Fin_gso2 _ _ _ _ hae]; exact ha₁
        · refine paxos_step_congr (mk_collectAny (j := j₂) hc₂ hj₂ ?_ ?_) ?_
          · simp only [collectAnySt, update_Fin_gss]; exact hb₂
          · simp only [collectAnySt, update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hae)]; exact ha₂
          · simp only [collectAnySt, update_Fin_gss, update_Fin_update_Fin_same,
              update_Fin_comm _ a₁ a₂ _ _ hae, hcm]
      · exact Or.inr (Or.inr (not_reachable_of_two_reports (mem_of_get hj₁) (mem_of_get hj₂) hv))
  · refine Or.inl ⟨collectAnySt (collectAnySt s i₂ a₂ acc₂) i₁ a₁ acc₁,
      mk_collectAny (j := j₁) hc₁ hj₁ ?_ ?_, ?_⟩
    · simp only [collectAnySt, update_Fin_gso2 _ _ _ _ hne]; exact hb₁
    · simp only [collectAnySt, update_Fin_gso2 _ _ _ _ hne]; exact ha₁
    · refine paxos_step_congr (mk_collectAny (j := j₂) hc₂ hj₂ ?_ ?_) ?_
      · simp only [collectAnySt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hb₂
      · simp only [collectAnySt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact ha₂
      · simp only [collectAnySt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne),
          update_Fin_comm _ i₁ i₂ _ _ hne]

theorem comm_collect_promise_accept {n} {s s' s'' : PaxosState n} {i₁ i₂ a : Fin n} {b₁ b₂ : Ballot}
    {acc : Option (Ballot × Value)} {v : Value} :
  paxos_step s (.proposer (.collect_promise a b₁ acc) i₁) s' →
  paxos_step s (.proposer (.accept b₂ v) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a b₁ acc) i₁) s''' ∧
           paxos_step s' (.proposer (.accept b₂ v) i₂) s''')
  ∨ (∃ t, paxos_step s'' (.proposer (.collect_promise a b₁ acc) i₁) t ∧
       t = { s' with proposers := update_Fin i₁ { s'.proposers i₁ with proposed := some v } s'.proposers,
                     network := { s'.network with
                       pmsgs := update_Fin i₁ (s.network.pmsgs i₁ ++ [PMessage.propose b₂ v]) s.network.pmsgs } })
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, hb₁, ha₁, hcase⟩ := collect_inv h₁
  obtain ⟨hc₂, hb₂, hp₂, hq₂, hv₂, rfl⟩ := accept_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
    · refine Or.inr (Or.inl ⟨collectSt (acceptSt s i₁ b₂ v) i₁ a, ?_, ?_⟩)
      · refine mk_collect (j := j) hc₁ hj ?_ ?_ ?_ <;> simp only [acceptSt, update_Fin_gss] <;> assumption
      · simp only [collectSt, acceptSt, update_Fin_gss, update_Fin_update_Fin_same]
    · refine Or.inr (Or.inl ⟨collectUpdSt (acceptSt s i₁ b₂ v) i₁ a acc, ?_, ?_⟩)
      · refine mk_collectUpd (j := j) hc₁ hj ?_ ?_ ?_ <;> simp only [acceptSt, update_Fin_gss] <;> assumption
      · simp only [collectUpdSt, acceptSt, update_Fin_gss, update_Fin_update_Fin_same]
  · have hne' : ¬ i₂ = i₁ := fun h => hne h.symm
    rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
    · refine Or.inl ⟨collectSt (acceptSt s i₂ b₂ v) i₁ a, ?_, ?_⟩
      · refine mk_collect (j := j) hc₁ hj ?_ ?_ ?_ <;> simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne] <;> assumption
      · refine paxos_step_congr (mk_accept hc₂ ?_ ?_ ?_ ?_) ?_
        · simp only [collectSt, update_Fin_gso2 _ _ _ _ hne']; exact hb₂
        · simp only [collectSt, update_Fin_gso2 _ _ _ _ hne']; exact hp₂
        · simp only [collectSt, update_Fin_gso2 _ _ _ _ hne']; exact hq₂
        · simp only [collectSt, update_Fin_gso2 _ _ _ _ hne']; exact hv₂
        · simp only [collectSt, acceptSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
          refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k
          · simp only
            rw [update_Fin_comm _ _ _ _ _ hne']
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
    · refine Or.inl ⟨collectUpdSt (acceptSt s i₂ b₂ v) i₁ a acc, ?_, ?_⟩
      · refine mk_collectUpd (j := j) hc₁ hj ?_ ?_ ?_ <;> simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne] <;> assumption
      · refine paxos_step_congr (mk_accept hc₂ ?_ ?_ ?_ ?_) ?_
        · simp only [collectUpdSt, update_Fin_gso2 _ _ _ _ hne']; exact hb₂
        · simp only [collectUpdSt, update_Fin_gso2 _ _ _ _ hne']; exact hp₂
        · simp only [collectUpdSt, update_Fin_gso2 _ _ _ _ hne']; exact hq₂
        · simp only [collectUpdSt, update_Fin_gso2 _ _ _ _ hne']; exact hv₂
        · simp only [collectUpdSt, acceptSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
          refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k
          · simp only
            rw [update_Fin_comm _ _ _ _ _ hne']
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl

theorem comm_accept_accept {n} {s s' s'' : PaxosState n} {i₁ i₂ : Fin n} {b₁ b₂ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.proposer (.accept b₁ v₁) i₁) s' →
  paxos_step s (.proposer (.accept b₂ v₂) i₂) s'' →
  (∃ s''', paxos_step s'' (.proposer (.accept b₁ v₁) i₁) s''' ∧
           paxos_step s' (.proposer (.accept b₂ v₂) i₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, hp₁, hq₁, hv₁, rfl⟩ := accept_inv h₁
  obtain ⟨hc₂, hb₂, hp₂, hq₂, hv₂, rfl⟩ := accept_inv h₂
  by_cases hne : i₁ = i₂
  · subst hne
    have hb : b₁ = b₂ := Option.some.inj (hb₁.symm.trans hb₂)
    subst hb
    have hv : v₁ = v₂ := Option.some.inj (hv₁.symm.trans hv₂)
    subst hv
    exact Or.inr (Or.inl rfl)
  · refine Or.inl ⟨acceptSt (acceptSt s i₂ b₂ v₂) i₁ b₁ v₁, ?_, ?_⟩
    · refine mk_accept hc₁ ?_ ?_ ?_ ?_ <;> simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne] <;> assumption
    · have hne' : ¬ i₂ = i₁ := fun h => hne h.symm
      refine paxos_step_congr (mk_accept hc₂ ?_ ?_ ?_ ?_) ?_
      · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne']; exact hb₂
      · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne']; exact hp₂
      · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne']; exact hq₂
      · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne']; exact hv₂
      · simp only [acceptSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ hne']
        refine PaxosState.ext_all ?_ ?_ ?_ ?_ ?_ ?_ <;> intro k
        · simp only
          rw [update_Fin_comm _ _ _ _ _ hne']
        · rfl
        · rfl
        · simp only
          rw [update_Fin_comm _ _ _ _ _ hne']
        · rfl
        · rfl

/-! ## Acceptor–acceptor -/

theorem comm_promise_promise {n} {s s' s'' : PaxosState n} {a₁ a₂ : Fin n} {b₁ b₂ : Ballot} :
  paxos_step s (.acceptor (.promise b₁) a₁) s' →
  paxos_step s (.acceptor (.promise b₂) a₂) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.promise b₁) a₁) s''' ∧
           paxos_step s' (.acceptor (.promise b₂) a₂) s''')
  ∨ (a₁ = a₂ ∧ b₁ < b₂ ∧ ∃ t, paxos_step s' (.acceptor (.promise b₂) a₂) t ∧
       t = { s'' with network := { s''.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.promise b₁ (s.acceptors a₁).maxAcc,
                                                              AMessage.promise b₂ (s.acceptors a₁).maxAcc])
                                   s.network.amsgs } })
  ∨ (a₁ = a₂ ∧ b₂ < b₁ ∧ ∃ t, paxos_step s'' (.acceptor (.promise b₁) a₁) t ∧
       t = { s' with network := { s'.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.promise b₂ (s.acceptors a₁).maxAcc,
                                                              AMessage.promise b₁ (s.acceptors a₁).maxAcc])
                                   s.network.amsgs } })
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i₁, j₁, hj₁⟩, hbal₁, rfl⟩ := promise_inv h₁
  obtain ⟨hc₂, ⟨i₂, j₂, hj₂⟩, hbal₂, rfl⟩ := promise_inv h₂
  by_cases hne : a₁ = a₂
  · subst hne
    rcases Nat.lt_trichotomy b₁ b₂ with hlt | heq | hgt
    · refine Or.inr (Or.inl ⟨rfl, hlt, promiseSt (promiseSt s a₁ b₁) a₁ b₂, ?_, ?_⟩)
      · exact mk_promise (i := i₂) (j := j₂) hc₂ hj₂ (by simp [promiseSt, bal_gt, hlt])
      · simp [promiseSt, update_Fin_update_Fin_same]
    · subst heq
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, hgt, promiseSt (promiseSt s a₁ b₂) a₁ b₁, ?_, ?_⟩))
      · exact mk_promise (i := i₁) (j := j₁) hc₁ hj₁ (by simp [promiseSt, bal_gt, hgt])
      · simp [promiseSt, update_Fin_update_Fin_same]
  · refine Or.inl ⟨promiseSt (promiseSt s a₂ b₂) a₁ b₁, ?_, ?_⟩
    · exact mk_promise (i := i₁) (j := j₁) hc₁ hj₁
        (by simp only [promiseSt, update_Fin_gso2 _ _ _ _ hne]; exact hbal₁)
    · refine paxos_step_congr (mk_promise (i := i₂) (j := j₂) hc₂ hj₂ ?_) ?_
      · simp only [promiseSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hbal₂
      · simp only [promiseSt]
        refine PaxosState.ext_all (fun _ => rfl) ?_ (fun _ => rfl) (fun _ => rfl) ?_ (fun _ => rfl)
        · intro k
          by_cases hk₁ : k = a₁
          · subst hk₁; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hk₂ : k = a₂
            · subst hk₂; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
            · simp [update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
        · intro k
          by_cases hk₁ : k = a₁
          · subst hk₁; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hk₂ : k = a₂
            · subst hk₂; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
            · simp [update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]

theorem comm_promise_vote {n} {s s' s'' : PaxosState n} {a₁ a₂ : Fin n} {b₁ b₂ : Ballot} {v : Value} :
  paxos_step s (.acceptor (.promise b₁) a₁) s' →
  paxos_step s (.acceptor (.vote b₂ v) a₂) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.promise b₁) a₁) s''' ∧
           paxos_step s' (.acceptor (.vote b₂ v) a₂) s''')
  ∨ (a₁ = a₂ ∧ b₁ ≤ b₂ ∧ ∃ t, paxos_step s' (.acceptor (.vote b₂ v) a₂) t ∧
       t = { s'' with network := { s''.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.promise b₁ (s.acceptors a₁).maxAcc,
                                                              AMessage.accepted b₂ v])
                                   s.network.amsgs } })
  ∨ (a₁ = a₂ ∧ b₂ < b₁ ∧ ∃ t, paxos_step s'' (.acceptor (.promise b₁) a₁) t ∧
       t = { s' with acceptors := update_Fin a₁ { s'.acceptors a₁ with maxAcc := some (b₂, v) } s'.acceptors,
                     network := { s'.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.accepted b₂ v,
                                                              AMessage.promise b₁ (some (b₂, v))])
                                   s.network.amsgs } })
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i₁, j₁, hj₁⟩, hbal₁, rfl⟩ := promise_inv h₁
  obtain ⟨hc₂, ⟨i₂, j₂, hj₂⟩, hbal₂, rfl⟩ := vote_inv h₂
  by_cases hne : a₁ = a₂
  · subst hne
    rcases Nat.lt_or_ge b₂ b₁ with hgt | hle
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, hgt, promiseSt (voteSt s a₁ b₂ v) a₁ b₁, ?_, ?_⟩))
      · exact mk_promise (i := i₁) (j := j₁) hc₁ hj₁ (by simp [voteSt, bal_gt, hgt])
      · simp [promiseSt, voteSt, update_Fin_update_Fin_same]
    · refine Or.inr (Or.inl ⟨rfl, hle, voteSt (promiseSt s a₁ b₁) a₁ b₂ v, ?_, ?_⟩)
      · exact mk_vote (i := i₂) (j := j₂) hc₂ hj₂ (by simp [promiseSt, bal_ge, hle])
      · simp [promiseSt, voteSt, update_Fin_update_Fin_same]
  · refine Or.inl ⟨promiseSt (voteSt s a₂ b₂ v) a₁ b₁, ?_, ?_⟩
    · exact mk_promise (i := i₁) (j := j₁) hc₁ hj₁
        (by simp only [voteSt, update_Fin_gso2 _ _ _ _ hne]; exact hbal₁)
    · refine paxos_step_congr (mk_vote (i := i₂) (j := j₂) hc₂ hj₂ ?_) ?_
      · simp only [promiseSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]; exact hbal₂
      · simp only [promiseSt, voteSt]
        refine PaxosState.ext_all (fun _ => rfl) ?_ (fun _ => rfl) (fun _ => rfl) ?_ (fun _ => rfl)
        · intro k
          by_cases hk₁ : k = a₁
          · subst hk₁; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hk₂ : k = a₂
            · subst hk₂; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
            · simp [update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]
        · intro k
          by_cases hk₁ : k = a₁
          · subst hk₁; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ hne]
          · by_cases hk₂ : k = a₂
            · subst hk₂; simp [update_Fin_gss, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
            · simp [update_Fin_gso2 _ _ _ _ hk₁, update_Fin_gso2 _ _ _ _ hk₂]

theorem comm_vote_vote {n} {s s' s'' : PaxosState n} {a₁ a₂ : Fin n} {b₁ b₂ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.acceptor (.vote b₁ v₁) a₁) s' →
  paxos_step s (.acceptor (.vote b₂ v₂) a₂) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.vote b₁ v₁) a₁) s''' ∧
           paxos_step s' (.acceptor (.vote b₂ v₂) a₂) s''')
  ∨ (a₁ = a₂ ∧ b₁ < b₂ ∧ ∃ t, paxos_step s' (.acceptor (.vote b₂ v₂) a₂) t ∧
       t = { s'' with network := { s''.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.accepted b₁ v₁, AMessage.accepted b₂ v₂])
                                   s.network.amsgs } })
  ∨ (a₁ = a₂ ∧ b₂ < b₁ ∧ ∃ t, paxos_step s'' (.acceptor (.vote b₁ v₁) a₁) t ∧
       t = { s' with network := { s'.network with
               amsgs := update_Fin a₁ (s.network.amsgs a₁ ++ [AMessage.accepted b₂ v₂, AMessage.accepted b₁ v₁])
                                   s.network.amsgs } })
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i₁, j₁, hj₁⟩, hb₁, rfl⟩ := vote_inv h₁
  obtain ⟨hc₂, ⟨i₂, j₂, hj₂⟩, hb₂, rfl⟩ := vote_inv h₂
  by_cases hne : a₁ = a₂
  · subst hne
    rcases Nat.lt_trichotomy b₁ b₂ with hlt | heq | hgt
    · -- b₁ < b₂ : secondo disgiunto
      refine Or.inr (Or.inl ⟨rfl, hlt, voteSt (voteSt s a₁ b₁ v₁) a₁ b₂ v₂, ?_, ?_⟩)
      · refine mk_vote (i := i₂) (j := j₂) hc₂ hj₂ ?_
        simp only [voteSt, update_Fin_gss, bal_ge]
        exact Nat.le_of_lt hlt
      · simp only [voteSt, update_Fin_gss, update_Fin_update_Fin_same, List.append_assoc,
          List.cons_append, List.nil_append]
    · -- b₁ = b₂
      subst heq
      by_cases hv : v₁ = v₂
      · subst hv
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (not_reachable_of_two_proposes (mem_of_get hj₁) (mem_of_get hj₂) hv))))
    · -- b₂ < b₁ : terzo disgiunto
      refine Or.inr (Or.inr (Or.inl ⟨rfl, hgt, voteSt (voteSt s a₁ b₂ v₂) a₁ b₁ v₁, ?_, ?_⟩))
      · refine mk_vote (i := i₁) (j := j₁) hc₁ hj₁ ?_
        simp only [voteSt, update_Fin_gss, bal_ge]
        exact Nat.le_of_lt hgt
      · simp only [voteSt, update_Fin_gss, update_Fin_update_Fin_same, List.append_assoc,
          List.cons_append, List.nil_append]
  · -- acceptor distinti: diamante
    refine Or.inl ⟨voteSt (voteSt s a₂ b₂ v₂) a₁ b₁ v₁, ?_, ?_⟩
    · refine mk_vote (i := i₁) (j := j₁) hc₁ hj₁ ?_
      simp only [voteSt, update_Fin_gso2 _ _ _ _ hne]
      exact hb₁
    · refine paxos_step_congr (mk_vote (i := i₂) (j := j₂) hc₂ hj₂ ?_) ?_
      · simp only [voteSt, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        exact hb₂
      · simp only [voteSt, update_Fin_gso2 _ _ _ _ hne, update_Fin_gso2 _ _ _ _ (Ne.symm hne)]
        rw [update_Fin_comm _ _ _ _ _ (Ne.symm hne), update_Fin_comm _ _ _ _ _ (Ne.symm hne)]

/-! ## Learner–learner -/

theorem comm_collect_accepted_collect_accepted {n} {s s' s'' : PaxosState n} {l₁ l₂ a₁ a₂ : Fin n}
    {b₁ b₂ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.learner (.collect_accepted a₁ b₁ v₁) l₁) s' →
  paxos_step s (.learner (.collect_accepted a₂ b₂ v₂) l₂) s'' →
  (∃ s''', paxos_step s'' (.learner (.collect_accepted a₁ b₁ v₁) l₁) s''' ∧
           paxos_step s' (.learner (.collect_accepted a₂ b₂ v₂) l₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j₁, hj₁⟩, ha₁, rfl⟩ := lcollect_inv h₁
  obtain ⟨hc₂, ⟨j₂, hj₂⟩, ha₂, rfl⟩ := lcollect_inv h₂
  by_cases hl : l₁ = l₂
  · subst hl
    by_cases hk : (b₁, v₁) = (b₂, v₂)
    · -- stessa chiave `(b, v)`
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      by_cases haa : a₁ = a₂
      · subst haa; exact Or.inr (Or.inl rfl)
      · refine Or.inl ⟨lcollectSt (lcollectSt s l₁ a₂ b₁ v₁) l₁ a₁ b₁ v₁,
          mk_lcollect (j := j₁) hc₁ hj₁ ?_, ?_⟩
        · simp only [lcollectSt, update_Fin_gss, update_Key_gss, update_Fin_gso2 _ _ _ _ haa]
          exact ha₁
        · refine paxos_step_congr (mk_lcollect (j := j₂) hc₂ hj₂ ?_) ?_
          · simp only [lcollectSt, update_Fin_gss, update_Key_gss,
              update_Fin_gso2 _ _ _ _ (Ne.symm haa)]
            exact ha₂
          · simp only [lcollectSt, update_Fin_gss, update_Key_gss, update_Fin_update_Fin_same,
              update_Key_update_Key_same]
            rw [update_Fin_comm _ a₁ a₂ _ _ haa]
    · -- chiavi diverse
      refine Or.inl ⟨lcollectSt (lcollectSt s l₁ a₂ b₂ v₂) l₁ a₁ b₁ v₁,
        mk_lcollect (j := j₁) hc₁ hj₁ ?_, ?_⟩
      · simp only [lcollectSt, update_Fin_gss, update_Key_gso2 _ _ _ _ hk]
        exact ha₁
      · refine paxos_step_congr (mk_lcollect (j := j₂) hc₂ hj₂ ?_) ?_
        · simp only [lcollectSt, update_Fin_gss, update_Key_gso2 _ _ _ _ (Ne.symm hk)]
          exact ha₂
        · simp only [lcollectSt, update_Fin_gss, update_Fin_update_Fin_same,
            update_Key_gso2 _ _ _ _ hk, update_Key_gso2 _ _ _ _ (Ne.symm hk)]
          rw [update_Key_comm _ _ _ _ _ hk]
  · -- learner diversi
    refine Or.inl ⟨lcollectSt (lcollectSt s l₂ a₂ b₂ v₂) l₁ a₁ b₁ v₁,
      mk_lcollect (j := j₁) hc₁ hj₁ ?_, ?_⟩
    · simp only [lcollectSt, update_Fin_gso2 _ _ _ _ hl]
      exact ha₁
    · refine paxos_step_congr (mk_lcollect (j := j₂) hc₂ hj₂ ?_) ?_
      · simp only [lcollectSt, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        exact ha₂
      · simp only [lcollectSt, update_Fin_gso2 _ _ _ _ hl, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        rw [update_Fin_comm _ _ _ _ _ hl]

theorem comm_collect_accepted_decide_rs {n} {s s' s'' : PaxosState n} {l₁ l₂ a : Fin n}
    {b₁ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.learner (.collect_accepted a b₁ v₁) l₁) s' →
  paxos_step_external s (.part (.decide_rs v₂) l₂) s'' →
  (∃ s''', paxos_step s'' (.learner (.collect_accepted a b₁ v₁) l₁) s''' ∧
           paxos_step_external s' (.part (.decide_rs v₂) l₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, ha₁, rfl⟩ := lcollect_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b₂, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  by_cases hl : l₁ = l₂
  · subst hl
    refine Or.inl ⟨lcollectSt (decideSt s l₁ v₂) l₁ a b₁ v₁, mk_lcollect (j := j) hc₁ hj ?_, ?_⟩
    · simp only [decideSt, update_Fin_gss]
      exact ha₁
    · refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ ?_ ?_) ?_
      · simp only [lcollectSt, update_Fin_gss]
        exact hd₂
      · -- il quorum sopravvive all'aggiunta di un voto
        simp only [lcollectSt, update_Fin_gss]
        by_cases hk : (b₂, v₂) = (b₁, v₁)
        · rw [hk, update_Key_gss]
          rw [hk] at hq₂
          unfold isQuorum at hq₂ ⊢
          have := count_le_update ((s.learners l₁).accepts (b₁, v₁)) a
          omega
        · rw [update_Key_gso2 _ _ _ _ hk]
          exact hq₂
      · simp only [lcollectSt, decideSt, update_Fin_gss, update_Fin_update_Fin_same]
  · refine Or.inl ⟨lcollectSt (decideSt s l₂ v₂) l₁ a b₁ v₁, mk_lcollect (j := j) hc₁ hj ?_, ?_⟩
    · simp only [decideSt, update_Fin_gso2 _ _ _ _ hl]
      exact ha₁
    · refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ ?_ ?_) ?_
      · simp only [lcollectSt, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        exact hd₂
      · simp only [lcollectSt, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        exact hq₂
      · simp only [lcollectSt, decideSt, update_Fin_gso2 _ _ _ _ hl,
          update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        rw [update_Fin_comm _ _ _ _ _ hl]

theorem comm_decide_rs_decide_rs {n} {s s' s'' : PaxosState n} {l₁ l₂ : Fin n} {v₁ v₂ : Value} :
  paxos_step_external s (.part (.decide_rs v₁) l₁) s' →
  paxos_step_external s (.part (.decide_rs v₂) l₂) s'' →
  (∃ s''', paxos_step_external s'' (.part (.decide_rs v₁) l₁) s''' ∧
           paxos_step_external s' (.part (.decide_rs v₂) l₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hd₁, ⟨b₁, hq₁⟩, rfl⟩ := decide_rs_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b₂, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  by_cases hl : l₁ = l₂
  · subst hl
    by_cases hv : v₁ = v₂
    · subst hv
      exact Or.inr (Or.inl rfl)
    · -- due quorum per valori diversi: stato non raggiungibile
      exact Or.inr (Or.inr (not_reachable_of_two_quorums hq₁ hq₂ hv))
  · refine Or.inl ⟨decideSt (decideSt s l₂ v₂) l₁ v₁, mk_decide_rs (b := b₁) hc₁ ?_ ?_, ?_⟩
    · simp only [decideSt, update_Fin_gso2 _ _ _ _ hl]
      exact hd₁
    · simp only [decideSt, update_Fin_gso2 _ _ _ _ hl]
      exact hq₁
    · refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ ?_ ?_) ?_
      · simp only [decideSt, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        exact hd₂
      · simp only [decideSt, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        exact hq₂
      · simp only [decideSt, update_Fin_gso2 _ _ _ _ hl, update_Fin_gso2 _ _ _ _ (Ne.symm hl)]
        rw [update_Fin_comm _ _ _ _ _ hl]

/-! ## Proposer–acceptor -/

/-- **Template** (diamante puro): i due passi toccano campi diversi (`proposers`/`pmsgs` contro
`acceptors`/`amsgs`); il `prepare b₂` letto dall'acceptor resta al suo posto dopo l'append del
proposer (`lst_get_append`) e gli stati finali coincidono per `simp`. -/
theorem comm_prepare_promise {n} {s s' s'' : PaxosState n} {i a : Fin n} {b₁ b₂ : Ballot} :
  paxos_step s (.proposer (.prepare b₁) i) s' →
  paxos_step s (.acceptor (.promise b₂) a) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i) s''' ∧
           paxos_step s' (.acceptor (.promise b₂) a) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := promise_inv h₂
  refine Or.inl ⟨prepareSt (promiseSt s a b₂) i b₁, mk_prepare hc₁ hb₁, ?_⟩
  refine paxos_step_congr (mk_promise (i := i') (j := j) hc₂ ?_ hbal) ?_
  · -- il `prepare b₂` è ancora in `pmsgs i'` dopo l'append del proposer `i`
    simp only [prepareSt]
    by_cases hii : i' = i
    · subst hii; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ hii]; exact hj
  · -- gli stati finali coincidono
    simp only [prepareSt, promiseSt]

theorem comm_prepare_vote {n} {s s' s'' : PaxosState n} {i a : Fin n} {b₁ b₂ : Ballot} {v : Value} :
  paxos_step s (.proposer (.prepare b₁) i) s' →
  paxos_step s (.acceptor (.vote b₂ v) a) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i) s''' ∧
           paxos_step s' (.acceptor (.vote b₂ v) a) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := vote_inv h₂
  refine Or.inl ⟨prepareSt (voteSt s a b₂ v) i b₁, mk_prepare hc₁ hb₁, ?_⟩
  refine paxos_step_congr (mk_vote (i := i') (j := j) hc₂ ?_ hbal) ?_
  · -- il `propose b₂ v` è ancora in `pmsgs i'` dopo l'append del proposer `i`
    simp only [prepareSt]
    by_cases hii : i' = i
    · subst hii; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ hii]; exact hj
  · -- gli stati finali coincidono
    simp only [prepareSt, voteSt]

theorem comm_collect_promise_promise {n} {s s' s'' : PaxosState n} {i a a' : Fin n} {b₁ b₂ : Ballot}
    {acc : Option (Ballot × Value)} :
  paxos_step s (.proposer (.collect_promise a b₁ acc) i) s' →
  paxos_step s (.acceptor (.promise b₂) a') s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a b₁ acc) i) s''' ∧
           paxos_step s' (.acceptor (.promise b₂) a') s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, hb, ha, hcase⟩ := collect_inv h₁
  obtain ⟨hc₂, ⟨i', j', hj'⟩, hbal, rfl⟩ := promise_inv h₂
  -- il `promise b₁ acc` è ancora in `amsgs a` dopo l'append dell'acceptor `a'`
  have hj₂ : ((promiseSt s a' b₂).network.amsgs a)[j]? = some (AMessage.promise b₁ acc) := by
    simp only [promiseSt]
    by_cases haa : a = a'
    · subst haa; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ haa]; exact hj
  rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
  · -- ramo `collect_promise`
    refine Or.inl ⟨collectSt (promiseSt s a' b₂) i a, mk_collect (j := j) hc₁ hj₂ hb ha hlt, ?_⟩
    refine paxos_step_congr (mk_promise (i := i') (j := j') hc₂ hj' hbal) ?_
    simp only [collectSt, promiseSt]
  · -- ramo `collect_promise_update`
    refine Or.inl ⟨collectUpdSt (promiseSt s a' b₂) i a acc, mk_collectUpd (j := j) hc₁ hj₂ hb ha hgt, ?_⟩
    refine paxos_step_congr (mk_promise (i := i') (j := j') hc₂ hj' hbal) ?_
    simp only [collectUpdSt, promiseSt]

theorem comm_collect_promise_vote {n} {s s' s'' : PaxosState n} {i a a' : Fin n} {b₁ b₂ : Ballot}
    {acc : Option (Ballot × Value)} {v : Value} :
  paxos_step s (.proposer (.collect_promise a b₁ acc) i) s' →
  paxos_step s (.acceptor (.vote b₂ v) a') s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a b₁ acc) i) s''' ∧
           paxos_step s' (.acceptor (.vote b₂ v) a') s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, hb, ha, hcase⟩ := collect_inv h₁
  obtain ⟨hc₂, ⟨i', j', hj'⟩, hbal, rfl⟩ := vote_inv h₂
  -- il `promise b₁ acc` è ancora in `amsgs a` dopo l'append dell'acceptor `a'`
  have hj₂ : ((voteSt s a' b₂ v).network.amsgs a)[j]? = some (AMessage.promise b₁ acc) := by
    simp only [voteSt]
    by_cases haa : a = a'
    · subst haa; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ haa]; exact hj
  rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
  · -- ramo `collect_promise`
    refine Or.inl ⟨collectSt (voteSt s a' b₂ v) i a, mk_collect (j := j) hc₁ hj₂ hb ha hlt, ?_⟩
    refine paxos_step_congr (mk_vote (i := i') (j := j') hc₂ hj' hbal) ?_
    simp only [collectSt, voteSt]
  · -- ramo `collect_promise_update`
    refine Or.inl ⟨collectUpdSt (voteSt s a' b₂ v) i a acc, mk_collectUpd (j := j) hc₁ hj₂ hb ha hgt, ?_⟩
    refine paxos_step_congr (mk_vote (i := i') (j := j') hc₂ hj' hbal) ?_
    simp only [collectUpdSt, voteSt]

theorem comm_accept_promise {n} {s s' s'' : PaxosState n} {i a : Fin n} {b₁ b₂ : Ballot} {v : Value} :
  paxos_step s (.proposer (.accept b₁ v) i) s' →
  paxos_step s (.acceptor (.promise b₂) a) s'' →
  (∃ s''', paxos_step s'' (.proposer (.accept b₁ v) i) s''' ∧
           paxos_step s' (.acceptor (.promise b₂) a) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, hp₁, hq₁, hv₁, rfl⟩ := accept_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := promise_inv h₂
  refine Or.inl ⟨acceptSt (promiseSt s a b₂) i b₁ v, mk_accept hc₁ hb₁ hp₁ hq₁ hv₁, ?_⟩
  refine paxos_step_congr (mk_promise (i := i') (j := j) hc₂ ?_ hbal) ?_
  · -- il `prepare b₂` è ancora in `pmsgs i'` dopo l'append del proposer `i`
    simp only [acceptSt]
    by_cases hii : i' = i
    · subst hii; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ hii]; exact hj
  · -- gli stati finali coincidono
    simp only [acceptSt, promiseSt]

theorem comm_accept_vote {n} {s s' s'' : PaxosState n} {i a : Fin n} {b₁ b₂ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.proposer (.accept b₁ v₁) i) s' →
  paxos_step s (.acceptor (.vote b₂ v₂) a) s'' →
  (∃ s''', paxos_step s'' (.proposer (.accept b₁ v₁) i) s''' ∧
           paxos_step s' (.acceptor (.vote b₂ v₂) a) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, hp₁, hq₁, hv₁, rfl⟩ := accept_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := vote_inv h₂
  refine Or.inl ⟨acceptSt (voteSt s a b₂ v₂) i b₁ v₁, mk_accept hc₁ hb₁ hp₁ hq₁ hv₁, ?_⟩
  refine paxos_step_congr (mk_vote (i := i') (j := j) hc₂ ?_ hbal) ?_
  · -- il `propose b₂ v₂` è ancora in `pmsgs i'` dopo l'append del proposer `i`
    simp only [acceptSt]
    by_cases hii : i' = i
    · subst hii; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj
    · simp only [update_Fin_gso2 _ _ _ _ hii]; exact hj
  · -- gli stati finali coincidono
    simp only [acceptSt, voteSt]

/-! ## Proposer–learner -/

theorem comm_prepare_collect_accepted {n} {s s' s'' : PaxosState n} {i l a : Fin n} {b₁ b₂ : Ballot}
    {v : Value} :
  paxos_step s (.proposer (.prepare b₁) i) s' →
  paxos_step s (.learner (.collect_accepted a b₂ v) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i) s''' ∧
           paxos_step s' (.learner (.collect_accepted a b₂ v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, ⟨j, hj⟩, ha₂, rfl⟩ := lcollect_inv h₂
  refine Or.inl ⟨prepareSt (lcollectSt s l a b₂ v) i b₁, mk_prepare hc₁ hb₁, ?_⟩
  refine paxos_step_congr (mk_lcollect (j := j) hc₂ hj ha₂) ?_
  simp only [prepareSt, lcollectSt]

theorem comm_prepare_decide_rs {n} {s s' s'' : PaxosState n} {i l : Fin n} {b₁ : Ballot} {v : Value} :
  paxos_step s (.proposer (.prepare b₁) i) s' →
  paxos_step_external s (.part (.decide_rs v) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.prepare b₁) i) s''' ∧
           paxos_step_external s' (.part (.decide_rs v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, rfl⟩ := prepare_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b₂, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  refine Or.inl ⟨prepareSt (decideSt s l v) i b₁, mk_prepare hc₁ hb₁, ?_⟩
  refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd₂ hq₂) ?_
  simp only [prepareSt, decideSt]

theorem comm_collect_promise_collect_accepted {n} {s s' s'' : PaxosState n} {i l a a' : Fin n}
    {b₁ b₂ : Ballot} {acc : Option (Ballot × Value)} {v : Value} :
  paxos_step s (.proposer (.collect_promise a b₁ acc) i) s' →
  paxos_step s (.learner (.collect_accepted a' b₂ v) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a b₁ acc) i) s''' ∧
           paxos_step s' (.learner (.collect_accepted a' b₂ v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, hb₁, ha₁, hbr⟩ := collect_inv h₁
  obtain ⟨hc₂, ⟨j', hj'⟩, ha₂, rfl⟩ := lcollect_inv h₂
  rcases hbr with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
  · refine Or.inl ⟨collectSt (lcollectSt s l a' b₂ v) i a,
      mk_collect (j := j) hc₁ hj hb₁ ha₁ hlt, ?_⟩
    refine paxos_step_congr (mk_lcollect (j := j') hc₂ hj' ha₂) ?_
    simp only [collectSt, lcollectSt]
  · refine Or.inl ⟨collectUpdSt (lcollectSt s l a' b₂ v) i a acc,
      mk_collectUpd (j := j) hc₁ hj hb₁ ha₁ hgt, ?_⟩
    refine paxos_step_congr (mk_lcollect (j := j') hc₂ hj' ha₂) ?_
    simp only [collectUpdSt, lcollectSt]

theorem comm_collect_promise_decide_rs {n} {s s' s'' : PaxosState n} {i l a : Fin n} {b₁ : Ballot}
    {acc : Option (Ballot × Value)} {v : Value} :
  paxos_step s (.proposer (.collect_promise a b₁ acc) i) s' →
  paxos_step_external s (.part (.decide_rs v) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.collect_promise a b₁ acc) i) s''' ∧
           paxos_step_external s' (.part (.decide_rs v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨j, hj⟩, hb₁, ha₁, hbr⟩ := collect_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b₂, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  rcases hbr with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
  · refine Or.inl ⟨collectSt (decideSt s l v) i a,
      mk_collect (j := j) hc₁ hj hb₁ ha₁ hlt, ?_⟩
    refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd₂ hq₂) ?_
    simp only [collectSt, decideSt]
  · refine Or.inl ⟨collectUpdSt (decideSt s l v) i a acc,
      mk_collectUpd (j := j) hc₁ hj hb₁ ha₁ hgt, ?_⟩
    refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd₂ hq₂) ?_
    simp only [collectUpdSt, decideSt]

theorem comm_accept_collect_accepted {n} {s s' s'' : PaxosState n} {i l a : Fin n} {b₁ b₂ : Ballot}
    {v₁ v₂ : Value} :
  paxos_step s (.proposer (.accept b₁ v₁) i) s' →
  paxos_step s (.learner (.collect_accepted a b₂ v₂) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.accept b₁ v₁) i) s''' ∧
           paxos_step s' (.learner (.collect_accepted a b₂ v₂) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, hp₁, hq₁, hv₁, rfl⟩ := accept_inv h₁
  obtain ⟨hc₂, ⟨j, hj⟩, ha₂, rfl⟩ := lcollect_inv h₂
  refine Or.inl ⟨acceptSt (lcollectSt s l a b₂ v₂) i b₁ v₁, mk_accept hc₁ hb₁ hp₁ hq₁ hv₁, ?_⟩
  refine paxos_step_congr (mk_lcollect (j := j) hc₂ hj ha₂) ?_
  simp only [acceptSt, lcollectSt]

theorem comm_accept_decide_rs {n} {s s' s'' : PaxosState n} {i l : Fin n} {b₁ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.proposer (.accept b₁ v₁) i) s' →
  paxos_step_external s (.part (.decide_rs v₂) l) s'' →
  (∃ s''', paxos_step s'' (.proposer (.accept b₁ v₁) i) s''' ∧
           paxos_step_external s' (.part (.decide_rs v₂) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, hb₁, hp₁, hq₁, hv₁, rfl⟩ := accept_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b₂, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  refine Or.inl ⟨acceptSt (decideSt s l v₂) i b₁ v₁, mk_accept hc₁ hb₁ hp₁ hq₁ hv₁, ?_⟩
  refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd₂ hq₂) ?_
  simp only [acceptSt, decideSt]

/-! ## Acceptor–learner -/

theorem comm_promise_collect_accepted {n} {s s' s'' : PaxosState n} {a l a' : Fin n} {b₁ b₂ : Ballot}
    {v : Value} :
  paxos_step s (.acceptor (.promise b₁) a) s' →
  paxos_step s (.learner (.collect_accepted a' b₂ v) l) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.promise b₁) a) s''' ∧
           paxos_step s' (.learner (.collect_accepted a' b₂ v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i, j, hj⟩, hbal, rfl⟩ := promise_inv h₁
  obtain ⟨hc₂, ⟨j', hj'⟩, ha, rfl⟩ := lcollect_inv h₂
  refine Or.inl ⟨promiseSt (lcollectSt s l a' b₂ v) a b₁, mk_promise (i := i) (j := j) hc₁ hj hbal, ?_⟩
  refine paxos_step_congr (mk_lcollect (j := j') hc₂ ?_ ha) ?_
  · -- l'`accepted b₂ v` è ancora in `amsgs a'` dopo l'append dell'acceptor `a`
    simp only [promiseSt]
    by_cases haa : a' = a
    · subst haa; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj'
    · simp only [update_Fin_gso2 _ _ _ _ haa]; exact hj'
  · -- gli stati finali coincidono
    simp only [promiseSt, lcollectSt]

theorem comm_promise_decide_rs {n} {s s' s'' : PaxosState n} {a l : Fin n} {b₁ : Ballot} {v : Value} :
  paxos_step s (.acceptor (.promise b₁) a) s' →
  paxos_step_external s (.part (.decide_rs v) l) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.promise b₁) a) s''' ∧
           paxos_step_external s' (.part (.decide_rs v) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i, j, hj⟩, hbal, rfl⟩ := promise_inv h₁
  obtain ⟨hc₂, hd, ⟨b₂, hq⟩, rfl⟩ := decide_rs_inv h₂
  refine Or.inl ⟨promiseSt (decideSt s l v) a b₁, mk_promise (i := i) (j := j) hc₁ hj hbal, ?_⟩
  refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd hq) ?_
  -- gli stati finali coincidono
  simp only [promiseSt, decideSt]

theorem comm_vote_collect_accepted {n} {s s' s'' : PaxosState n} {a l a' : Fin n} {b₁ b₂ : Ballot}
    {v₁ v₂ : Value} :
  paxos_step s (.acceptor (.vote b₁ v₁) a) s' →
  paxos_step s (.learner (.collect_accepted a' b₂ v₂) l) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.vote b₁ v₁) a) s''' ∧
           paxos_step s' (.learner (.collect_accepted a' b₂ v₂) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i, j, hj⟩, hbal, rfl⟩ := vote_inv h₁
  obtain ⟨hc₂, ⟨j', hj'⟩, ha, rfl⟩ := lcollect_inv h₂
  refine Or.inl ⟨voteSt (lcollectSt s l a' b₂ v₂) a b₁ v₁, mk_vote (i := i) (j := j) hc₁ hj hbal, ?_⟩
  refine paxos_step_congr (mk_lcollect (j := j') hc₂ ?_ ha) ?_
  · -- l'`accepted b₂ v₂` è ancora in `amsgs a'` dopo l'append dell'acceptor `a`
    simp only [voteSt]
    by_cases haa : a' = a
    · subst haa; simp only [update_Fin_gss]; exact lst_get_append _ _ _ _ hj'
    · simp only [update_Fin_gso2 _ _ _ _ haa]; exact hj'
  · -- gli stati finali coincidono
    simp only [voteSt, lcollectSt]

theorem comm_vote_decide_rs {n} {s s' s'' : PaxosState n} {a l : Fin n} {b₁ : Ballot} {v₁ v₂ : Value} :
  paxos_step s (.acceptor (.vote b₁ v₁) a) s' →
  paxos_step_external s (.part (.decide_rs v₂) l) s'' →
  (∃ s''', paxos_step s'' (.acceptor (.vote b₁ v₁) a) s''' ∧
           paxos_step_external s' (.part (.decide_rs v₂) l) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, ⟨i, j, hj⟩, hbal, rfl⟩ := vote_inv h₁
  obtain ⟨hc₂, hd, ⟨b₂, hq⟩, rfl⟩ := decide_rs_inv h₂
  refine Or.inl ⟨voteSt (decideSt s l v₂) a b₁ v₁, mk_vote (i := i) (j := j) hc₁ hj hbal, ?_⟩
  refine paxos_step_external_congr (mk_decide_rs (b := b₂) hc₂ hd hq) ?_
  -- gli stati finali coincidono
  simp only [voteSt, decideSt]

/-! ## Crash

Il crash del nodo `i` e un passo del nodo `i'`: con `i ≠ i'` il diamante (il crash non tocca
né lo stato del nodo `i'` né la rete); con `i = i'` i due passi non commutano mai, perché dopo
il crash il nodo non fa più nulla (crash-stop): l'enunciato lo dice con il disgiunto `i = i'`. -/

theorem comm_crash_prepare {n} {s s' s'' : PaxosState n} {i i' : Fin n} {b : Ballot} :
  paxos_step s (.crash i) s' →
  paxos_step s (.proposer (.prepare b) i') s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.proposer (.prepare b) i') s''')
  ∨ s' = s''
  ∨ i = i'
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, hb₂, rfl⟩ := prepare_inv h₂
  by_cases hii : i = i'
  · exact Or.inr (Or.inr (Or.inl hii))
  · refine Or.inl ⟨crashSt (prepareSt s i' b) i, mk_crash hc₁, ?_⟩
    refine paxos_step_congr (mk_prepare ?_ hb₂) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hii]; exact hc₂
    · simp only [crashSt, prepareSt]

theorem comm_crash_collect_promise {n} {s s' s'' : PaxosState n} {i i' a : Fin n} {b : Ballot}
    {acc : Option (Ballot × Value)} :
  paxos_step s (.crash i) s' →
  paxos_step s (.proposer (.collect_promise a b acc) i') s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.proposer (.collect_promise a b acc) i') s''')
  ∨ s' = s''
  ∨ i = i'
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, ⟨j, hj⟩, hb₂, ha₂, hcase⟩ := collect_inv h₂
  by_cases hii : i = i'
  · exact Or.inr (Or.inr (Or.inl hii))
  · rcases hcase with ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩
    · refine Or.inl ⟨crashSt (collectSt s i' a) i, mk_crash hc₁, ?_⟩
      refine paxos_step_congr (mk_collect (j := j) ?_ hj hb₂ ha₂ hlt) ?_
      · simp only [crashSt, update_Fin_gso _ _ _ _ hii]; exact hc₂
      · simp only [crashSt, collectSt]
    · refine Or.inl ⟨crashSt (collectUpdSt s i' a acc) i, mk_crash hc₁, ?_⟩
      refine paxos_step_congr (mk_collectUpd (j := j) ?_ hj hb₂ ha₂ hgt) ?_
      · simp only [crashSt, update_Fin_gso _ _ _ _ hii]; exact hc₂
      · simp only [crashSt, collectUpdSt]

theorem comm_crash_accept {n} {s s' s'' : PaxosState n} {i i' : Fin n} {b : Ballot} {v : Value} :
  paxos_step s (.crash i) s' →
  paxos_step s (.proposer (.accept b v) i') s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.proposer (.accept b v) i') s''')
  ∨ s' = s''
  ∨ i = i'
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, hb₂, hp₂, hq₂, hv₂, rfl⟩ := accept_inv h₂
  by_cases hii : i = i'
  · exact Or.inr (Or.inr (Or.inl hii))
  · refine Or.inl ⟨crashSt (acceptSt s i' b v) i, mk_crash hc₁, ?_⟩
    refine paxos_step_congr (mk_accept ?_ hb₂ hp₂ hq₂ hv₂) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hii]; exact hc₂
    · simp only [crashSt, acceptSt]

theorem comm_crash_promise {n} {s s' s'' : PaxosState n} {i a : Fin n} {b : Ballot} :
  paxos_step s (.crash i) s' →
  paxos_step s (.acceptor (.promise b) a) s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.acceptor (.promise b) a) s''')
  ∨ s' = s''
  ∨ i = a
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := promise_inv h₂
  by_cases hia : i = a
  · exact Or.inr (Or.inr (Or.inl hia))
  · refine Or.inl ⟨crashSt (promiseSt s a b) i, mk_crash hc₁, ?_⟩
    refine paxos_step_congr (mk_promise (i := i') (j := j) ?_ hj hbal) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hia]; exact hc₂
    · simp only [crashSt, promiseSt]

theorem comm_crash_vote {n} {s s' s'' : PaxosState n} {i a : Fin n} {b : Ballot} {v : Value} :
  paxos_step s (.crash i) s' →
  paxos_step s (.acceptor (.vote b v) a) s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.acceptor (.vote b v) a) s''')
  ∨ s' = s''
  ∨ i = a
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, ⟨i', j, hj⟩, hbal, rfl⟩ := vote_inv h₂
  by_cases hia : i = a
  · exact Or.inr (Or.inr (Or.inl hia))
  · refine Or.inl ⟨crashSt (voteSt s a b v) i, mk_crash hc₁, ?_⟩
    refine paxos_step_congr (mk_vote (i := i') (j := j) ?_ hj hbal) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hia]; exact hc₂
    · simp only [crashSt, voteSt]

theorem comm_crash_collect_accepted {n} {s s' s'' : PaxosState n} {i l a : Fin n} {b : Ballot} {v : Value} :
  paxos_step s (.crash i) s' →
  paxos_step s (.learner (.collect_accepted a b v) l) s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step s' (.learner (.collect_accepted a b v) l) s''')
  ∨ s' = s''
  ∨ i = l
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, ⟨j, hj⟩, ha₂, rfl⟩ := lcollect_inv h₂
  by_cases hil : i = l
  · exact Or.inr (Or.inr (Or.inl hil))
  · refine Or.inl ⟨crashSt (lcollectSt s l a b v) i, mk_crash hc₁, ?_⟩
    refine paxos_step_congr (mk_lcollect (j := j) ?_ hj ha₂) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hil]; exact hc₂
    · simp only [crashSt, lcollectSt]

theorem comm_crash_decide_rs {n} {s s' s'' : PaxosState n} {i l : Fin n} {v : Value} :
  paxos_step s (.crash i) s' →
  paxos_step_external s (.part (.decide_rs v) l) s'' →
  (∃ s''', paxos_step s'' (.crash i) s''' ∧
           paxos_step_external s' (.part (.decide_rs v) l) s''')
  ∨ s' = s''
  ∨ i = l
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, hd₂, ⟨b, hq₂⟩, rfl⟩ := decide_rs_inv h₂
  by_cases hil : i = l
  · exact Or.inr (Or.inr (Or.inl hil))
  · refine Or.inl ⟨crashSt (decideSt s l v) i, mk_crash hc₁, ?_⟩
    refine paxos_step_external_congr (mk_decide_rs (b := b) ?_ hd₂ hq₂) ?_
    · simp only [crashSt, update_Fin_gso _ _ _ _ hil]; exact hc₂
    · simp only [crashSt, decideSt]

theorem comm_crash_crash {n} {s s' s'' : PaxosState n} {i₁ i₂ : Fin n} :
  paxos_step s (.crash i₁) s' →
  paxos_step s (.crash i₂) s'' →
  (∃ s''', paxos_step s'' (.crash i₁) s''' ∧
           paxos_step s' (.crash i₂) s''')
  ∨ s' = s''
  ∨ ¬ Paxos.reachable s := by
  intro h₁ h₂
  obtain ⟨hc₁, rfl⟩ := crash_inv h₁
  obtain ⟨hc₂, rfl⟩ := crash_inv h₂
  by_cases hii : i₁ = i₂
  · subst hii; exact Or.inr (Or.inl rfl)
  · refine Or.inl ⟨crashSt (crashSt s i₂) i₁, ?_, ?_⟩
    · refine mk_crash ?_
      simp only [crashSt, update_Fin_gso2 _ _ _ _ hii]; exact hc₁
    · refine paxos_step_congr (mk_crash ?_) ?_
      · simp only [crashSt, update_Fin_gso _ _ _ _ hii]; exact hc₂
      · simp only [crashSt, update_Fin_comm _ _ _ _ _ hii]
