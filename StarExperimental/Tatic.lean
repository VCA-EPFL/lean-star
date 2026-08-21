import Star.BackwardsInvariants.TwoPhaseCommit
import StarExperimental.MI

/-!
# `backward_search`: la tattica di ricerca backward

Tattica da chiamare dentro una dimostrazione di `¬ l.reachable s`:

    theorem no : ¬ twoPC.reachable disagreement := by
      backward_search init_state

Fa esattamente il procedimento descritto a voce:

* **vado backward di uno step** — per lo stato `a` la tattica apre il goal
  `∀ p t, l.transitions t p a → …` e *inverte le regole* con `cases`: ogni
  regola che può arrivare in `a` produce un predecessore concreto, i rami
  impossibili si potano da soli;
* **aggiungo tutti gli stati raggiunti alla lista di stati irraggiungibili** —
  la lista `visited` mantenuta dalla tattica;
* **se lo stato è già nella lista mi fermo, ho fatto centro** — il controllo di
  appartenenza prima di esplorare;
* **se no faccio l'induzione backward di nuovo** — il ciclo sulla frontiera;
* **se da uno stato non si può andare backward ho vinto** — l'inversione non
  produce nessun sottogoal, il ramo è chiuso.

In più (necessario per la correttezza, e non era nella descrizione a voce): se
andando all'indietro si incontra uno **stato iniziale**, la tattica fallisce,
perché in quel caso il cammino trovato, letto in avanti, porta dall'init allo
stato di partenza — che quindi è raggiungibile.

## Perché il risultato è affidabile

La ricerca è solo una *euristica per trovare la lista* `U`. Alla fine la tattica
costruisce un termine di prova con `unreachable_certificate`, e ri-dimostra da
capo, per ogni `a ∈ U`, che tutti i predecessori di `a` stanno in `U`. Quel
termine passa dal kernel: se la ricerca avesse dimenticato un predecessore, la
tattica fallirebbe invece di produrre una prova sbagliata. Non serve quindi
nessuna prova di completezza a carico dell'utente.

L'induzione backward non è riscritta qui: il certificato usa
`LTS.backwards_reachable_from` e `backwards_reachable_not_init` di `THEORY`, e
i lemmi `backwards_closed` / `unreachable_of_backwards_closed` sono
`back_reachable_twoPC` / `reachable_twoPC` generalizzati a un predicato
qualsiasi al posto di `unreachable_set`.

## L'inversione adattiva

Alcune regole non si invertono per pura unificazione. In TwoPhaseCommit,

    step_commit : … → Protocol .commit s {p1 := s.p1.commit, p2 := s.p2.commit, …}

ha in conclusione `PState.commit s.p1`, che non è un costruttore: `cases` si
blocca con "dependent elimination failed". Allora la tattica *enumera* un campo
di tipo finito e riprova, ricorsivamente, finché l'inversione riesce. Enumera
solo quanto serve: le regole che si invertono da sole non pagano nulla.

Requisiti: gli stati devono avere `DecidableEq` e campi di tipo finito
(induttivi non ricorsivi con campi finiti — `Bool`, `Option Bool`, `PState`…).
-/

open THEORY
open Relation
open Lean Meta Elab Tactic

namespace BackwardTactic

/-! ## Il certificato

La parte logica non è inventata da zero: è costruita sulle definizioni di
`THEORY` (`LTS.backwards_reachable_from`, `backwards_reachable_not_init`), e i
due teoremi qui sotto sono esattamente `back_reachable_twoPC` e `reachable_twoPC`
di `TwoPhaseCommit.lean`, generalizzati da `unreachable_set` a un predicato `P`
qualsiasi — così valgono per ogni `LTS` e non vanno riscritti per ogni sistema. -/

/-- Versione generica di `back_reachable_twoPC`: un predicato chiuso all'indietro
*di un passo* è chiuso lungo tutta la `backwards_reachable_from`. È l'induzione
backward, fatta una volta per tutte. -/
theorem backwards_closed {T : Type} {l : LTS T} {P : l.S → Prop}
    (hstep : ∀ (a p : l.S) (t : T), P a → l.transitions t p a → P p) {s x : l.S}
    (h : l.backwards_reachable_from s x) : P s → P x := by
  dsimp [LTS.backwards_reachable_from] at h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact id
  | @head a c h1 h2 h3 =>
    intro ha
    dsimp [Function.swap, LTS.atrans] at h1
    obtain ⟨t, ht⟩ := h1
    exact h3 (hstep a c t ha ht)

/-- Versione generica di `reachable_twoPC`: uno stato che sta in un insieme
chiuso all'indietro e privo di stati iniziali non è raggiungibile. Il passaggio
da `reachable` a `backwards_reachable_from` è `backwards_reachable_not_init`
di `THEORY`. -/
theorem unreachable_of_backwards_closed {T : Type} {l : LTS T} {P : l.S → Prop}
    (hstep : ∀ (a p : l.S) (t : T), P a → l.transitions t p a → P p)
    (s_init : l.S) (hinit : l.init s_init) (hninit : ¬ P s_init)
    {s : l.S} (hs : P s) : ¬ l.reachable s := fun hreach =>
  hninit (backwards_closed hstep
    (backwards_reachable_not_init.mpr hreach s_init hinit) hs)

/-- Il certificato applicato dalla tattica. Il predicato è l'appartenenza alla
lista `U` prodotta dalla ricerca: `(· ∈ U)` gioca esattamente il ruolo che in
`TwoPhaseCommit.lean` ha `unreachable_set`, con la differenza che qui la lista
la calcola la tattica invece di doverla inventare a mano. -/
theorem unreachable_certificate {T : Type} {l : LTS T}
    (U : List l.S) (s_init : l.S) (hinit : l.init s_init)
    {s₀ : l.S} (hmem : s₀ ∈ U)
    (hninit : ∀ s ∈ U, ¬ l.init s)
    (hclosed : ∀ a ∈ U, ∀ (p : l.S) (t : T), l.transitions t p a → p ∈ U) :
    ¬ l.reachable s₀ :=
  unreachable_of_backwards_closed (P := (· ∈ U))
    (fun a p t ha ht => hclosed a ha p t ht)
    s_init hinit (fun hs => hninit s_init hs hinit) hmem

/-! ### Il certificato duale

Quando la chiusura **all'indietro** dell'insieme cattivo è enorme ma gli stati
raggiungibili sono pochi, conviene girare il ragionamento: invece di un insieme
chiuso all'indietro che contiene lo stato cattivo, un insieme chiuso **in
avanti** che contiene quello iniziale e non contiene il cattivo.

È lo stesso certificato letto nell'altro verso, e la macchina è identica: dove
la ricerca all'indietro chiede "chi può portare *in* questo stato?", quella in
avanti chiede "dove si può andare *da* questo stato?". -/

/-- Un predicato chiuso in avanti di un passo è chiuso lungo tutto il cammino.
È l'induzione in avanti, speculare a `backwards_closed`. -/
theorem forward_closed {T : Type} {l : LTS T} {P : l.S → Prop}
    (hstep : ∀ (a p : l.S) (t : T), P a → l.transitions t a p → P p) {x y : l.S}
    (h : ReflTransGen l.atrans x y) : P x → P y := by
  induction h with
  | refl => exact id
  | tail _ hlast ih =>
    intro hx
    obtain ⟨t, ht⟩ := hlast
    exact hstep _ _ t (ih hx) ht

/-- Il certificato in avanti: `V` contiene lo stato iniziale, è chiuso per
transizione, e `s₀` non ci sta. Allora `s₀` non è raggiungibile. -/
theorem invariant_certificate {T : Type} {l : LTS T}
    (V : List l.S) (s_init : l.S) (hinit : l.init s_init) (hmem : s_init ∈ V)
    (hclosed : ∀ a ∈ V, ∀ (p : l.S) (t : T), l.transitions t a p → p ∈ V)
    {s₀ : l.S} (hbad : s₀ ∈ V → False) : ¬ l.reachable s₀ := fun hreach =>
  hbad (forward_closed (P := (· ∈ V)) (fun a p t ha ht => hclosed a ha p t ht)
    (hreach s_init hinit) hmem)

/-- Marcatore usato solo durante la fase di ricerca per "leggere" i predecessori
dai goal residui: la tattica apre `∀ p t, trans t p a → Frontier p` e raccoglie
gli `X` dei goal `Frontier X`. È `irreducible` e vale `False`, quindi nessun
`simp` può dimostrarlo: un goal `Frontier X` si chiude solo se le ipotesi del
ramo sono contraddittorie, cioè se quel predecessore non esiste. -/
@[irreducible] def Frontier {α : Type} (_ : α) : Prop := False

/-- `p ∈ U` sotto un nome che `simp` non srotola (un `def` semplice non ha
lemmi di equazione nel simp set). Serve nelle obbligazioni del certificato: la
lista `U` può avere centinaia di stati, e lasciare che `simp_all` la espanda a
ogni foglia costa quanto tutto il resto messo insieme. È definizionalmente
uguale a `p ∈ U`, quindi `decide` la valuta e il certificato la accetta. -/
def InList {α : Type} (U : List α) (p : α) : Prop := p ∈ U

/-! ## Utilità meta -/

/-- `ty` è un tipo finito enumerabile? Induttivo non ricorsivo, senza indici, i
cui costruttori hanno solo campi a loro volta finiti (`Bool`, `Option Bool`,
`PState`, `State`, …). Il `fuel` protegge dalle catene troppo profonde. -/
partial def isFiniteType (fuel : Nat) (ty : Expr) : MetaM Bool := do
  if fuel == 0 then return false
  let ty ← whnfD ty
  let .const n us := ty.getAppFn | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  if iv.numIndices != 0 || iv.isRec then return false
  let args := ty.getAppArgs
  if args.size != iv.numParams then return false
  iv.ctors.allM fun c => do
    let cty ← inferType (mkAppN (mkConst c us) args)
    forallTelescopeReducing cty fun fields _ =>
      fields.allM fun f => do isFiniteType (fuel - 1) (← inferType f)

/-- `simp_all` su un goal: `none` se il goal si chiude (ramo impossibile),
altrimenti il goal semplificato. -/
def trySimpAll (g : MVarId) : MetaM (Option MVarId) := do
  try
    let ctx ← Simp.mkContext (config := {})
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let (res, _) ← simpAll g ctx (simprocs := #[← Simp.getSimprocs])
    return res
  catch _ => return some g

/-- La prima variabile libera del target che ha tipo finito (candidata da
enumerare). -/
def findFiniteFVar (g : MVarId) : MetaM (Option FVarId) :=
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    (collectFVars {} tgt).fvarIds.findM? fun fv => do
      isFiniteType 6 (← fv.getType)

/-- Enumera le variabili di tipo finito rimaste nel target (per esempio la `b`
di `.tentative b`, o un campo che la regola sovrascrive e quindi lascia libero
nel predecessore) e chiama `leaf` su ogni foglia completamente istanziata. -/
partial def splitFiniteFVars (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  match ← findFiniteFVar g with
  | none => leaf g
  | some fv =>
    for sub in ← g.cases fv do
      match ← trySimpAll sub.mvarId with
      | none => pure ()
      | some g' => splitFiniteFVars g' leaf

/-- **Il passo backward.** Goal: `⊢ l.transitions t p a → C p` (l'ipotesi di
transizione non ancora introdotta).

Prova a invertire le regole con `cases`. Se l'unificazione si blocca (una regola
ha in conclusione una funzione non-costruttore, come `PState.commit`), enumera
una variabile di tipo finito e riprova: solo i rami che ne hanno bisogno pagano
l'enumerazione. Se nessuna regola può arrivare in `a` non restano sottogoal:
"da questo stato non si può andare backward". -/
partial def invertStep (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  match ← observing? (do let (h, g1) ← g.intro `hstep; g1.cases h) with
  | some subs =>
    for sub in subs do
      match ← trySimpAll sub.mvarId with
      | none => pure ()
      | some g' => splitFiniteFVars g' leaf
  | none =>
    match ← findFiniteFVar g with
    | some fv => for sub in ← g.cases fv do invertStep sub.mvarId leaf
    | none =>
      throwError "backward_search: non riesco a invertire il passo su{indentD (← g.withContext do addMessageContext m!"{← g.getType}")}"

/-- Su un goal `∀ p t, l.transitions t p a → C p`: introduce `p` (destrutturandolo
nei campi, così le regole scritte con `{s with …}` si unificano) e `t`
(enumerando le regole), poi inverte. -/
def backwardStep (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  let (pF, g1) ← g.intro `p
  let gs ← (do
    match ← observing? (g1.cases pF) with
    | some subs => pure (subs.toList.map (·.mvarId))
    | none => pure [g1])
  for g2 in gs do
    let (tF, g3) ← g2.intro `t
    let gs2 ← (do
      match ← observing? (g3.cases tF) with
      | some subs => pure (subs.toList.map (·.mvarId))
      | none => pure [g3])
    for g4 in gs2 do
      invertStep g4 leaf

/-- Su un goal con ipotesi `hm : a ∈ U` (`U` lista letterale), enumera i casi
`a = u₁, a = u₂, …` e chiama `k` su ciascuno. -/
partial def enumMem (g : MVarId) (hm : FVarId) (k : MVarId → MetaM Unit) : MetaM Unit := do
  for sub in ← g.cases hm do
    if sub.ctorName == ``List.Mem.head then
      k sub.mvarId
    else
      enumMem sub.mvarId sub.fields.back!.fvarId! k

/-- Espone la testa di una proposizione (`l.init s` → la sua definizione),
lasciando intatto un eventuale `¬` davanti, così che l'istanza `Decidable` si
possa sintetizzare. -/
def normalizeProp (ty : Expr) : MetaM Expr := do
  match ty.not? with
  | some p => return mkApp (mkConst ``Not) (← whnfD p)
  | none => whnfD ty

/-- Srotola la testa di una proposizione di *un solo* passo, rispettando un
eventuale `¬` davanti. -/
def unfoldHeadOnce (ty : Expr) : MetaM (Option Expr) := do
  try
    match ty.not? with
    | some p => return (← unfoldDefinition? p).map (mkApp (mkConst ``Not))
    | none => unfoldDefinition? ty
  catch _ => return none

/-- Le forme successive di una proposizione: com'è, poi srotolandone la testa un
passo alla volta, infine in forma normale di testa.

Le istanze `Decidable` sono indicizzate sulla forma sintattica, quindi vanno
provate tutte: `x ∈ U` va lasciato intatto, `InList U x` srotolato di *un* passo
(due e diventa `List.Mem`, per cui non c'è istanza), `l.init s` fino in fondo. -/
def propForms (p : Expr) : MetaM (List Expr) := do
  let mut out := #[p]
  let mut q := p
  for _ in [0:8] do
    match ← unfoldHeadOnce q with
    | some q' => out := out.push q'; q := q'
    | none => break
  return (out.push (← normalizeProp p)).toList

/-- Come `mkDecideProof`, ma valuta davvero `decide p` e fallisce subito se non
si riduce a `true` (`mkDecideProof` da solo costruisce il termine senza
controllare, e l'errore emergerebbe solo nel kernel).

Prova prima sulla proposizione com'è — le istanze `Decidable` sono indicizzate
sulla forma sintattica, quindi `x ∈ U` va lasciato intatto — e solo se la
sintesi fallisce riprova sulla versione normalizzata, che serve per predicati
come `l.init s` la cui testa va srotolata. -/
def decideProp (p : Expr) : MetaM Expr := do
  let attempt (q : Expr) : MetaM (Option Expr) := do
    try
      let r ← withDefault <| whnf (← mkDecide q)
      if r.isConstOf ``Bool.true then return some (← mkDecideProof q) else return none
    catch _ => return none
  for q in ← propForms p do
    if let some e ← attempt q then return e
  throwError "la proposizione{indentExpr p}\nnon si riduce a `true` con `decide`"

/-- Valuta una proposizione decidibile chiusa, srotolandone la testa se serve
(un predicato definito dall'utente, come `twoCachesM`, non è riconosciuto dalla
sintesi di istanze finché non si espande). `none` se non è decidibile. -/
def evalDecidable (p : Expr) : MetaM (Option Bool) := do
  let attempt (q : Expr) : MetaM (Option Bool) := do
    try
      let r ← withDefault <| whnf (← mkDecide q)
      if r.isConstOf ``Bool.true then return some true
      else if r.isConstOf ``Bool.false then return some false
      else return none
    catch _ => return none
  for q in ← propForms p do
    if let some b ← attempt q then return some b
  return none

/-- Normalizza uno stato concreto (riduce coercizioni, proiezioni, `match`). -/
def normState (e : Expr) : MetaM Expr := do
  withDefault <| Meta.reduce (← instantiateMVars e) (skipTypes := true) (skipProofs := true)

/-! Enumerazione di un tipo finito: serve alla modalità "insieme di stati" per
trovare, dato un predicato, gli stati da cui far partire la ricerca. -/
mutual

/-- Tutti gli abitanti di un tipo finito. -/
partial def enumerateType (fuel : Nat) (ty : Expr) : MetaM (List Expr) := do
  if fuel == 0 then throwError "backward_search: tipo troppo profondo da enumerare"
  let ty ← whnfD ty
  let .const n us := ty.getAppFn
    | throwError "backward_search: tipo non enumerabile{indentExpr ty}"
  let some (.inductInfo iv) := (← getEnv).find? n
    | throwError "backward_search: tipo non enumerabile{indentExpr ty}"
  if iv.numIndices != 0 || iv.isRec then
    throwError "backward_search: tipo non finito{indentExpr ty}"
  let args := ty.getAppArgs
  let mut out : List Expr := []
  for c in iv.ctors do
    out := out ++ (← enumCtorArgs fuel (mkAppN (mkConst c us) args))
  return out

/-- Satura un costruttore parzialmente applicato in tutti i modi possibili. -/
partial def enumCtorArgs (fuel : Nat) (e : Expr) : MetaM (List Expr) := do
  match ← whnfD (← inferType e) with
  | .forallE _ dom _ _ =>
    let mut out : List Expr := []
    for v in ← enumerateType (fuel - 1) dom do
      out := out ++ (← enumCtorArgs fuel (mkApp e v))
    return out
  | _ => return [e]
end

/-! ## Il corpo della tattica -/

/-- **Fase 1** (la ricerca backward a partire da `seeds`) e **fase 2** (la
costruzione delle obbligazioni del certificato). Restituisce la lista `U`
trovata e le prove di `hinit`, `hninit`, `hclosed`. -/
def searchAndCertify (verbose : Bool) (TType lE Sty transE sInitE : Expr)
    (seeds : List Expr) : TacticM (Expr × Expr × Expr × Expr) := do
  ---------------------------------------------------------------------------
  -- FASE 1: la ricerca. `visited` è la lista di stati irraggiungibili,
  -- `frontier` gli stati ancora da esplorare all'indietro.
  ---------------------------------------------------------------------------
  let visitedRef ← IO.mkRef ([] : List Expr)
  -- gli stati sono termini chiusi normalizzati da `normState`, quindi
  -- l'uguaglianza strutturale basta: una hash set al posto della scansione
  -- `isDefEq` su tutta la lista, che da sola costava O(n²)
  let seenRef ← IO.mkRef (∅ : Std.HashSet Expr)
  let frontierRef ← IO.mkRef seeds
  let traceRef ← IO.mkRef (#[] : Array MessageData)
  let mut steps : Nat := 0
  repeat
    match ← frontierRef.get with
    | [] => break
    | a :: rest =>
      frontierRef.set rest
      steps := steps + 1
      if steps > 5000 then
        throwError "backward_search: troppi stati esplorati (>5000)"
      -- "se lo stato è già nella lista si ferma": fatto centro
      if (← seenRef.get).contains a then
        if verbose then
          traceRef.modify (·.push m!"[{steps}] {a}\n      già nella lista: FATTO CENTRO, ramo chiuso")
        continue
      -- lo stato non deve essere iniziale, altrimenti è raggiungibile
      let initA ← mkAppM ``LTS.init #[lE, a]
      unless ← (do try discard <| decideProp (mkApp (mkConst ``Not) initA); pure true
                   catch _ => pure false) do
        let sofar ← if verbose then
            pure (m!"backward_search: la ricerca all'indietro passo per passo\n\n"
              ++ MessageData.joinSep (← traceRef.get).toList m!"\n" ++ m!"\n\n")
          else pure m!""
        throwError (sofar ++
          m!"STOP al passo {steps}: andando all'indietro si raggiunge lo stato iniziale{indentExpr a}\nlo stato di partenza è quindi RAGGIUNGIBILE (oppure `init` non è decidibile)")
      visitedRef.modify (a :: ·)
      seenRef.modify (·.insert a)
      -- un passo backward: tutti i predecessori di `a`
      let goalTy ← withLocalDeclD `p Sty fun p =>
        withLocalDeclD `t TType fun t => do
          mkForallFVars #[p, t]
            (← mkArrow (mkApp3 transE t p a) (← mkAppM ``Frontier #[p]))
      let probe ← mkFreshExprMVar goalTy
      let predsRef ← IO.mkRef (#[] : Array Expr)
      backwardStep probe.mvarId! fun g => do
        let gty ← instantiateMVars (← g.getType)
        unless gty.isAppOfArity ``Frontier 2 do
          throwError "backward_search: forma inattesa del goal di esplorazione{indentExpr gty}"
        let X ← normState gty.appArg!
        if X.hasFVar || X.hasMVar then
          throwError "backward_search: predecessore non completamente determinato{indentExpr X}\n(il tipo degli stati ha campi non finiti?)"
        predsRef.modify (·.push X)
        frontierRef.modify (X :: ·)
      if verbose then
        let preds := (← predsRef.get).toList
        if preds.isEmpty then
          traceRef.modify (·.push
            m!"[{steps}] {a}\n      nessun predecessore: da qui non si va indietro, VINTO")
        else
          traceRef.modify (·.push (m!"[{steps}] {a}\n      {preds.length} predecessori, in frontiera:\n"
            ++ MessageData.joinSep (preds.map fun e => m!"        → {e}") m!"\n"))

  let visited := (← visitedRef.get).reverse
  if verbose then
    logInfo (m!"backward_search: {seeds.length} stati di partenza, la ricerca all'indietro passo per passo\n\n"
      ++ MessageData.joinSep (← traceRef.get).toList m!"\n"
      ++ m!"\n\nSTOP: frontiera vuota dopo {steps} passi — nessuno degli stati incontrati era iniziale, "
      ++ m!"quindi tutti e {visited.length} sono irraggiungibili.")

  ---------------------------------------------------------------------------
  -- FASE 2: le obbligazioni del certificato, ri-dimostrate da capo
  -- (è questo termine, non la ricerca, a essere controllato dal kernel).
  ---------------------------------------------------------------------------
  let UE ← mkListLit Sty visited
  let mkMemE := fun (x : Expr) => mkAppM ``Membership.mem #[UE, x]
  let hinitTy ← mkAppM ``LTS.init #[lE, sInitE]
  let hninitTy ← withLocalDeclD `s Sty fun s => do
    mkForallFVars #[s] (← mkArrow (← mkMemE s)
      (mkApp (mkConst ``Not) (← mkAppM ``LTS.init #[lE, s])))
  let hclosedTy ← withLocalDeclD `a Sty fun a => do
    let inner ← withLocalDeclD `p Sty fun p =>
      withLocalDeclD `t TType fun t => do
        mkForallFVars #[p, t]
          (← mkArrow (mkApp3 transE t p a) (← mkAppM ``InList #[UE, p]))
    mkForallFVars #[a] (← mkArrow (← mkMemE a) inner)
  let hinitM ← mkFreshExprMVar hinitTy
  let hninitM ← mkFreshExprMVar hninitTy
  let hclosedM ← mkFreshExprMVar hclosedTy

  -- (1) `s_init` è davvero uno stato iniziale
  try hinitM.mvarId!.assign (← decideProp hinitTy)
  catch _ =>
    try hinitM.mvarId!.refl
    catch _ =>
      throwError "backward_search: non riesco a dimostrare che{indentExpr sInitE}\nè uno stato iniziale"
  -- (2) nessuno stato della lista è iniziale
  let (fs, g1) ← hninitM.mvarId!.introN 2
  enumMem g1 fs[1]! fun g => do
    g.assign (← decideProp (← instantiateMVars (← g.getType)))
  -- (3) la lista è chiusa all'indietro: per ogni `a ∈ U` si rifà lo stesso
  --     passo backward della ricerca, e ogni predecessore deve stare in `U`
  let (fs2, g2) ← hclosedM.mvarId!.introN 2
  enumMem g2 fs2[1]! fun ga =>
    backwardStep ga fun g => do
      let gty ← instantiateMVars (← g.getType)
      if gty.hasFVar then
        throwError "backward_search: goal residuo non chiuso{indentExpr gty}"
      g.assign (← decideProp gty)

  return (UE, hinitM, hninitM, hclosedM)

/-- Modalità "uno stato": goal `¬ l.reachable s₀`. -/
def backwardSearchCore (verbose : Bool) (sInitStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let tgt ← instantiateMVars (← mainGoal.getType)
    let some body := tgt.not?
      | throwError "backward_search: il goal deve avere la forma `¬ l.reachable s`, trovato{indentExpr tgt}"
    unless body.isAppOfArity ``LTS.reachable 3 do
      throwError "backward_search: il goal deve avere la forma `¬ l.reachable s`, trovato{indentExpr body}"
    let args := body.getAppArgs
    let TType := args[0]!
    let lE := args[1]!
    let Sty ← whnfD (← mkAppM ``LTS.S #[lE])
    let transE ← whnfD (← mkAppM ``LTS.transitions #[lE])
    let s0 ← normState args[2]!
    let sInitE ← elabTermEnsuringType sInitStx (some Sty)
    let (UE, hinitM, hninitM, hclosedM) ←
      searchAndCertify verbose TType lE Sty transE sInitE [s0]
    let hmemM ← mkFreshExprMVar (← mkAppM ``Membership.mem #[UE, s0])
    hmemM.mvarId!.assign (← decideProp (← inferType hmemM))
    let prf ← mkAppOptM ``unreachable_certificate
      #[some TType, some lE, some UE, some sInitE, some hinitM, some s0,
        some hmemM, some hninitM, some hclosedM]
    unless ← isDefEq (← inferType prf) tgt do
      throwError "backward_search: impossibile applicare il certificato al goal"
    mainGoal.assign prf
    replaceMainGoal []

/-- Modalità "insieme di stati": goal `∀ s, P s → ¬ l.reachable s`.

La ricerca parte da *tutti* gli stati che soddisfano `P` — enumerando il tipo
degli stati e filtrando con `decide` — invece che da uno solo. Serve quando la
proprietà da escludere non è uno stato ma una condizione, come "due cache in
`M`", che vincola solo alcuni campi e lascia liberi gli altri. -/
def backwardSearchSetCore (verbose : Bool) (sInitStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let tgt ← instantiateMVars (← mainGoal.getType)
    -- il goal deve essere `∀ s, P s → ¬ l.reachable s`
    let (TType, lE, Sty, transE, PE) ← forallBoundedTelescope tgt (some 2) fun xs body => do
      unless xs.size == 2 do
        throwError "backward_search_all: il goal deve avere la forma `∀ s, P s → ¬ l.reachable s`, trovato{indentExpr tgt}"
      let some nbody := body.not?
        | throwError "backward_search_all: il goal deve avere la forma `∀ s, P s → ¬ l.reachable s`, trovato{indentExpr tgt}"
      unless nbody.isAppOfArity ``LTS.reachable 3 && nbody.getAppArgs[2]! == xs[0]! do
        throwError "backward_search_all: il goal deve avere la forma `∀ s, P s → ¬ l.reachable s`, trovato{indentExpr tgt}"
      let args := nbody.getAppArgs
      let lE := args[1]!
      return (args[0]!, lE,
        ← whnfD (← mkAppM ``LTS.S #[lE]),
        ← whnfD (← mkAppM ``LTS.transitions #[lE]),
        ← mkLambdaFVars #[xs[0]!] (← inferType xs[1]!))
    let sInitE ← elabTermEnsuringType sInitStx (some Sty)
    -- gli stati di partenza: tutti quelli che soddisfano `P`
    let mut seeds : List Expr := []
    for v in ← enumerateType 8 Sty do
      let pv := (mkApp PE v).headBeta
      let some ok ← evalDecidable pv
        | throwError "backward_search_all: il predicato{indentExpr pv}\nnon è decidibile"
      if ok then seeds := (← normState v) :: seeds
    if seeds.isEmpty then
      throwError "backward_search_all: nessuno stato soddisfa il predicato"
    if verbose then
      logInfo m!"backward_search_all: {seeds.length} stati di partenza soddisfano il predicato"
    let (UE, hinitM, hninitM, hclosedM) ←
      searchAndCertify verbose TType lE Sty transE sInitE seeds
    -- ogni stato che soddisfa `P` sta nella lista trovata
    let hmemAllTy ← withLocalDeclD `s Sty fun s => do
      mkForallFVars #[s] (← mkArrow (mkApp PE s).headBeta
        (← mkAppM ``InList #[UE, s]))
    let hmemAllM ← mkFreshExprMVar hmemAllTy
    let (_, gm) ← hmemAllM.mvarId!.intro `s
    -- per ogni stato concreto: o soddisfa `P` e allora sta nella lista (era un
    -- seme della ricerca), oppure non lo soddisfa e l'ipotesi è contraddittoria
    splitFiniteFVars gm fun g => g.withContext do
      let gty ← instantiateMVars (← g.getType)
      if let some e ← (try pure (some (← decideProp gty)) catch _ => pure none) then
        g.assign e
      else
        let (hF, g1) ← g.intro `hp
        g1.withContext do
          let gty1 ← instantiateMVars (← g1.getType)
          if let some e ← (try pure (some (← decideProp gty1)) catch _ => pure none) then
            g1.assign e
          else
            let hn ← decideProp (mkApp (mkConst ``Not) (← instantiateMVars (← hF.getType)))
            g1.assign (← mkAppOptM ``absurd #[none, some gty1, some (mkFVar hF), some hn])
    let prf ← withLocalDeclD `s Sty fun s =>
      withLocalDeclD `hp (mkApp PE s).headBeta fun hp => do
        let body ← mkAppOptM ``unreachable_certificate
          #[some TType, some lE, some UE, some sInitE, some hinitM, some s,
            some (mkApp2 hmemAllM s hp), some hninitM, some hclosedM]
        mkLambdaFVars #[s, hp] body
    unless ← isDefEq (← inferType prf) tgt do
      throwError "backward_search_all: impossibile applicare il certificato al goal"
    mainGoal.assign prf
    replaceMainGoal []

/-- **La ricerca in avanti.** Goal: `¬ l.reachable s₀` oppure
`∀ s, P s → ¬ l.reachable s`.

Esplora in avanti da `s_init` accumulando l'insieme raggiungibile `V`, e
fallisce appena incontra uno stato cattivo (che allora è raggiungibile davvero).
Alla fine applica `invariant_certificate`.

Rispetto a `backward_search` cambia solo *da che parte* si guarda la
transizione: qui il goal di esplorazione è `∀ p t, l.transitions t a p → …`,
con `a` (la sorgente) concreta invece del bersaglio. Il resto della macchina —
inversione delle regole, potatura dei rami impossibili, enumerazione dei campi
liberi — è la stessa. -/
def forwardInvariantCore (verbose : Bool) (sInitStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let tgt ← instantiateMVars (← mainGoal.getType)
    -- il goal è `¬ l.reachable s₀` oppure `∀ s, P s → ¬ l.reachable s`
    let parseReach (body : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
      unless body.isAppOfArity ``LTS.reachable 3 do
        throwError "forward_invariant: atteso `l.reachable s`, trovato{indentExpr body}"
      let args := body.getAppArgs
      let lE := args[1]!
      return (args[0]!, lE, ← whnfD (← mkAppM ``LTS.S #[lE]),
        ← whnfD (← mkAppM ``LTS.transitions #[lE]), args[2]!)
    let (TType, lE, Sty, transE, single?, pred?) ←
      match tgt.not? with
      | some body => do
        let (T, l, S, tr, s0) ← parseReach body
        pure (T, l, S, tr, some (← normState s0), none)
      | none =>
        forallBoundedTelescope tgt (some 2) fun xs body => do
          unless xs.size == 2 do
            throwError "forward_invariant: il goal deve essere `¬ l.reachable s` o `∀ s, P s → ¬ l.reachable s`, trovato{indentExpr tgt}"
          let some nbody := body.not?
            | throwError "forward_invariant: atteso `¬ l.reachable s` dopo le ipotesi, trovato{indentExpr body}"
          let (T, l, S, tr, s0) ← parseReach nbody
          unless s0 == xs[0]! do
            throwError "forward_invariant: `∀ s, P s → ¬ l.reachable s` deve parlare della stessa `s`"
          pure (T, l, S, tr, none, some (← mkLambdaFVars #[xs[0]!] (← inferType xs[1]!)))
    let sInitE ← normState (← elabTermEnsuringType sInitStx (some Sty))

    ---------------------------------------------------------------------------
    -- FASE 1: l'esplorazione in avanti
    ---------------------------------------------------------------------------
    let isBad (x : Expr) : TacticM Bool := do
      match single?, pred? with
      | some s0, _ => pure (x == s0)
      | _, some PE => pure ((← evalDecidable (mkApp PE x).headBeta).getD false)
      | _, _ => pure false
    let visitedRef ← IO.mkRef ([] : List Expr)
    let seenRef ← IO.mkRef (∅ : Std.HashSet Expr)
    let frontierRef ← IO.mkRef [sInitE]
    let traceRef ← IO.mkRef (#[] : Array MessageData)
    let mut steps : Nat := 0
    repeat
      match ← frontierRef.get with
      | [] => break
      | a :: rest =>
        frontierRef.set rest
        steps := steps + 1
        if steps > 20000 then
          throwError "forward_invariant: troppi stati esplorati (>20000)"
        if (← seenRef.get).contains a then
          continue
        if ← isBad a then
          throwError "forward_invariant: l'esplorazione in avanti raggiunge{indentExpr a}\nche è uno degli stati da escludere: quindi è RAGGIUNGIBILE e l'enunciato è falso"
        visitedRef.modify (a :: ·)
        seenRef.modify (·.insert a)
        let goalTy ← withLocalDeclD `p Sty fun p =>
          withLocalDeclD `t TType fun t => do
            mkForallFVars #[p, t]
              (← mkArrow (mkApp3 transE t a p) (← mkAppM ``Frontier #[p]))
        let probe ← mkFreshExprMVar goalTy
        let succsRef ← IO.mkRef (#[] : Array Expr)
        backwardStep probe.mvarId! fun g => do
          let gty ← instantiateMVars (← g.getType)
          unless gty.isAppOfArity ``Frontier 2 do
            throwError "forward_invariant: forma inattesa del goal di esplorazione{indentExpr gty}"
          let X ← normState gty.appArg!
          if X.hasFVar || X.hasMVar then
            throwError "forward_invariant: successore non completamente determinato{indentExpr X}"
          succsRef.modify (·.push X)
          frontierRef.modify (X :: ·)
        if verbose then
          let succs := (← succsRef.get).toList
          if succs.isEmpty then
            traceRef.modify (·.push m!"[{steps}] {a}\n      nessun successore: stato terminale")
          else
            traceRef.modify (·.push (m!"[{steps}] {a}\n      {succs.length} successori:\n"
              ++ MessageData.joinSep (succs.map fun e => m!"        → {e}") m!"\n"))

    let visited := (← visitedRef.get).reverse
    if verbose then
      logInfo (m!"forward_invariant: esplorazione in avanti da `s_init`\n\n"
        ++ MessageData.joinSep (← traceRef.get).toList m!"\n"
        ++ m!"\n\nSTOP: frontiera vuota dopo {steps} passi — l'invariante ha {visited.length} stati, "
        ++ m!"e nessuno di essi è fra quelli da escludere.")
    else
      logInfo m!"forward_invariant: invariante chiuso in avanti di {visited.length} stati (esplorazione: {steps} passi)"

    ---------------------------------------------------------------------------
    -- FASE 2: il certificato
    ---------------------------------------------------------------------------
    let VE ← mkListLit Sty visited
    let hinitTy ← mkAppM ``LTS.init #[lE, sInitE]
    let hmemTy ← mkAppM ``Membership.mem #[VE, sInitE]
    let hclosedTy ← withLocalDeclD `a Sty fun a => do
      let inner ← withLocalDeclD `p Sty fun p =>
        withLocalDeclD `t TType fun t => do
          mkForallFVars #[p, t]
            (← mkArrow (mkApp3 transE t a p) (← mkAppM ``InList #[VE, p]))
      mkForallFVars #[a] (← mkArrow (← mkAppM ``Membership.mem #[VE, a]) inner)
    let hinitM ← mkFreshExprMVar hinitTy
    let hmemM ← mkFreshExprMVar hmemTy
    let hclosedM ← mkFreshExprMVar hclosedTy
    try hinitM.mvarId!.assign (← decideProp hinitTy)
    catch _ =>
      try hinitM.mvarId!.refl
      catch _ =>
        throwError "forward_invariant: non riesco a dimostrare che{indentExpr sInitE}\nè uno stato iniziale"
    hmemM.mvarId!.assign (← decideProp hmemTy)
    let (fs, g1) ← hclosedM.mvarId!.introN 2
    enumMem g1 fs[1]! fun ga =>
      backwardStep ga fun g => do
        let gty ← instantiateMVars (← g.getType)
        if gty.hasFVar then
          throwError "forward_invariant: goal residuo non chiuso{indentExpr gty}"
        g.assign (← decideProp gty)

    let prf ← match single?, pred? with
      | some s0, _ => do
        let hbadTy ← mkArrow (← mkAppM ``Membership.mem #[VE, s0]) (mkConst ``False)
        let hbadM ← mkFreshExprMVar hbadTy
        hbadM.mvarId!.assign (← decideProp hbadTy)
        mkAppOptM ``invariant_certificate
          #[some TType, some lE, some VE, some sInitE, some hinitM, some hmemM,
            some hclosedM, some s0, some hbadM]
      | _, some PE => do
        -- nessuno stato dell'invariante è fra quelli da escludere
        let hdisjTy ← withLocalDeclD `a Sty fun a => do
          mkForallFVars #[a] (← mkArrow (← mkAppM ``Membership.mem #[VE, a])
            (mkApp (mkConst ``Not) (mkApp PE a).headBeta))
        let hdisjM ← mkFreshExprMVar hdisjTy
        let (fs2, g2) ← hdisjM.mvarId!.introN 2
        enumMem g2 fs2[1]! fun g => do
          g.assign (← decideProp (← instantiateMVars (← g.getType)))
        withLocalDeclD `s Sty fun s =>
          withLocalDeclD `hp (mkApp PE s).headBeta fun hp => do
            let hbad ← withLocalDeclD `hsv (← mkAppM ``Membership.mem #[VE, s]) fun hsv => do
              mkLambdaFVars #[hsv] (mkApp (mkApp2 hdisjM s hsv) hp)
            let body ← mkAppOptM ``invariant_certificate
              #[some TType, some lE, some VE, some sInitE, some hinitM, some hmemM,
                some hclosedM, some s, some hbad]
            mkLambdaFVars #[s, hp] body
      | _, _ => throwError "forward_invariant: goal non riconosciuto"
    unless ← isDefEq (← inferType prf) tgt do
      throwError "forward_invariant: impossibile applicare il certificato al goal"
    mainGoal.assign prf
    replaceMainGoal []

end BackwardTactic

/-- `forward_invariant s_init` dimostra `¬ l.reachable s` o
`∀ s, P s → ¬ l.reachable s` esplorando **in avanti** da `s_init`: costruisce
l'insieme degli stati raggiungibili e verifica che nessuno sia fra quelli da
escludere. È il duale di `backward_search`, e conviene quando la chiusura
all'indietro dell'insieme cattivo è molto più grande dell'insieme raggiungibile. -/
elab (name := forwardInvariantTac) "forward_invariant" sInitStx:term : tactic =>
  BackwardTactic.forwardInvariantCore false sInitStx

/-- Come `forward_invariant`, ma stampa l'esplorazione passo per passo. -/
elab (name := forwardInvariantVerboseTac) "forward_invariant?" sInitStx:term : tactic =>
  BackwardTactic.forwardInvariantCore true sInitStx

/-- `backward_search s_init` dimostra un goal `¬ l.reachable s`: va all'indietro
da `s` un passo alla volta invertendo le regole, accumula gli stati in una lista
di stati irraggiungibili, chiude i rami che tornano su stati già in lista
("fatto centro") o che non hanno predecessori ("vinto"), e fallisce se incontra
uno stato iniziale. `s_init` è il testimone che gli stati iniziali esistono. -/
elab (name := backwardSearchTac) "backward_search" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchCore false sInitStx

/-- Come `backward_search`, ma stampa la lista di stati irraggiungibili trovata. -/
elab (name := backwardSearchVerboseTac) "backward_search?" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchCore true sInitStx

/-- `backward_search_all s_init` dimostra un goal `∀ s, P s → ¬ l.reachable s`:
come `backward_search`, ma la ricerca parte da *tutti* gli stati che soddisfano
`P`. Serve quando la proprietà da escludere è una condizione su alcuni campi e
non un singolo stato. -/
elab (name := backwardSearchAllTac) "backward_search_all" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchSetCore false sInitStx

/-- Come `backward_search_all`, ma stampa quello che trova. -/
elab (name := backwardSearchAllVerboseTac) "backward_search_all?" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchSetCore true sInitStx


/-!
# La tattica all'opera su TwoPhaseCommit

Il sistema è quello di `Star/BackwardsInvariants/TwoPhaseCommit.lean`: `twoPC`,
con le regole `pinit1/pinit2` (un partecipante vota), `part1/part2` (il voto
arriva al coordinatore) e `commit` (il coordinatore committa se i due voti
coincidono).

Servono `DecidableEq` sugli stati (la tattica confronta stati concreti e decide
`init`) e `Repr` per stampare i controesempi.
-/

namespace THEORY.TwoPhaseCommit

deriving instance DecidableEq, Repr for PState
deriving instance DecidableEq, Repr for State
deriving instance DecidableEq, Repr for Rule

/-! ## 1. Gli stati che nel file originale hanno richiesto un invariante a mano

`reachable_twoPC_test … test3` sono dimostrati là passando per
`unreachable_set` e `back_reachable_twoPC`, scritti e dimostrati a mano. Qui
sono una riga: la tattica trova che nessuna regola può produrre questi stati,
quindi "non si può andare backward" e ha vinto subito. -/

example : ¬ twoPC.reachable test_state := by backward_search init_state
example : ¬ twoPC.reachable test_state1 := by backward_search init_state
example : ¬ twoPC.reachable test_state2 := by backward_search init_state
example : ¬ twoPC.reachable test_state3 := by backward_search init_state

/-! ## 2. Un esempio con vera induzione backward

Il coordinatore ha ricevuto `false` da p1 e `true` da p2, ma entrambi i
partecipanti hanno votato `false`: il voto di p2 in volo non corrisponde al suo
stato. Qui la ricerca non finisce al primo passo, e usa tutti i pezzi della
procedura:

    ⟨p12c := some false, p22c := some true, p1 := tentative false, p2 := tentative false⟩
      ├─ part1 all'indietro: `p12c` viene sovrascritto, quindi il valore
      │  precedente è libero → tre predecessori (uno è lo stato stesso:
      │  **fatto centro**, il ramo si chiude)
      ├─ ⟨some true, some true, tentative false, tentative false⟩ → nessun
      │  predecessore: **vinto**
      └─ ⟨none, some true, tentative false, tentative false⟩
           └─ pinit1 all'indietro
              └─ ⟨none, some true, empty, tentative false⟩ → nessun
                 predecessore: **vinto**
-/

def vote_mismatch : State :=
  { p12c := some false, p22c := some true, p1 := .tentative false, p2 := .tentative false }

theorem vote_mismatch_unreachable : ¬ twoPC.reachable vote_mismatch := by
  backward_search init_state

/-! ## 3. La proprietà di sicurezza del protocollo

I due partecipanti non possono committare valori diversi. È il caso che esercita
l'inversione adattiva: la regola `commit` ha in conclusione `s.p1.commit`, che
non è un costruttore, quindi `cases` da solo si blocca e la tattica enumera i
campi finché l'inversione riesce. -/

def disagreement : State :=
  { p12c := none, p22c := none, p1 := .committed true, p2 := .committed false }

theorem disagreement_unreachable : ¬ twoPC.reachable disagreement := by
  backward_search? init_state

/-! ## 4. Controprova: su uno stato raggiungibile la tattica fallisce

`test_state4` è quello che nel file originale è rimasto **commentato**, perché
non rientra in `unreachable_set`. E infatti è raggiungibile: la tattica lo
scopre da sola, arrivando all'indietro fino allo stato iniziale. -/

-- example : ¬ twoPC.reachable test_state4 := by backward_search init_state
--
-- backward_search: andando all'indietro si raggiunge lo stato iniziale
--   { p12c := none, p22c := none, p1 := PState.empty, p2 := PState.empty }
-- lo stato di partenza è quindi RAGGIUNGIBILE (...)

/-- Lo stato intermedio: p2 ha votato `true`, il voto non è ancora arrivato. -/
def voted2 : State := { p12c := none, p22c := none, p1 := .empty, p2 := .tentative true }

/-- E in effetti `test_state4` si raggiunge in due passi: p2 vota `true`, poi il
voto arriva al coordinatore. -/
theorem test_state4_reachable : twoPC.reachable test_state4 := by
  intro s hs
  have hsi : s = init_state := by
    obtain ⟨p12c, p22c, p1, p2⟩ := s
    obtain ⟨h1, h2, h3, h4⟩ := hs
    cases p12c <;> cases p22c <;> simp_all [init_state]
  subst hsi
  have step1 : twoPC.atrans init_state voted2 :=
    ⟨.pinit2, Protocol.step_pinit2 (b := true) rfl rfl⟩
  have step2 : twoPC.atrans voted2 test_state4 :=
    ⟨.part2, Protocol.step_part2 (b := true) rfl⟩
  exact ReflTransGen.head step1 (ReflTransGen.single step2)

/-! ## 5. Le prove prodotte dalla tattica sono termini veri

Nessun `sorryAx`: quello che la tattica costruisce è un termine di prova
controllato dal kernel, non un risultato di cui fidarsi. Restano solo i tre
assiomi standard di Lean, ereditati da `backwards_reachable_not_init`. -/

#print axioms vote_mismatch_unreachable
#print axioms disagreement_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end THEORY.TwoPhaseCommit



/-!
# Il modello MI a due cache

## Possedere la linea

MI governa **una linea di cache**. Ogni cache sta in uno dei due `Bstate` di
MI.lean:

* `M` (*Modified*) — quella cache ha la linea ed è l'unica ad averla: può
  leggerla e scriverla perché nessun altro ne ha copia. "Possedere la linea"
  vuol dire essere in `M`;
* `I` (*Invalid*) — non ce l'ha; se le serve deve chiederla.

La proprietà da garantire è **un solo proprietario alla volta**, ed è esattamente
ciò che `twoCachesM` di MI.lean nega.

## I quattro messaggi

Ogni messaggio di MI ha qui il suo flag "ce n'è uno in volo", per ciascuna
delle due direzioni:

| flag       | messaggio di MI.lean      | chi → chi        | porta il token? |
|------------|---------------------------|------------------|-----------------|
| `q0` `q1`  | `CPEvent.rqM`             | cache → parent   | no: è la richiesta |
| `g0` `g1`  | `PCEvent.rsM v`           | parent → cache   | **sì**: è la concessione |
| `v0` `v1`  | `PCEvent.rqIμ`            | parent → cache   | no: è la richiesta di restituzione |
| `r0` `r1`  | `CPEvent.rsIμ v`          | cache → parent   | **sì**: è la restituzione |

I due che portano il token (`g` e `r`) sono i posti 2 e 3 di `MIState.tokens` in
MI.lean:

    CacheState.tokens cs = cs.state.tok                             -- `c`
                         + cs.queue_pc.countP PCEvent.isGrant       -- `g`
                         + cs.queue_cp.countP CPEvent.isRelease     -- `r`

Il token è uno solo, e quei tre posti sono tutti i posti in cui può stare:
dentro una cache, in volo verso una cache, in volo verso il parent.

## La directory

`d0`/`d1` è `s.parent.shared_state i`: cosa il **parent crede** di aver
concesso. È separata da `c0`/`c1` perché i messaggi impiegano tempo — fra la
concessione e la ricezione si ha `d0 = M` ma `c0 = I`, e fra la restituzione e
la sua registrazione si ha `c0 = I` ma `d0 = M`.

## Il giro completo

    cache 0 vuole la linea, ce l'ha la cache 1

    request0      c0=I                       → q0 := true
    invalidate1   q0, d1=M                   → v1 := true      (il parent la richiama alla 1)
    release1      v1, c1=M                   → c1 := I, r1 := true
    recvRelease1  r1                         → d1 := I         (ora la directory è libera)
    grant0        q0, d0=I, d1=I             → d0 := M, g0 := true
    recvGrant0    g0, c0=I                   → c0 := M

## Le semplificazioni rispetto a `MIState n`

Servono perché la tattica enumera stati concreti, e `MIState n` è infinito
(`Value = Nat`, code `List` illimitate).

1. **via i valori.** La proprietà riguarda *chi* possiede, non *cosa* è
   memorizzato: `Value` sparisce da messaggi e cache.
2. **via letture e scritture** (`ld_rs`, `st_rs`): non toccano né lo stato delle
   cache né la directory.
3. **coda ridotta a un booleano**: si tiene solo *se* c'è un messaggio, non
   quanti né con che valore. È fedele finché il protocollo non tiene due
   messaggi dello stesso tipo in volo nella stessa direzione — che è
   precisamente ciò che l'invariante a token di MI.lean garantisce.

Nessun passo è fuso: la restituzione della linea da parte della cache e la sua
registrazione da parte del parent sono due transizioni distinte, come in MI.lean
(`rq_data_not_available`/`downgrade_from_M_rs` da un lato, `downgrade_from_M_rq1`
dall'altro).
-/

namespace MI2

open THEORY

deriving instance DecidableEq for Bstate

/-- Lo stato: due cache, la directory del parent, e i quattro messaggi per
ciascuna direzione. -/
structure St where
  c0 : Bstate   -- `(s.caches 0).state`
  c1 : Bstate   -- `(s.caches 1).state`
  d0 : Bstate   -- `s.parent.shared_state 0`
  d1 : Bstate   -- `s.parent.shared_state 1`
  q0 : Bool     -- `rqM`  richiesta      cache 0 → parent
  q1 : Bool
  g0 : Bool     -- `rsM`  concessione    parent → cache 0   (porta il token)
  g1 : Bool
  v0 : Bool     -- `rqIμ` richiamo       parent → cache 0
  v1 : Bool
  r0 : Bool     -- `rsIμ` restituzione   cache 0 → parent   (porta il token)
  r1 : Bool
deriving DecidableEq, Repr

inductive Rl where
  | request0 | request1          -- la cache chiede la linea
  | grant0 | grant1              -- il parent concede
  | invalidate0 | invalidate1    -- il parent richiama la linea al proprietario
  | recvGrant0 | recvGrant1      -- la cache riceve la concessione
  | release0 | release1          -- la cache restituisce, richiamata
  | evict0 | evict1              -- la cache restituisce, di sua iniziativa
  | recvRelease0 | recvRelease1  -- il parent registra la restituzione
deriving DecidableEq, Repr

/-- Le regole, una per una, con la corrispondenza a MI.lean.

* `request i` — `upgrade_from_I_rq`: una cache invalida chiede la linea, e il
  messaggio `rqM` parte.
* `grant i` — `upgrade_to_M_data_avilable_rq1`: c'è una richiesta **e** la
  directory è tutta libera (`∀ i, shared_state i = I`). Il parent consuma la
  richiesta, si segna `d i := M` e la concessione parte.
* `invalidate j` — `upgrade_to_M_invalid_all`: l'altra cache ha chiesto la linea
  ma la directory dice che ce l'ha `j`; il parent gliela richiama.
* `recvGrant i` — `upgrade_from_I_rs`: la cache processa la concessione e sale
  in `M`.
* `release i` — `downgrade_from_M_rs`: la cache richiamata scende a `I` e la
  restituzione parte. La directory **non** cambia: il parent non lo sa ancora.
* `evict i` — `rq_data_not_available`: uguale, ma di iniziativa della cache
  senza essere stata richiamata.
* `recvRelease i` — `downgrade_from_M_rq1`: il parent processa la restituzione e
  solo qui libera la directory. -/
inductive Step : Rl → St → St → Prop where
  | request0 {s} : s.c0 = .I → Step .request0 s { s with q0 := true }
  | request1 {s} : s.c1 = .I → Step .request1 s { s with q1 := true }
  | grant0 {s} : s.q0 = true → s.d0 = .I → s.d1 = .I →
      Step .grant0 s { s with q0 := false, d0 := .M, g0 := true }
  | grant1 {s} : s.q1 = true → s.d0 = .I → s.d1 = .I →
      Step .grant1 s { s with q1 := false, d1 := .M, g1 := true }
  | invalidate0 {s} : s.q1 = true → s.d0 = .M → Step .invalidate0 s { s with v0 := true }
  | invalidate1 {s} : s.q0 = true → s.d1 = .M → Step .invalidate1 s { s with v1 := true }
  | recvGrant0 {s} : s.g0 = true → s.c0 = .I →
      Step .recvGrant0 s { s with c0 := .M, g0 := false }
  | recvGrant1 {s} : s.g1 = true → s.c1 = .I →
      Step .recvGrant1 s { s with c1 := .M, g1 := false }
  | release0 {s} : s.v0 = true → s.c0 = .M →
      Step .release0 s { s with c0 := .I, v0 := false, r0 := true }
  | release1 {s} : s.v1 = true → s.c1 = .M →
      Step .release1 s { s with c1 := .I, v1 := false, r1 := true }
  | evict0 {s} : s.c0 = .M → Step .evict0 s { s with c0 := .I, r0 := true }
  | evict1 {s} : s.c1 = .M → Step .evict1 s { s with c1 := .I, r1 := true }
  | recvRelease0 {s} : s.r0 = true → Step .recvRelease0 s { s with d0 := .I, r0 := false }
  | recvRelease1 {s} : s.r1 = true → Step .recvRelease1 s { s with d1 := .I, r1 := false }

/-- Nessuno ha la linea, la directory è libera, niente in volo: zero token. -/
def initSt : St := ⟨.I, .I, .I, .I, false, false, false, false, false, false, false, false⟩

def mi2 : LTS Rl where
  S := St
  transitions := Step
  init s := s = initSt
  flushed _ := True

/-- `twoCachesM` di MI.lean, con `n = 2` e gli indici espansi. -/
def twoCachesM (s : St) : Prop := s.c0 = .M ∧ s.c1 = .M

/-! ## La dimostrazione

Perché la proprietà vale, in una frase: all'inizio ci sono **zero token**;
l'unica regola che ne crea uno è `grant`, che nel farlo **si autoblocca** —
scrivendo `d i := M` rende falsa la propria guardia `d0 = I ∧ d1 = I`, quindi
nessun'altra concessione può partire. L'unico modo per riaprirla è
`recvRelease`, che però consuma il token che c'era. Il totale resta ≤ 1, e due
cache in `M` ne vorrebbero 2. **La directory del parent fa da lucchetto.**

`twoCachesM` fissa solo `c0` e `c1` e lascia liberi gli altri dieci campi:
**1024 stati di partenza**. La ricerca all'indietro qui non ce la fa, e non per
un difetto della tattica: la chiusura all'indietro di quell'insieme ha **3408
stati sui 4096** dello spazio, perché da quasi ogni stato "rotto" si arriva a
due proprietari. Gli stati raggiungibili dall'iniziale sono invece **112**.

Quando i due numeri sono così sbilanciati conviene il certificato duale: invece
di un insieme chiuso all'indietro che contiene gli stati cattivi, un insieme
chiuso **in avanti** che contiene quello iniziale e non li contiene. È
`invariant_certificate`, e la tattica è `forward_invariant`. -/

set_option maxHeartbeats 4000000 in
/-- **Tutti gli stati con due cache in `M` sono irraggiungibili**, comunque
siano messi la directory e i messaggi in volo. L'invariante che la tattica
costruisce ha 112 stati, trovati in 369 passi di esplorazione. -/
theorem twoCachesM_unreachable : ∀ s : St, twoCachesM s → ¬ mi2.reachable s := by
  forward_invariant initSt

/-! ## Lo stato `bothM = ⟨M, M, M, I⟩`

    c0 = M   c1 = M      entrambe le cache credono di possedere la linea
    d0 = M   d1 = I      il parent crede di averla data alla 0, e che la 1 non ce l'abbia
    nessun messaggio in volo

È rotto due volte. Nel conto dei token di MI.lean ci sono due token, entrambi
dentro le cache (`tokens 0 = tokens 1 = 1`), e per di più il token della cache 1
**non è registrato dal parent**: è il terzo disgiunto di `unreachable_setM`,
`∃ i, 1 ≤ tokens i ∧ shared_state i = I`, quello che il commento in MI.lean
chiama "il disgiunto decisivo".

Ed è decisivo davvero, perché è la porta del disastro: con `d1 = I` il parent ha
perso di vista la cache 1. Basta che la cache 0 restituisca la linea e il parent
lo registri, e la directory risulta **tutta libera** mentre la cache 1 è ancora
in `M` — a quel punto il parent è pronto a concedere la linea a chiunque
(`bothM_fools_parent`).

I suoi predecessori diretti sono quattro, e vale la pena guardarli:

    c=(I,M) d=(M,I) g0        la cache 0 stava per ricevere la concessione
    c=(M,I) d=(M,I) g1        idem la cache 1
    c=(M,M) d=(M,I) r1        il parent aveva appena registrato una restituzione
    c=(M,M) d=(M,M) r1        della cache 1 — che però è ancora in `M`

La chiusura all'indietro da qui ha **2640 stati**, contro i 4 di `⟨M,M,M,M⟩`:
la ricerca all'indietro è fuori portata, mentre il teorema in avanti lo copre
gratis. -/

/-- Due proprietari, e il parent che ne vede uno solo. -/
def bothM : St := ⟨.M, .M, .M, .I, false, false, false, false, false, false, false, false⟩

theorem bothM_twoCachesM : twoCachesM bothM := ⟨rfl, rfl⟩

/-- **`bothM` è irraggiungibile**: corollario immediato del teorema generale. -/
theorem bothM_unreachable : ¬ mi2.reachable bothM :=
  twoCachesM_unreachable bothM bothM_twoCachesM

/-- **Perché è la porta del disastro.** Da `bothM`, in due passi — la cache 0
sfratta la linea, il parent registra la restituzione — si arriva a directory
completamente libera con la cache 1 ancora in `M`. Da lì il parent concederebbe
la linea a chiunque, creando un secondo proprietario. -/
theorem bothM_fools_parent :
    ReflTransGen mi2.atrans bothM
      ⟨.I, .M, .I, .I, false, false, false, false, false, false, false, false⟩ :=
  ReflTransGen.head ⟨.evict0, Step.evict0 rfl⟩
    (ReflTransGen.single ⟨.recvRelease0, Step.recvRelease0 rfl⟩)

/-! ## Dove invece la ricerca all'indietro si vede bene

Sullo stato "coerente" `⟨M, M, M, M⟩` — due proprietari, ma almeno il parent li
vede entrambi — la chiusura all'indietro ha **4 stati**, e `backward_search?`
stampa tutta la ricerca. La differenza con `bothM` è tutta in quel `d1`: con la
directory a `M` la regola `grant` è bloccata all'indietro, con la directory a
`I` si riapre e la chiusura esplode. -/

/-- Due proprietari, e il parent li vede entrambi. -/
def bothM_dirM : St := ⟨.M, .M, .M, .M, false, false, false, false, false, false, false, false⟩

set_option maxHeartbeats 1000000 in
/-- La traccia: per ogni stato tirato fuori dalla frontiera la tattica dice
quali predecessori ha trovato, se era già nella lista (*fatto centro*) o se non
si può andare indietro (*vinto*), e perché si ferma. Nonostante le quattordici
regole bastano 5 passi e 4 stati: quasi tutte si potano da sole all'indietro,
perché lascerebbero acceso un flag che qui è spento. -/
theorem bothM_dirM_unreachable : ¬ mi2.reachable bothM_dirM := by
  backward_search? initSt

/-! ### Perché `twoCachesM` da sola non basta

Nella traccia il predecessore di `bothM_dirM` ha **una sola** cache in `M`: il
secondo proprietario è un *messaggio*, non una cache. Per questo nessun
predicato sui soli stati delle cache è chiuso all'indietro, ed è il motivo per
cui in MI.lean `back_reachable_MI1` è rimasto `sorry`. La tattica quegli stati se
li aggiunge da sola. -/

/-- La cache 1 possiede la linea, la cache 0 no — ma la concessione per la cache
0 è già in volo. È il `(I + grant rsM, M)` del commento a `back_reachable_MI1`. -/
def grantInFlight : St := ⟨.I, .M, .M, .M, false, false, true, false, false, false, false, false⟩

/-- Non è in `twoCachesM`: una sola cache è in `M`. -/
theorem grantInFlight_not_twoCachesM : ¬ twoCachesM grantInFlight := by
  simp [twoCachesM, grantInFlight]

/-- ...eppure con un passo ci entra: `twoCachesM` non è chiusa all'indietro. -/
theorem grantInFlight_steps_into_twoCachesM : Step .recvGrant0 grantInFlight bothM_dirM :=
  Step.recvGrant0 rfl rfl

set_option maxHeartbeats 1000000 in
/-- La tattica lo copre lo stesso. -/
theorem grantInFlight_unreachable : ¬ mi2.reachable grantInFlight := by
  backward_search initSt

/-! ## Controprova: uno stato raggiungibile viene rifiutato -/

/-- La cache 0 possiede la linea, la directory è d'accordo, niente in volo: è la
situazione normale dopo un giro di handshake. -/
def owned0 : St := ⟨.M, .I, .M, .I, false, false, false, false, false, false, false, false⟩

-- example : ¬ mi2.reachable owned0 := by backward_search? initSt
--
-- ...la ricerca si allarga e poi:
-- STOP: andando all'indietro si raggiunge lo stato iniziale
--   ⟨I, I, I, I, false, …⟩
-- lo stato di partenza è quindi RAGGIUNGIBILE

/-- E infatti si raggiunge in tre passi: la cache chiede, il parent concede, la
cache riceve. -/
theorem owned0_reachable : mi2.reachable owned0 := by
  intro s hs
  have : s = initSt := hs
  subst this
  refine ReflTransGen.head ⟨.request0, Step.request0 rfl⟩
    (ReflTransGen.head ⟨.grant0, Step.grant0 rfl rfl rfl⟩
      (ReflTransGen.single ⟨.recvGrant0, Step.recvGrant0 rfl rfl⟩))

#print axioms twoCachesM_unreachable
#print axioms bothM_unreachable
#print axioms bothM_dirM_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end MI2
