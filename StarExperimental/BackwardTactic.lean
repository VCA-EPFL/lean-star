import StarExperimental.BackwardSearch

/-!
# `backward_search`: la tattica di ricerca backward

Qui l'algoritmo descritto a voce è realizzato come **tattica vera** (un
metaprogramma), da chiamare dentro una dimostrazione:

    theorem bad_not_reachable : ¬ miniMI.reachable bad := by
      backward_search initState

Non serve scrivere nessuna funzione dei predecessori né alcun modello: la
tattica lavora direttamente sulla relazione induttiva dei passi (`MiniStep`),
invertendola con `cases`. La corrispondenza con la descrizione a voce:

* "partendo da uno stato vado backward di uno step" → per lo stato `a` la
  tattica apre il goal `∀ p t, l.transitions t p a → …` e fa `cases` sulla
  transizione: ogni costruttore che può arrivare in `a` produce un
  predecessore concreto (i rami impossibili si chiudono da soli);
* "aggiungo tutti gli stati alla lista di stati irraggiungibili" → la lista
  `visited` mantenuta dalla tattica;
* "se lo stato è già nella lista mi fermo: fatto centro" → il controllo di
  appartenenza prima di esplorare;
* "se no faccio l'induzione backward di nuovo" → il ciclo sulla frontiera;
* "se da uno stato non si può andare backward ho vinto" → `cases` sulla
  transizione non produce nessun sottogoal;
* in più (necessario per la correttezza): se andando backward si incontra uno
  stato *iniziale* la tattica fallisce, perché lo stato di partenza è
  raggiungibile.

Alla fine la tattica chiude il goal applicando `unreachable_certificate` con
la lista trovata, e ridimostra le tre obbligazioni (lo stato di partenza è in
lista, nessuno stato in lista è iniziale, la lista è chiusa all'indietro).

Requisiti sul sistema: l'`LTS` deve essere `@[reducible]`, gli stati devono
avere `DecidableEq` e campi di tipo enumerabile (induttivi a costruttori
senza argomenti, come `Bstate`), e `init` deve essere decidibile.

La variante `backward_search? initState` stampa anche la lista di stati
irraggiungibili trovata.
-/

open THEORY
open Relation
open Lean Meta Elab Tactic

namespace BackwardTactic

/-- Versione generica di `back_reachable_twoPC`: un predicato chiuso all'indietro
di un passo è chiuso lungo tutta la `backwards_reachable_from` di `THEORY`. -/
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

/-- Versione generica di `reachable_twoPC`, via `backwards_reachable_not_init`. -/
theorem unreachable_of_backwards_closed {T : Type} {l : LTS T} {P : l.S → Prop}
    (hstep : ∀ (a p : l.S) (t : T), P a → l.transitions t p a → P p)
    (s_init : l.S) (hinit : l.init s_init) (hninit : ¬ P s_init)
    {s : l.S} (hs : P s) : ¬ l.reachable s := fun hreach =>
  hninit (backwards_closed hstep
    (backwards_reachable_not_init.mpr hreach s_init hinit) hs)

/-- Il certificato che la tattica applica alla fine: la lista `U` trovata dalla
ricerca gioca il ruolo di `unreachable_set`. -/
theorem unreachable_certificate {T : Type} {l : LTS T}
    (U : List l.S) (s_init : l.S) (hinit : l.init s_init)
    {s₀ : l.S} (hmem : s₀ ∈ U)
    (hninit : ∀ s ∈ U, ¬ l.init s)
    (hclosed : ∀ a ∈ U, ∀ (p : l.S) (t : T), l.transitions t p a → p ∈ U) :
    ¬ l.reachable s₀ :=
  unreachable_of_backwards_closed (P := (· ∈ U))
    (fun a p t ha ht => hclosed a ha p t ht)
    s_init hinit (fun hs => hninit s_init hs hinit) hmem

/-- Marcatore usato solo a livello meta per "leggere" i predecessori dai goal
di esplorazione: la tattica apre `∀ p t, trans t p a → BackTag p` e raccoglie
gli `X` dei goal residui `BackTag X`. Il goal non viene mai dimostrato. -/
@[irreducible] def BackTag {α : Type} (_ : α) : Prop := False

/-- `ty` è un tipo enumerabile? (induttivo senza indici, tutti i costruttori
senza argomenti: `Bstate`, `Bool`, ...) -/
def isEnumType (ty : Expr) : MetaM Bool := do
  let ty ← whnfD ty
  let .const n _ := ty.getAppFn | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  if iv.numIndices != 0 then return false
  iv.ctors.allM fun c => do
    let some (.ctorInfo cv) := (← getEnv).find? c | return false
    return cv.numFields == 0

/-- Come `mkDecideProof`, ma valuta davvero `decide p` (con `whnf`) e fallisce
subito se non si riduce a `true` — `mkDecideProof` da solo costruisce il
termine senza controllare e l'errore emergerebbe solo nel kernel. -/
def decideProp (p : Expr) : MetaM Expr := do
  let d ← mkDecide p
  let r ← withDefault <| whnf d
  unless r.isConstOf ``Bool.true do
    throwError "la proposizione{indentExpr p}\nnon si riduce a `true` con `decide`"
  mkDecideProof p

/-- `simp_all` su un goal: `none` se il goal si chiude (ramo impossibile),
altrimenti il goal semplificato. -/
def trySimpAll (g : MVarId) : MetaM (Option MVarId) := do
  try
    let ctx ← Simp.mkContext (config := {})
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let (res, _) ← simpAll g ctx (simprocs := #[← Simp.getSimprocs])
    return res
  catch _ =>
    return some g

/-- Enumera le variabili libere di tipo enumerabile rimaste nel target
(es. un campo non determinato dalla regola, come `d0` in un writeback) e
chiama `leaf` su ogni goal completamente istanziato. -/
partial def splitEnumFVars (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  let next ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let fvars := (collectFVars {} tgt).fvarIds
    let mut found := none
    for fv in fvars do
      if ← isEnumType (← fv.getType) then
        found := some fv
        break
    pure found
  match next with
  | none => leaf g
  | some fv =>
    for sub in ← g.cases fv do
      splitEnumFVars sub.mvarId leaf

/-- Il passo backward simbolico. Su un goal `∀ p t, l.transitions t p a → P p`:
destruttura `p` nei suoi campi, fa `cases` sulla transizione (l'inversione
delle regole: un sottogoal per ogni regola che può arrivare in `a`, i rami
impossibili vengono potati), normalizza con `simp_all`, enumera i campi
rimasti liberi e chiama `leaf` su ogni foglia. Se nessuna regola può arrivare
in `a` ("non si può andare backward") non ci sono foglie: vinto. -/
partial def visitPredecessors (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  let (pF, g1) ← g.intro `p
  let gs ← try pure ((← g1.cases pF).toList.map (·.mvarId)) catch _ => pure [g1]
  for g2 in gs do
    let (fs, g3) ← g2.introN 2
    for sub in ← g3.cases fs[1]! do
      match ← trySimpAll sub.mvarId with
      | none => pure ()
      | some g4 => splitEnumFVars g4 leaf

/-- Su un goal `∀ …` con ipotesi `hm : a ∈ U` (con `U` lista letterale),
enumera i casi `a = u₁, a = u₂, …` e chiama `k` su ciascuno. -/
partial def enumMem (g : MVarId) (hm : FVarId) (k : MVarId → MetaM Unit) : MetaM Unit := do
  for sub in ← g.cases hm do
    if sub.ctorName == ``List.Mem.head then
      k sub.mvarId
    else
      enumMem sub.mvarId sub.fields.back!.fvarId! k

/-- Dimostra l'obbligazione di chiusura all'indietro
`∀ a ∈ U, ∀ p t, l.transitions t p a → p ∈ U`, rifacendo per ogni `a ∈ U`
lo stesso passo backward della fase di ricerca e chiudendo le foglie
(appartenenze fra stati concreti) con `decide`. -/
def proveClosed (g : MVarId) : MetaM Unit := do
  let (fs, g1) ← g.introN 2
  enumMem g1 fs[1]! fun g2 =>
    visitPredecessors g2 fun g3 => do
      let ty ← instantiateMVars (← g3.getType)
      if ty.hasFVar then
        throwError "backward_search: goal residuo non chiuso{indentExpr ty}"
      g3.assign (← decideProp ty)

/-- Il corpo della tattica. -/
def backwardSearchCore (verbose : Bool) (sInitStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    -- il goal deve essere `¬ l.reachable s₀`
    let tgt ← instantiateMVars (← mainGoal.getType)
    let some body := tgt.not?
      | throwError "backward_search: il goal deve avere la forma `¬ l.reachable s`, trovato{indentExpr tgt}"
    unless body.isAppOfArity ``LTS.reachable 3 do
      throwError "backward_search: il goal deve avere la forma `¬ l.reachable s`, trovato{indentExpr body}"
    let args := body.getAppArgs
    let TType := args[0]!
    let lE := args[1]!
    let s0 := args[2]!
    let SPro ← mkAppM ``LTS.S #[lE]
    let Sty ← whnfD SPro
    let sInitE ← elabTermEnsuringType sInitStx (some SPro)
    let transE ← mkAppM ``LTS.transitions #[lE]

    -- FASE 1: la ricerca. `visited` è la lista di stati irraggiungibili,
    -- `frontier` gli stati ancora da esplorare all'indietro.
    let visitedRef ← IO.mkRef ([] : List Expr)
    let frontierRef ← IO.mkRef [← whnfD s0]
    let mut done := false
    for _ in [0:2000] do
      if done then break
      match ← frontierRef.get with
      | [] => done := true
      | a :: rest =>
        frontierRef.set rest
        let visited ← visitedRef.get
        if ← visited.anyM (fun v => isDefEq v a) then
          -- già nella lista: fatto centro, il ramo si chiude
          continue
        -- lo stato non deve essere iniziale, altrimenti è raggiungibile
        let initA ← mkAppM ``LTS.init #[lE, a]
        try
          discard <| decideProp (mkApp (mkConst ``Not) initA)
        catch _ =>
          throwError "backward_search: andando all'indietro si incontra lo stato iniziale{indentExpr a}\nquindi lo stato di partenza è raggiungibile (o `init` non è decidibile)"
        visitedRef.modify (a :: ·)
        -- un passo backward: tutti i predecessori di `a`
        let goalTy ← withLocalDeclD `p Sty fun p =>
          withLocalDeclD `t TType fun t => do
            mkForallFVars #[p, t]
              (← mkArrow (mkApp3 transE t p a) (← mkAppM ``BackTag #[p]))
        let probe ← mkFreshExprMVar goalTy
        visitPredecessors probe.mvarId! fun g => do
          let tgt ← instantiateMVars (← g.getType)
          unless tgt.isAppOfArity ``BackTag 2 do
            throwError "backward_search: forma inattesa del goal di esplorazione{indentExpr tgt}"
          let X := tgt.appArg!
          if X.hasFVar || X.hasMVar then
            throwError "backward_search: predecessore non completamente determinato{indentExpr X}\n(il tipo degli stati ha campi non enumerabili?)"
          frontierRef.modify (X :: ·)
    unless done do
      throwError "backward_search: troppi stati esplorati (>2000): il sistema è davvero finito?"

    let visited := (← visitedRef.get).reverse
    if verbose then
      let lines := visited.map fun e => m!"  • {e}"
      logInfo (m!"backward_search: {visited.length} stati irraggiungibili trovati:\n"
        ++ MessageData.joinSep lines m!"\n")

    -- FASE 2: applica il certificato con la lista trovata e ridimostra le
    -- obbligazioni.
    let UE ← mkListLit Sty visited
    let mkMemE := fun (x : Expr) => mkAppM ``Membership.mem #[UE, x]
    let hinitTy ← mkAppM ``LTS.init #[lE, sInitE]
    let hmemTy ← mkMemE s0
    let hninitTy ← withLocalDeclD `s Sty fun s => do
      mkForallFVars #[s] (← mkArrow (← mkMemE s)
        (mkApp (mkConst ``Not) (← mkAppM ``LTS.init #[lE, s])))
    let hclosedTy ← withLocalDeclD `a Sty fun a => do
      let inner ← withLocalDeclD `p Sty fun p =>
        withLocalDeclD `t TType fun t => do
          mkForallFVars #[p, t] (← mkArrow (mkApp3 transE t p a) (← mkMemE p))
      mkForallFVars #[a] (← mkArrow (← mkMemE a) inner)
    let hinitM ← mkFreshExprMVar hinitTy
    let hmemM ← mkFreshExprMVar hmemTy
    let hninitM ← mkFreshExprMVar hninitTy
    let hclosedM ← mkFreshExprMVar hclosedTy
    let prf ← mkAppOptM ``unreachable_certificate
      #[some TType, some lE, some UE, some sInitE, some hinitM, some s0,
        some hmemM, some hninitM, some hclosedM]
    unless ← isDefEq (← inferType prf) tgt do
      throwError "backward_search: impossibile applicare il certificato al goal"
    -- 1. `s_init` è davvero iniziale
    try
      hinitM.mvarId!.assign (← decideProp hinitTy)
    catch _ =>
      try hinitM.mvarId!.refl
      catch _ =>
        throwError "backward_search: non riesco a dimostrare che{indentExpr sInitE}\nè uno stato iniziale"
    -- 2. lo stato di partenza è nella lista
    hmemM.mvarId!.assign (← decideProp hmemTy)
    -- 3. nessuno stato della lista è iniziale
    hninitM.mvarId!.assign (← decideProp hninitTy)
    -- 4. la lista è chiusa all'indietro
    proveClosed hclosedM.mvarId!
    mainGoal.assign prf
    replaceMainGoal []

end BackwardTactic

/-- `backward_search s_init` dimostra un goal `¬ l.reachable s` con la ricerca
backward: da `s` va indietro di un passo alla volta, accumula gli stati in una
lista di stati irraggiungibili, si ferma sui rami che tornano su stati già in
lista ("fatto centro") o senza predecessori, e fallisce se incontra uno stato
iniziale. `s_init` è un testimone che gli stati iniziali esistono. -/
elab "backward_search" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchCore false sInitStx

/-- Come `backward_search`, ma stampa la lista di stati irraggiungibili trovata. -/
elab "backward_search?" sInitStx:term : tactic =>
  BackwardTactic.backwardSearchCore true sInitStx


/-!
# La tattica all'opera sull'esempio MI

Stesso sistema `MiniMI` di `BackwardSearch.lean` (2 cache M/I con directory),
ma qui NON si usa nessun modello (`miniPre`, `miniModel`, ...): la tattica
inverte direttamente la relazione induttiva `MiniStep`.
-/

namespace MiniMI

/-- Due cache contemporaneamente in `M`: la tattica esplora
`⟨M,M,M,I⟩ ← ⟨I,M,I,I⟩ ← {⟨M,M,M,I⟩ (fatto centro), ⟨M,M,I,I⟩ (senza predecessori)}`
e chiude. -/
theorem bad1_not_reachable_tac : ¬ miniMI.reachable bad1 := by
  backward_search initState

/-- La cache 0 in `M` ma directory a `I`: qui il "fatto centro" avviene
proprio sullo stato di partenza. La variante `?` stampa la lista trovata. -/
theorem bad2_not_reachable_tac : ¬ miniMI.reachable bad2 := by
  backward_search? initState

/-- Tutto a `M`: nessun predecessore, vinto al primo colpo. -/
theorem bad3_not_reachable_tac : ¬ miniMI.reachable bad3 := by
  backward_search initState

-- Su uno stato raggiungibile la tattica fallisce con il messaggio giusto:
--
--   example : ¬ miniMI.reachable good := by backward_search initState
--   -- backward_search: andando all'indietro si incontra lo stato iniziale
--   --   { c0 := Bstate.I, c1 := Bstate.I, d0 := Bstate.I, d1 := Bstate.I }
--   -- quindi lo stato di partenza è raggiungibile (...)

end MiniMI
