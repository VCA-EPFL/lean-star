import StarExperimental.BackwardGen

/-!
# `discover_views`: la ricerca all'indietro che *scopre* le viste cattive

`backward_search_gen` parte da un insieme di viste cattive dato (`SymSetup.bad`) e verifica
che la sua chiusura all'indietro non tocchi la vista iniziale. Qui l'ordine è invertito e
**non si assume nulla**:

1. si prendono *tutte* le viste del tipo finito `V` e per ognuna si fa il passo all'indietro
   sulle regole vere (lo stesso `symStep` di `BackwardGen`): ne esce il grafo astratto dei
   predecessori, una vista → le viste da cui può venire in un passo;
2. per ogni vista `v` si segue il grafo all'indietro, senza mai ripassare da una vista già
   vista:
   * se si incontra la vista dello stato iniziale, `v` è raggiungibile (a livello di viste)
     e il cammino trovato è il testimone;
   * se la chiusura all'indietro si esaurisce senza incontrarla, `v` è **irraggiungibile**:
     è una vista cattiva *scoperta* dall'algoritmo;
3. l'insieme `U` delle viste irraggiungibili è il più grande insieme chiuso all'indietro
   che non contiene la vista iniziale; il certificato `SymSetup.certificateSet` dimostra
   `st.UnreachableSet U`.

Il campo `bad` del setup non entra nella ricerca. Serve solo alla fine, per il confronto:
`bad ⊆ U`? quali viste sono state scoperte ma non dichiarate? quali dichiarate cattive sono
invece raggiungibili (con il cammino)?

Forme del goal accettate:
* `∃ U : List V, st.UnreachableSet U ∧ ∀ v, st.bad v → v ∈ U` — `U` è quello scoperto e la
  seconda parte è il confronto con `bad`;
* `∃ U : List V, st.UnreachableSet U`;
* `st.Unreachable` — come `backward_search_gen`, ma con `U` scoperto.

La sintassi e i parametri (`simp`, `fwd`, `split`, `upd`, `inv`) sono quelli di
`backward_search_gen`; `discover_views?` stampa anche, per ogni vista, i predecessori e
l'esito della chiusura all'indietro.
-/

open Relation
open Lean Meta Elab Tactic

namespace BackwardGen

variable {S T ι V : Type}

/-- "Nessuno stato con una coppia di indici a vista in `U` è raggiungibile da `s0`." -/
def SymSetup.UnreachableSet (st : SymSetup S T ι V) (U : List V) : Prop :=
  ∀ s, (∃ i j, st.view s i j ∈ U) → ¬ ReflTransGen st.atrans st.s0 s

/-- Il certificato senza il vincolo su `bad`: `U` chiuso all'indietro lungo le regole vere e
senza la vista di `s0`. È `SymSetup.certificate` senza `hbad`. -/
theorem SymSetup.certificateSet (st : SymSetup S T ι V) (U : List V)
    (h0 : ∀ i j, st.view st.s0 i j ∉ U)
    (hclosed : ∀ i j, ∀ a ∈ U, ∀ p t s, st.Inv p → st.trans p t s →
        st.view s i j = a → st.view p i j ∈ U) : st.UnreachableSet U := by
  intro s hs hpath
  obtain ⟨i, j, hb⟩ := hs
  have key : ∀ x, ReflTransGen st.atrans st.s0 x → st.Inv x ∧ st.view x i j ∉ U := by
    intro x hx
    induction hx with
    | refl => exact ⟨st.inv0, h0 i j⟩
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      exact ⟨st.inv_step _ _ _ ih.1 ht, fun hmem => ih.2 (hclosed i j _ hmem _ _ _ ih.1 ht rfl)⟩
  exact (key s hpath).2 hb

/-- Da `U` irraggiungibile e `bad ⊆ U` al risultato di `backward_search_gen`. -/
theorem SymSetup.unreachable_of_set (st : SymSetup S T ι V) (U : List V)
    (hU : st.UnreachableSet U) (hbad : ∀ v, st.bad v → v ∈ U) : st.Unreachable :=
  fun s ⟨i, j, hb⟩ => hU s ⟨i, j, hbad _ hb⟩

namespace Discover

open Gen

/-- Stampa compatta di una vista concreta: `⟨I, M, M, zero, zero, true⟩`. -/
partial def compact (e : Expr) : MessageData :=
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if args.isEmpty then m!"{n.getString!}"
    else if n.getString! == "mk" then
      m!"⟨" ++ MessageData.joinSep (args.toList.map compact) m!", " ++ m!"⟩"
    else m!"{e}"
  | _ => m!"{e}"

/-- Un cammino di viste, dalla vista iniziale alla vista data. -/
def showPath (path : List Expr) : MessageData :=
  MessageData.joinSep (path.map compact) m!" → "

/-- Il setup, con i suoi tipi e i suoi campi (senza srotolarne il valore). -/
structure SetupData where
  setupE : Expr
  sTy : Expr
  tTy : Expr
  iTy : Expr
  vTy : Expr
  transE : Expr
  invE : Expr
  viewE : Expr
  badE : Expr
  s0E : Expr

/-- Elabora il setup e ne unifica i parametri (tipicamente `n`) con l'occorrenza di
`st.UnreachableSet` / `st.Unreachable` nel goal. -/
def elabSetup (setupStx : Syntax) (tgt : Expr) : TacticM SetupData := do
  let setupE ← Term.elabTerm setupStx none
  let setupTy ← whnfD (← inferType setupE)
  unless setupTy.isAppOfArity ``SymSetup 4 do
    throwError "discover_views: atteso un `SymSetup`, trovato{indentExpr setupTy}"
  -- l'occorrenza del setup nel goal: sotto l'eventuale `∃ U`
  let isSt (e : Expr) : MetaM Bool :=
    pure (e.isAppOfArity ``SymSetup.UnreachableSet 6 || e.isAppOfArity ``SymSetup.Unreachable 5)
  let unifyIn (body : Expr) : MetaM Unit := do
    match ← findSubM? body isSt with
    | some e =>
      unless ← isDefEq setupE e.getAppArgs[4]! do
        throwError "discover_views: il setup non è quello del goal"
    | none => throwError "discover_views: il goal deve contenere `st.UnreachableSet U` o `st.Unreachable`"
  if tgt.isAppOfArity ``Exists 2 then
    lambdaTelescope tgt.appArg! fun _ body => unifyIn body
  else
    unifyIn tgt
  let setupE ← instantiateMVars setupE
  let setupTy ← instantiateMVars setupTy
  let args := setupTy.getAppArgs
  let setupVal ← whnfD setupE
  let proj (f : Name) : MetaM Expr := do
    let e ← mkAppM f #[setupVal]
    let r ← whnfCore e
    if r == e then whnfD e else pure r
  return { setupE, sTy := args[0]!, tTy := args[1]!, iTy := args[2]!, vTy := args[3]!,
           transE := ← proj ``SymSetup.trans, invE := ← proj ``SymSetup.Inv,
           viewE := ← proj ``SymSetup.view, badE := ← proj ``SymSetup.bad,
           s0E := ← proj ``SymSetup.s0 }

/-- Le viste dello stato iniziale: i campi che dipendono dagli indici (il flag `i = j`) sono
di tipo `Bool`, e si prendono entrambi i valori. -/
def initialViews (sd : SetupData) : MetaM (List Expr) :=
  withLocalDeclD `i sd.iTy fun i => withLocalDeclD `j sd.iTy fun j => do
    let v ← normState (mkApp3 sd.viewE sd.s0E i j)
    let args := v.getAppArgs
    let mut outs : List Expr := [v.getAppFn]
    for a in args do
      if a.hasFVar then
        unless (← whnfD (← inferType a)).isConstOf ``Bool do
          throwError "discover_views: la vista di `s0` dipende dagli indici{indentExpr v}"
        outs := outs.flatMap fun f => [mkApp f (mkConst ``Bool.true), mkApp f (mkConst ``Bool.false)]
      else
        outs := outs.map fun f => mkApp f a
    let mut res : List Expr := []
    for e in outs do res := res ++ [← normState e]
    pure res

/-- **Il passo all'indietro di una vista** (lo stesso di `backward_search_gen`): dimostra
`∀ i j, ∀ p t s, Inv p → trans p t s → 𝒱 s i j = a → 𝒱 p i j ∈ Preds a`
e restituisce `Preds a` (come lista di `Expr` e come letterale) con la prova. -/
def expandView (cfg : Cfg) (ctx : Simp.Context) (sd : SetupData) (a : Expr) :
    TermElabM (List Expr × Expr × Expr) := do
  let mkView (s i j : Expr) : Expr := mkApp3 sd.viewE s i j
  let PM ← mkFreshExprMVar (← mkArrow sd.vTy (mkSort levelZero))
  withLocalDeclD `i sd.iTy fun i => withLocalDeclD `j sd.iTy fun j => do
    let goalTy ← withLocalDeclD `p sd.sTy fun p => withLocalDeclD `t sd.tTy fun t =>
      withLocalDeclD `s sd.sTy fun s => do
        let body ← mkArrow (mkApp sd.invE p) (← mkArrow (mkApp3 sd.transE p t s)
          (← mkArrow (← mkEq (mkView s i j) a) (← mkAppM ``Marker #[PM, mkView p i j])))
        mkForallFVars #[p, t, s] body
    let gM ← mkFreshExprMVar goalTy
    let leaves ← IO.mkRef (#[] : Array (MVarId × Expr))
    symStep cfg ctx gM.mvarId! fun g => do
      let X ← leafView g
      leaves.modify (·.push (g, X))
    let mut preds : List Expr := []
    for (_, X) in ← leaves.get do
      unless preds.contains X do preds := preds ++ [X]
    let predsE ← mkListLit sd.vTy preds
    let PMval ← withLocalDeclD `v sd.vTy fun v => do
      mkLambdaFVars #[v] (← mkAppM ``Membership.mem #[predsE, v])
    PM.mvarId!.assign PMval
    for (g, X) in ← leaves.get do
      let prf ← mkMemProof sd.vTy preds X
      g.withContext do
        unless ← isDefEq (← inferType prf) (← g.getType) do
          throwError "discover_views: la foglia non combacia con i predecessori"
        g.assign prf
    let proof ← instantiateMVars gM
    if proof.hasMVar then throwError "discover_views: la dimostrazione del passo ha metavariabili"
    pure (preds, predsE, ← mkLambdaFVars #[i, j] proof)

/-- **La chiusura all'indietro di una vista** sul grafo astratto, senza ripassare da viste già
viste. `some path` se si incontra una vista iniziale (`path` va dalla vista iniziale ad `a`),
`none` se la chiusura si esaurisce; in entrambi i casi anche la sua dimensione. -/
def backSearch (preds : Std.HashMap Expr (List Expr)) (v0s : List Expr) (a : Expr) :
    Option (List Expr) × Nat := Id.run do
  let mut visited : Std.HashSet Expr := ({} : Std.HashSet Expr).insert a
  -- `parent[p] = x`: `p` è stato raggiunto (all'indietro) da `x`, cioè `p → x` in avanti
  let mut parent : Std.HashMap Expr Expr := {}
  let mut queue : Array Expr := #[a]
  let mut idx := 0
  while idx < queue.size do
    let x := queue[idx]!
    idx := idx + 1
    if v0s.contains x then
      let mut path : List Expr := [x]
      let mut cur := x
      while cur != a do
        match parent[cur]? with
        | some nxt => cur := nxt; path := path ++ [cur]
        | none => break
      return (some path, visited.size)
    for p in preds.getD x [] do
      unless visited.contains p do
        visited := visited.insert p
        parent := parent.insert p x
        queue := queue.push p
  return (none, visited.size)

/-- Il corpo della tattica. -/
def core (cfg : Cfg) (setupStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let tgt ← instantiateMVars (← mainGoal.getType)
    let sd ← elabSetup setupStx tgt
    let ctx ← mkSimpCtx cfg sd.vTy
    let v0s ← initialViews sd
    let mut views : List Expr := []
    for v in ← enumerateType 8 sd.vTy do views := views ++ [← normState v]
    let total := views.length
    -------------------------------------------------------------------------
    -- FASE 1: il passo all'indietro su TUTTE le viste (nessuna assunzione)
    -------------------------------------------------------------------------
    let mut predsMap : Std.HashMap Expr (List Expr) := {}
    let mut proofMap : Std.HashMap Expr (Expr × Expr) := {}   -- vista ↦ (Preds a, hstep_a)
    let mut trace : Array MessageData := #[]
    let mut k : Nat := 0
    for a in views do
      k := k + 1
      let (preds, predsE, prf) ← expandView cfg ctx sd a
      predsMap := predsMap.insert a preds
      proofMap := proofMap.insert a (predsE, prf)
      if cfg.verbose then
        trace := trace.push (m!"[{k}/{total}] {compact a}\n      {preds.length} predecessori: "
          ++ MessageData.joinSep (preds.map compact) m!", ")
    -------------------------------------------------------------------------
    -- FASE 2: per ogni vista, la chiusura all'indietro sul grafo astratto
    -------------------------------------------------------------------------
    let mut U : List Expr := []
    let mut reach : List (Expr × List Expr) := []
    let mut trace2 : Array MessageData := #[]
    for a in views do
      match backSearch predsMap v0s a with
      | (some path, sz) =>
        reach := reach ++ [(a, path)]
        if cfg.verbose then
          trace2 := trace2.push (m!"{compact a}: RAGGIUNGIBILE dopo {sz} viste, cammino "
            ++ showPath path)
      | (none, sz) =>
        U := U ++ [a]
        if cfg.verbose then
          trace2 := trace2.push m!"{compact a}: irraggiungibile (chiusura all'indietro di {sz} viste, mai quella iniziale)"
    -- il confronto con `bad`, se è decidibile
    let mut declared : List Expr := []
    let mut badDecidable := true
    for v in views do
      match ← evalDecidable (mkApp sd.badE v).headBeta with
      | some true => declared := declared ++ [v]
      | some false => pure ()
      | none => badDecidable := false
    let declaredReach := if badDecidable then reach.filter (fun (a, _) => declared.contains a) else []
    let discoveredOnly := if badDecidable then U.filter (fun a => !declared.contains a) else []
    let mut msg := m!"discover_views: {total} viste, nessuna assunzione iniziale.\n"
      ++ m!"  scoperte irraggiungibili: {U.length}   raggiungibili (a livello di viste): {reach.length}\n"
    if badDecidable then
      msg := msg ++ m!"  dichiarate cattive (`bad`): {declared.length}"
      if declaredReach.isEmpty then
        msg := msg ++ m!" — tutte tra le scoperte: `bad ⊆ U`\n"
      else
        msg := msg ++ m!" — {declaredReach.length} sono RAGGIUNGIBILI:\n"
          ++ MessageData.joinSep (declaredReach.map fun (a, p) =>
               m!"    {compact a}  ←  " ++ showPath p) m!"\n" ++ m!"\n"
      msg := msg ++ m!"  scoperte ma non dichiarate: {discoveredOnly.length}\n"
      unless discoveredOnly.isEmpty do
        msg := msg ++ MessageData.joinSep (discoveredOnly.map fun a => m!"    {compact a}") m!"\n" ++ m!"\n"
    else
      msg := msg ++ m!"  (`bad` non è decidibile: nessun confronto)\n"
    msg := msg ++ m!"  raggiungibili, con un cammino dalla vista iniziale:\n"
      ++ MessageData.joinSep (reach.map fun (_, p) => m!"    " ++ showPath p) m!"\n"
    if cfg.verbose then
      msg := msg ++ m!"\n\nI passi all'indietro:\n" ++ MessageData.joinSep trace.toList m!"\n"
        ++ m!"\n\nLe chiusure all'indietro:\n" ++ MessageData.joinSep trace2.toList m!"\n"
    logInfo msg
    -------------------------------------------------------------------------
    -- FASE 3: il certificato per `U`
    -------------------------------------------------------------------------
    let vTy := sd.vTy
    let UE ← mkListLit vTy U
    let memU (x : Expr) : MetaM Expr := mkAppM ``Membership.mem #[UE, x]
    let mkView (s i j : Expr) : Expr := mkApp3 sd.viewE s i j
    -- h0 : ∀ i j, 𝒱 s0 i j ∉ U (come in `backward_search_gen`)
    let h0Ty ← withLocalDeclD `i sd.iTy fun i => withLocalDeclD `j sd.iTy fun j => do
      mkForallFVars #[i, j] (mkApp (mkConst ``Not) (← memU (mkView sd.s0E i j)))
    let h0M ← mkFreshExprMVar h0Ty
    let (fs0, g0) ← h0M.mvarId!.introN 3
    let closeInit (g : MVarId) (hne? : Option FVarId) : TermElabM Unit := g.withContext do
      let mut memDecl : Option LocalDecl := none
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isAppOfArity ``Membership.mem 5 then memDecl := some d
      let some d := memDecl
        | throwError "discover_views: ipotesi di appartenenza non trovata in{indentD (MessageData.ofGoal g)}"
      let ty ← instantiateMVars d.type
      let x := ty.appArg!
      let ctx' ← match hne? with
        | some h => do
          let thms ← ctx.simpTheorems[0]!.add (.fvar h) #[] (mkFVar h)
          pure (ctx.setSimpTheorems #[thms])
        | none => pure ctx
      let (r, _) ← Simp.main x ctx' (methods := ← Simp.mkDefaultMethods)
      let heq ← r.getProof
      let x'' ← normState r.expr
      if x''.hasFVar then
        throwError "discover_views: la vista di `s0` non si riduce{indentExpr x''}"
      let hn ← decideProp (mkApp (mkConst ``Not) (← memU x''))
      let PU ← withLocalDeclD `v vTy fun v => do mkLambdaFVars #[v] (← memU v)
      let mem' ← mkAppM ``Eq.mp #[← mkCongrArg PU heq, d.toExpr]
      let prf ← mkAppOptM ``absurd #[none, some (mkConst ``False), some mem', some hn]
      g.assign prf
    let (pos0, neg0) ← g0.withContext do
      g0.byCases (← mkEq (mkFVar fs0[0]!) (mkFVar fs0[1]!)) `hij
    let posGoals ← pos0.mvarId.withContext do
      let hname ← pos0.fvarId.getUserName
      runTac pos0.mvarId (← `(tactic| subst $(mkIdent hname):ident))
    for g in posGoals do closeInit g none
    closeInit neg0.mvarId (some neg0.fvarId)
    -- hclosed : ∀ i j, ∀ a ∈ U, ∀ p t s, Inv p → trans p t s → 𝒱 s i j = a → 𝒱 p i j ∈ U
    let hclosedTy ← withLocalDeclD `i sd.iTy fun i => withLocalDeclD `j sd.iTy fun j => do
      withLocalDeclD `a vTy fun a => do
      let memA ← memU a
      withLocalDeclD `ha memA fun ha => do
        let inner ← withLocalDeclD `p sd.sTy fun p => withLocalDeclD `t sd.tTy fun t =>
          withLocalDeclD `s sd.sTy fun s => do
            let body ← mkArrow (mkApp sd.invE p) (← mkArrow (mkApp3 sd.transE p t s)
              (← mkArrow (← mkEq (mkView s i j) a) (← memU (mkView p i j))))
            mkForallFVars #[p, t, s] body
        mkForallFVars #[i, j, a, ha] inner
    -- `Preds a ⊆ U`, per costruttori: vale perché `U` è chiuso all'indietro per costruzione
    let subsetProof (preds : List Expr) : MetaM Expr := do
      let PU ← withLocalDeclD `x vTy fun x => do mkLambdaFVars #[x] (← memU x)
      let rec go : List Expr → MetaM Expr
        | [] => pure (mkAppN (mkConst ``forall_mem_nil') #[vTy, PU])
        | y :: rest => do
          let restE ← mkListLit vTy rest
          let hy ← mkMemProof vTy U y
          let hrest ← go rest
          pure (mkAppN (mkConst ``forall_mem_cons') #[vTy, PU, y, restE, hy, hrest])
      go preds
    let hclosedM ← withLocalDeclD `i sd.iTy fun i => withLocalDeclD `j sd.iTy fun j => do
        let Q ← withLocalDeclD `a vTy fun a => do
          let inner ← withLocalDeclD `p sd.sTy fun p => withLocalDeclD `t sd.tTy fun t =>
            withLocalDeclD `s sd.sTy fun s => do
              let body ← mkArrow (mkApp sd.invE p) (← mkArrow (mkApp3 sd.transE p t s)
                (← mkArrow (← mkEq (mkView s i j) a) (← memU (mkView p i j))))
              mkForallFVars #[p, t, s] body
          mkLambdaFVars #[a] inner
        let qProof (a : Expr) : MetaM Expr := do
          let some (predsE, hstep) := proofMap[a]?
            | throwError "discover_views: manca il passo della vista {compact a}"
          let preds := (predsE.listLit?.map (·.2)).getD []
          let sub ← subsetProof preds
          withLocalDeclD `p sd.sTy fun p => withLocalDeclD `t sd.tTy fun t =>
            withLocalDeclD `s sd.sTy fun s => do
              withLocalDeclD `hinv (mkApp sd.invE p) fun hinv =>
              withLocalDeclD `hst (mkApp3 sd.transE p t s) fun hst => do
                let hvTy ← mkEq (mkView s i j) a
                withLocalDeclD `hv hvTy fun hv => do
                  let hs := mkAppN hstep #[i, j, p, t, s, hinv, hst, hv]
                  let body := mkApp2 sub (mkView p i j) hs
                  mkLambdaFVars #[p, t, s, hinv, hst, hv] body
        let rec chain : List Expr → MetaM Expr
          | [] => pure (mkAppN (mkConst ``forall_mem_nil') #[vTy, Q])
          | a :: rest => do
            let restE ← mkListLit vTy rest
            let hq ← qProof a
            let hrest ← chain rest
            pure (mkAppN (mkConst ``forall_mem_cons') #[vTy, Q, a, restE, hq, hrest])
        let body ← chain U
        mkLambdaFVars #[i, j] body
    unless ← isDefEq (← inferType hclosedM) hclosedTy do
      throwError "discover_views: l'obbligazione di chiusura non combacia"
    let certSet := mkAppN (mkConst ``SymSetup.certificateSet)
      #[sd.sTy, sd.tTy, sd.iTy, vTy, sd.setupE, UE, h0M, hclosedM]
    -- hbad : ∀ v, bad v → v ∈ U (solo se il goal lo chiede)
    let mkHbad : TacticM Expr := do
      unless badDecidable do
        throwError "discover_views: il predicato `bad` non è decidibile, non posso confrontarlo con `U`"
      unless declaredReach.isEmpty do
        throwError (m!"discover_views: {declaredReach.length} viste dichiarate cattive sono raggiungibili a livello di viste "
          ++ m!"(bug del modello, o vista troppo grossolana):\n"
          ++ MessageData.joinSep (declaredReach.map fun (a, p) => m!"  {compact a}  ←  " ++ showPath p) m!"\n")
      let hbadTy ← withLocalDeclD `v vTy fun v => do
        mkForallFVars #[v] (← mkArrow (mkApp sd.badE v).headBeta (← memU v))
      let hbadM ← mkFreshExprMVar hbadTy
      let (_, gb) ← hbadM.mvarId!.intro `v
      splitFiniteNoSimp gb fun g => g.withContext do
        let (hF, g1) ← g.intro `hp
        g1.withContext do
          let gty1 ← instantiateMVars (← g1.getType)
          let hpTy ← instantiateMVars (← hF.getType)
          let v ← normState gty1.appArg!
          match ← evalDecidable hpTy with
          | some true => g1.assign (← mkMemProof vTy U v)
          | some false =>
            let hn ← decideProp (mkApp (mkConst ``Not) hpTy)
            g1.assign (← mkAppOptM ``absurd #[none, some gty1, some (mkFVar hF), some hn])
          | none => throwError "discover_views: predicato cattivo non decidibile su{indentExpr v}"
      instantiateMVars hbadM
    -- il goal
    if tgt.isAppOfArity ``Exists 2 then
      let pred := tgt.appArg!
      let body := (mkApp pred UE).headBeta
      let prfBody ←
        if body.isAppOfArity ``And 2 then
          let A := body.appFn!.appArg!
          let B := body.appArg!
          unless ← isDefEq (← inferType certSet) A do
            throwError "discover_views: la prima parte del goal deve essere `st.UnreachableSet U`, trovato{indentExpr A}"
          let hbad ← mkHbad
          unless ← isDefEq (← inferType hbad) B do
            throwError "discover_views: la seconda parte del goal deve essere `∀ v, st.bad v → v ∈ U`, trovato{indentExpr B}"
          mkAppM ``And.intro #[certSet, hbad]
        else
          unless ← isDefEq (← inferType certSet) body do
            throwError "discover_views: il goal deve essere `∃ U, st.UnreachableSet U`, trovato{indentExpr body}"
          pure certSet
      let prf ← mkAppOptM ``Exists.intro #[none, some pred, some UE, some prfBody]
      unless ← isDefEq (← inferType prf) tgt do
        throwError "discover_views: la dimostrazione non combacia con il goal"
      mainGoal.assign prf
    else if tgt.isAppOfArity ``SymSetup.Unreachable 5 then
      let hbad ← mkHbad
      let prf := mkAppN (mkConst ``SymSetup.unreachable_of_set)
        #[sd.sTy, sd.tTy, sd.iTy, vTy, sd.setupE, UE, certSet, hbad]
      unless ← isDefEq (← inferType prf) tgt do
        throwError "discover_views: la dimostrazione non combacia con il goal"
      mainGoal.assign prf
    else
      throwError "discover_views: il goal deve essere `∃ U, st.UnreachableSet U [∧ ∀ v, st.bad v → v ∈ U]` o `st.Unreachable`"
    replaceMainGoal []

end Discover

syntax (name := discoverViewsTac) "discover_views" term:max
  " simp " "[" ident,* "]" " fwd " "[" ident,* "]" " split " ident ident " upd " ident
  " inv " "[" ident,* "]" : tactic
syntax (name := discoverViewsVerboseTac) "discover_views?" term:max
  " simp " "[" ident,* "]" " fwd " "[" ident,* "]" " split " ident ident " upd " ident
  " inv " "[" ident,* "]" : tactic

@[tactic discoverViewsTac] def Discover.evalTac : Tactic := fun stx => do
  match stx with
  | `(tactic| discover_views $setup simp [$simps,*] fwd [$fwds,*] split $spl $fn upd $updS inv [$invs,*]) =>
    let cfg ← Gen.parseCfg false simps.getElems fwds.getElems spl fn updS invs.getElems
    Discover.core cfg setup
  | _ => throwUnsupportedSyntax

@[tactic discoverViewsVerboseTac] def Discover.evalTacVerbose : Tactic := fun stx => do
  match stx with
  | `(tactic| discover_views? $setup simp [$simps,*] fwd [$fwds,*] split $spl $fn upd $updS inv [$invs,*]) =>
    let cfg ← Gen.parseCfg true simps.getElems fwds.getElems spl fn updS invs.getElems
    Discover.core cfg setup
  | _ => throwUnsupportedSyntax

end BackwardGen
