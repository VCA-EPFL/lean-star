import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# `backward_search_gen`: ricerca backward con stati generalizzati

La tattica di `Tatic.lean` lavora su stati concreti di un tipo finito. Questa la
generalizza a sistemi con stati infiniti: uno "stato" della lista è una **vista**
(un valore di un tipo finito `V`, calcolato da `view : S → ι → ι → V` su una coppia di
indici), due stati sono "simili" se hanno la stessa vista, e il passo backward si fa
**sulle regole vere** del sistema, invertendole con `cases` su uno stato simbolico
vincolato solo dalla sua vista. Il certificato (`SymSetup.certificate`) è l'induzione
backward per il predicato `∃ i j, view s i j ∈ U`, con un invariante in avanti `Inv`
che il passo può assumere sul predecessore.

Il file è indipendente dal sistema: MI.lean lo importa e fornisce la vista, l'insieme
cattivo, l'invariante e i lemmi `simp`/"in avanti" sui suoi dati (vedi `new_backward_tatic`
in MI.lean). Dettagli e trappole sono nei commenti delle singole funzioni.
-/

open Relation
open Lean Meta Elab Tactic

namespace BackwardGen

/-! ## Il certificato generico -/

/-- Tutto ciò che serve alla tattica su un sistema con stati `S`, etichette `T`,
indici `ι` e viste (finite) `V`. -/
structure SymSetup (S T ι V : Type) where
  trans : S → T → S → Prop
  Inv : S → Prop
  inv_step : ∀ p t s, Inv p → trans p t s → Inv s
  view : S → ι → ι → V
  bad : V → Prop
  s0 : S
  inv0 : Inv s0

variable {S T ι V : Type}

def SymSetup.atrans (st : SymSetup S T ι V) : S → S → Prop := fun a b => ∃ t, st.trans a t b

/-- "Nessuno stato con una coppia di indici a vista cattiva è raggiungibile da `s0`." -/
def SymSetup.Unreachable (st : SymSetup S T ι V) : Prop :=
  ∀ s, (∃ i j, st.bad (st.view s i j)) → ¬ ReflTransGen st.atrans st.s0 s

/-- Il certificato: `U` (lista di viste) è chiusa all'indietro lungo le regole vere,
non contiene la vista di `s0`, e contiene tutte le viste cattive. -/
theorem SymSetup.certificate (st : SymSetup S T ι V) (U : List V)
    (h0 : ∀ i j, st.view st.s0 i j ∉ U)
    (hclosed : ∀ i j, ∀ a ∈ U, ∀ p t s, st.Inv p → st.trans p t s →
        st.view s i j = a → st.view p i j ∈ U)
    (hbad : ∀ v, st.bad v → v ∈ U) : st.Unreachable := by
  intro s hs hpath
  obtain ⟨i, j, hb⟩ := hs
  have key : ∀ x, ReflTransGen st.atrans st.s0 x → st.Inv x ∧ st.view x i j ∉ U := by
    intro x hx
    induction hx with
    | refl => exact ⟨st.inv0, h0 i j⟩
    | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      exact ⟨st.inv_step _ _ _ ih.1 ht, fun hmem => ih.2 (hclosed i j _ hmem _ _ _ ih.1 ht rfl)⟩
  exact (key s hpath).2 (hbad _ hb)

/-- Segnaposto per la fase di ricerca: `P` è una metavariabile che la tattica assegna
quando ha esplorato tutti i rami di una vista (`fun v => v ∈ predecessori`), così ogni
foglia si chiude con una prova di appartenenza per costruttori. -/
def Marker {V : Type} (P : V → Prop) (v : V) : Prop := P v

/-- `∀ x ∈ l, P x` costruito elemento per elemento (termini piatti, senza `cases`). -/
theorem forall_mem_cons' {α : Type} (P : α → Prop) (a : α) (l : List α) (h : P a)
    (hl : ∀ x, x ∈ l → P x) : ∀ x, x ∈ a :: l → P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hl x hx

theorem forall_mem_nil' {α : Type} (P : α → Prop) : ∀ x, x ∈ ([] : List α) → P x := by
  intro x hx; simp at hx

/-- Contatore saturo: `0`, `1`, "almeno 2". -/
inductive Cnt where
  | zero | one | many
deriving DecidableEq, Repr

def Cnt.ofCount : Nat → Cnt
  | 0 => .zero
  | 1 => .one
  | _ => .many

/-- Il lemma con cui la tattica spezza un contatore simbolico. -/
theorem Cnt.ofCount_cases (e : Nat) :
    (Cnt.ofCount e = .zero ∧ e = 0) ∨ (Cnt.ofCount e = .one ∧ e = 1)
      ∨ (Cnt.ofCount e = .many ∧ 2 ≤ e) := by
  match e with
  | 0 => exact Or.inl ⟨rfl, rfl⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | _ + 2 => exact Or.inr (Or.inr ⟨rfl, by omega⟩)

@[simp] theorem Cnt.ofCount_eq_zero (e : Nat) : Cnt.ofCount e = .zero ↔ e = 0 := by
  match e with
  | 0 => simp [Cnt.ofCount]
  | 1 => simp [Cnt.ofCount]
  | _ + 2 => simp [Cnt.ofCount]

@[simp] theorem Cnt.ofCount_eq_one (e : Nat) : Cnt.ofCount e = .one ↔ e = 1 := by
  match e with
  | 0 => simp [Cnt.ofCount]
  | 1 => simp [Cnt.ofCount]
  | _ + 2 => simp [Cnt.ofCount]

@[simp] theorem Cnt.ofCount_eq_many (e : Nat) : Cnt.ofCount e = .many ↔ 2 ≤ e := by
  match e with
  | 0 => simp [Cnt.ofCount]
  | 1 => simp [Cnt.ofCount]
  | _ + 2 => simp [Cnt.ofCount]


/-! ## Utilità meta (copiate da `Tatic.lean`, che importa MI.lean e qui non si può usare) -/

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

/-- La prima variabile libera del target che ha tipo finito (candidata da
enumerare). -/
def findFiniteFVar (g : MVarId) : MetaM (Option FVarId) :=
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    (collectFVars {} tgt).fvarIds.findM? fun fv => do
      isFiniteType 6 (← fv.getType)

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

/-! ## La tattica -/

namespace Gen


structure Cfg where
  simps : Array Name
  fwds : Array Name
  splitLemma : Name
  splitFn : Name
  updFn : Name
  invs : Array Name
  verbose : Bool

/-- Il simp set: **non** quello di default (troppo lento, e con lemmi come
`List.countP_eq_zero` che distruggono gli atomi aritmetici che servono a `omega`), ma
solo i lemmi dati dall'utente (per le definizioni, le loro equazioni) più un pugno di
lemmi logici. I simproc di default (costruttori distinti, `if`, letterali) restano. -/
def coreSimpLemmas : Array Name := #[
  ``eq_self_iff_true, ``Bool.true_eq_false, ``Bool.false_eq_true, ``if_true, ``if_false,
  ``decide_true, ``decide_false, ``decide_eq_true_eq,
  ``decide_eq_false_iff_not, ``Bool.not_eq_true, ``Bool.not_eq_false,
  ``ne_eq, ``not_false_eq_true, ``not_true_eq_false, ``and_self, ``and_true, ``true_and,
  ``and_false, ``false_and, ``implies_true, ``true_implies, ``false_implies, ``forall_and,
  ``and_imp, ``Option.some.injEq, ``Nat.add_zero, ``Nat.zero_add, ``ite_true, ``ite_false,
  ``iff_self, ``imp_self, ``forall_const, ``true_or, ``or_true, ``false_or, ``or_false,
  ``not_and, ``forall_eq, ``forall_eq', ``exists_eq, ``exists_eq', ``Bool.not_eq_true,
  ``Bool.not_eq_false, ``decide_eq_true_eq, ``List.countP_nil, ``List.countP_cons,
  ``List.countP_append]

def mkSimpCtx (cfg : Cfg) (viewTy : Expr) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  let addThm (thms : SimpTheorems) (n : Name) : MetaM SimpTheorems := do
    match (← getConstInfo n) with
    | .thmInfo _ => thms.addConst n
    | _ =>
      match ← getEqnsFor? n with
      | some eqns => eqns.foldlM (fun t e => t.addConst e) thms
      | none => thms.addDeclToUnfold n
  for n in coreSimpLemmas do
    if (← getEnv).contains n then thms ← addThm thms n
  -- l'iniettività del costruttore delle viste
  if let .const vn _ := viewTy.getAppFn then
    let inj := vn ++ `mk ++ `injEq
    if (← getEnv).contains inj then thms ← thms.addConst inj
  for n in cfg.simps do thms ← addThm thms n
  Simp.mkContext (config := {}) (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

def trySimpAll (ctx : Simp.Context) (g : MVarId) : MetaM (Option MVarId) := do
  tryCatchRuntimeEx
    (do let (res, _) ← simpAll g ctx (simprocs := #[← Simp.getSimprocs]); return res)
    (fun _ => return some g)

/-- Enumera le variabili di tipo finito del target con `cases`, senza `simp`
(il target può contenere il letterale di `U`, su cui `simp` sfonda la ricorsione). -/
partial def splitFiniteNoSimp (g : MVarId) (leaf : MVarId → MetaM Unit) : MetaM Unit := do
  match ← findFiniteFVar g with
  | none => leaf g
  | some fv =>
    for sub in ← g.cases fv do splitFiniteNoSimp sub.mvarId leaf

def runTac (g : MVarId) (stx : Syntax) : TermElabM (List MVarId) :=
  Tactic.run g (Tactic.evalTactic stx)

/-- Il primo sottotermine (senza variabili legate libere) che soddisfa `p`. -/
partial def findSubM? (e : Expr) (p : Expr → MetaM Bool) : MetaM (Option Expr) := do
  if !e.hasLooseBVars then
    if ← p e then return some e
  match e with
  | .app f a => (do if let some r ← findSubM? f p then return some r else findSubM? a p)
  | .lam _ d b _ => (do if let some r ← findSubM? d p then return some r else findSubM? b p)
  | .forallE _ d b _ => (do if let some r ← findSubM? d p then return some r else findSubM? b p)
  | .letE _ t v b _ => (do
      if let some r ← findSubM? t p then return some r
      if let some r ← findSubM? v p then return some r
      findSubM? b p)
  | .mdata _ b => findSubM? b p
  | .proj _ _ b => findSubM? b p
  | _ => return none

/-- Il nome della costante in testa a un'ipotesi, se c'è. -/
def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

/-- Inverte ricorsivamente tutte le ipotesi la cui testa è una delle relazioni in
`cfg.invs` (`mi_step_internal`, poi `cache_mi_step_internal` / `parent_mi_step`). -/
partial def invertAll (cfg : Cfg) (g : MVarId) (k : MVarId → TermElabM Unit) : TermElabM Unit :=
  g.withContext do
    let mut target : Option FVarId := none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some n := headConst? (← instantiateMVars d.type) then
        if cfg.invs.contains n then target := some d.fvarId; break
    match target with
    | none => k g
    | some fv =>
      let subs ← g.cases fv
      for sub in subs do invertAll cfg sub.mvarId k

/-- Aggiunge, per ogni ipotesi e ogni lemma in avanti, l'istanza del lemma se tipa. -/
def addForward (cfg : Cfg) (g : MVarId) : TermElabM MVarId := do
  let decls ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      out := out.push d.toExpr
    pure out
  let mut g := g
  for h in decls do
    for lem in cfg.fwds do
      let r? ← g.withContext do
        try
          let val ← mkAppM lem #[h]
          pure (some (val, ← inferType val))
        catch _ => pure none
      if let some (val, ty) := r? then
        let g' ← g.assert `hfwd ty val
        let (_, g'') ← g'.intro1P
        g := g''
  return g

/-- Cerca un'applicazione `upd q _ _ k` con `q`, `k` variabili distinte non ancora
decise nel contesto. -/
def findIndexSplit (cfg : Cfg) (g : MVarId) : MetaM (Option (Expr × Expr)) := g.withContext do
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    exprs := exprs.push (← instantiateMVars d.type)
  let decided (a b : Expr) : MetaM Bool := do
    for d in ← getLCtx do
      let ty ← instantiateMVars d.type
      let ty : Expr := (ty.not?).getD ty
      let pair : Option (Expr × Expr) :=
        match ty.eq? with
        | some (_, x, y) => some (x, y)
        | none => match ty.ne? with
          | some (_, x, y) => some (x, y)
          | none => none
      if let some (x, y) := pair then
        if (x == a && y == b) || (x == b && y == a) then return true
    return false
  for e in exprs do
    let found ← findSubM? e fun sub => do
      if sub.isApp && sub.getAppFn.isConstOf cfg.updFn then
        let args := sub.getAppArgs
        if args.size ≥ 4 then
          let q := args[args.size - 4]!
          let k := args[args.size - 1]!
          if q.isFVar && k.isFVar && q != k then
            return !(← decided q k)
      return false
    if let some sub := found then
      let args := sub.getAppArgs
      return some (args[args.size - 4]!, args[args.size - 1]!)
  return none

/-- Cerca nel goal un `splitFn e` con `e` non numerale. -/
def findCountSplit (cfg : Cfg) (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let found ← findSubM? tgt fun sub => do
    if sub.isApp && sub.getAppFn.isConstOf cfg.splitFn && sub.getAppNumArgs == 1 then
      let e : Expr := sub.appArg!
      return ((e.nat?).isNone && !e.hasLooseBVars)
    return false
  return found.map (·.appArg!)

/-- Cerca nel goal `Marker ?P X` un sottotermine di `X` di tipo finito che non sia un
costruttore applicato (e non sia `splitFn _`). -/
def findFiniteSplit (cfg : Cfg) (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  unless tgt.isAppOfArity ``Marker 3 do return none
  let X := tgt.appArg!
  let env ← getEnv
  findSubM? X fun sub => do
    if sub.hasLooseBVars then return false
    if sub.isApp && sub.getAppFn.isConstOf cfg.splitFn then return false
    if let some n := headConst? sub then
      if env.isConstructor n then return false
    if !sub.hasFVar then return false
    let ty ← inferType sub
    isFiniteType 6 ty

def tryOmega (g : MVarId) : TermElabM Bool := do
  try
    let gs ← runTac g (← `(tactic| omega))
    return gs.isEmpty
  catch _ => return false

/-- Spezza un'ipotesi `A ∧ B ∧ …` in ipotesi separate (così `simp_all`, che semplifica
ogni congiunto nel contesto degli altri, non le cancella come duplicate). -/
partial def splitAnds (g : MVarId) (fv : FVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← fv.getType))
  if ty.isAppOfArity ``And 2 then
    let subs ← g.cases fv
    match subs with
    | #[sub] =>
      let fields := sub.fields
      if fields.size == 2 then
        let g1 ← splitAnds sub.mvarId fields[0]!.fvarId!
        splitAnds g1 fields[1]!.fvarId!
      else pure sub.mvarId
    | _ => pure g
  else pure g

/-- Dopo `simp_all`: sostituisce le uguaglianze fra variabili rimaste nel contesto. -/
partial def substVarEqs (g : MVarId) : TermElabM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, x, y) := ty.eq? then
      if x.isFVar && y.isFVar && x != y then
        let gs ← runTac g (← `(tactic| subst $(mkIdent d.userName):ident))
        match gs with
        | [g'] => return ← substVarEqs g'
        | _ => pure ()
  return g

/-- **Il passo backward generalizzato.** Goal: `Inv p → trans p t s → 𝒱 s = a → Marker ?P (𝒱 p)`
con `p t s` già introdotte. Inverte, aggiunge i fatti in avanti, e poi alterna
`simp_all` con gli spezzamenti (indici, contatori, campi finiti) finché ogni ramo o è
contraddittorio o ha la vista del predecessore completamente determinata. -/
partial def refineLeaf (cfg : Cfg) (ctx : Simp.Context) (g : MVarId)
    (leaf : MVarId → TermElabM Unit) : TermElabM Unit := do
  match ← trySimpAll ctx g with
  | none => return
  | some g =>
    let g ← substVarEqs g
    if let some (a, b) ← findIndexSplit cfg g then
      let (pos, neg) ← g.byCases (← mkEq a b) `hidx
      -- ramo `a = b`: sostituisce
      let posGoals ← pos.mvarId.withContext do
        let hname ← pos.fvarId.getUserName
        runTac pos.mvarId (← `(tactic| subst $(mkIdent hname):ident))
      for g' in posGoals do refineLeaf cfg ctx g' leaf
      -- ramo `a ≠ b`: aggiunge anche `b ≠ a`
      let negG ← neg.mvarId.withContext do
        let hne ← mkAppM ``Ne.symm #[mkFVar neg.fvarId]
        let g1 ← neg.mvarId.assert `hidx' (← inferType hne) hne
        let (_, g2) ← g1.intro1P
        pure g2
      refineLeaf cfg ctx negG leaf
      return
    if let some e ← findCountSplit cfg g then
      -- prima prova a *decidere* il contatore con `omega` dalle ipotesi
      let decided ← g.withContext do
        let cands : Array (Name × Expr) := #[
          (cfg.splitLemma.getPrefix ++ `ofCount_eq_zero, ← mkEq e (mkNatLit 0)),
          (cfg.splitLemma.getPrefix ++ `ofCount_eq_one, ← mkEq e (mkNatLit 1)),
          (cfg.splitLemma.getPrefix ++ `ofCount_eq_many, ← mkAppM ``LE.le #[mkNatLit 2, e])]
        let mut res : Option Expr := none
        for (lem, prop) in cands do
          if res.isSome then break
          unless (← getEnv).contains lem do continue
          let m ← mkFreshExprMVar prop
          if ← tryOmega m.mvarId! then
            let iff ← mkAppM lem #[e]
            res := some (← mkAppM ``Iff.mpr #[iff, ← instantiateMVars m])
        pure res
      if let some h := decided then
        let r ← g.rewrite (← g.getType) h
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        refineLeaf cfg ctx g' leaf
        return
      let eStx ← g.withContext (Term.exprToSyntax e)
      let gs ← runTac g (← `(tactic|
        obtain ⟨hcnt, hcnt'⟩ | ⟨hcnt, hcnt'⟩ | ⟨hcnt, hcnt'⟩ := $(mkIdent cfg.splitLemma):ident $eStx))
      for g' in gs do
        let gs2 ← (do
          try runTac g' (← `(tactic| rw [hcnt]))
          catch _ => pure [g'])
        for g'' in gs2 do refineLeaf cfg ctx g'' leaf
      return
    if let some e ← findFiniteSplit cfg g then
      let eStx ← g.withContext (Term.exprToSyntax e)
      let gs ← runTac g (← `(tactic| cases hfin : $eStx))
      for g' in gs do refineLeaf cfg ctx g' leaf
      return
    if ← tryOmega g then return
    leaf g

partial def symStep (cfg : Cfg) (ctx : Simp.Context) (g : MVarId)
    (leaf : MVarId → TermElabM Unit) : TermElabM Unit := do
  let (fvs, g) ← g.introN 6 [`p, `t, `s, `hinv, `h, `hv]
  -- `hv : 𝒱 s i j = a` → un `simp` NON contestuale (a differenza di `simp_all`, non usa
  -- i congiunti l'uno contro l'altro) e poi un'ipotesi per campo
  let g ← g.withContext do
    let hv := fvs[5]!
    let (r, _) ← Simp.main (← instantiateMVars (← hv.getType)) ctx (methods := ← Simp.mkDefaultMethods)
    match ← applySimpResultToLocalDecl g hv r (mayCloseGoal := true) with
    | none => throwError "backward_search_gen: `𝒱 s i j = a` chiude il goal?"
    | some (hv', g') => splitAnds g' hv'
  invertAll cfg g fun g => do
    let g ← addForward cfg g
    refineLeaf cfg ctx g leaf

/-- `x ∈ l` per una lista letterale, per costruttori (niente `decide`). -/
def mkMemProof (α : Expr) (l : List Expr) (x : Expr) : MetaM Expr := do
  let rec go : List Expr → MetaM Expr
    | [] => throwError "backward_search_gen: {x} non è nella lista"
    | y :: rest => do
      let restE ← mkListLit α rest
      if y == x then
        mkAppOptM ``List.Mem.head #[some α, some x, some restE]
      else
        let h ← go rest
        mkAppOptM ``List.Mem.tail #[some α, some x, some y, some restE, some h]
  go l

/-- La vista del predecessore in una foglia `Marker ?P X`: `X` normalizzato, che deve
essere chiuso. -/
def leafView (g : MVarId) : TermElabM Expr := g.withContext do
  let gty ← instantiateMVars (← g.getType)
  unless gty.isAppOfArity ``Marker 3 do
    throwError "backward_search_gen: forma inattesa della foglia{indentExpr gty}"
  let X ← normState gty.appArg!
  if X.hasFVar || X.hasMVar then
    throwError "backward_search_gen: vista del predecessore non determinata{indentExpr X}\n\
      (nel contesto:\n{← g.withContext do addMessageContext (MessageData.ofGoal g)})"
  return X

/-- Il corpo della tattica. -/
def core (cfg : Cfg) (setupStx : Syntax) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let tgt ← instantiateMVars (← mainGoal.getType)
    -- il setup, e i suoi tipi
    let setupE ← Term.elabTerm setupStx none
    let setupTy ← whnfD (← inferType setupE)
    unless setupTy.isAppOfArity ``SymSetup 4 do
      throwError "backward_search_gen: atteso un `SymSetup`, trovato{indentExpr setupTy}"
    -- il goal: `st.Unreachable` oppure `∀ s, B s → ¬ l.reachable s` (MI.LTS)
    let sTy := setupTy.getAppArgs[0]!
    -- unifica il tipo degli stati con il binder del goal (istanzia `n`)
    forallBoundedTelescope tgt (some 1) fun xs _ => do
      unless xs.size == 1 do throwError "backward_search_gen: il goal deve iniziare con `∀ s`"
      unless ← isDefEq (← inferType xs[0]!) sTy do
        throwError "backward_search_gen: il tipo degli stati del goal non è quello del setup"
    let setupE ← instantiateMVars setupE
    let setupTy ← instantiateMVars setupTy
    let args := setupTy.getAppArgs
    let sTy := args[0]!; let tTy := args[1]!; let iTy := args[2]!; let vTy := args[3]!
    -- i campi del setup, senza srotolarne il valore (`whnfD` scenderebbe dentro `miView`)
    let setupVal ← whnfD setupE
    let proj (f : Name) : MetaM Expr := do
      let e ← mkAppM f #[setupVal]
      let r ← whnfCore e
      if r == e then whnfD e else pure r
    let transE ← proj ``SymSetup.trans
    let invE ← proj ``SymSetup.Inv
    let viewE ← proj ``SymSetup.view
    let badE ← proj ``SymSetup.bad
    let s0E ← proj ``SymSetup.s0
    let ctx ← mkSimpCtx cfg vTy
    let mkView (s i j : Expr) : Expr := mkApp3 viewE s i j
    -- le viste dello stato iniziale: i campi che dipendono dagli indici (il flag `i = j`)
    -- sono di tipo `Bool`, e si prendono entrambi i valori
    let v0s ← withLocalDeclD `i iTy fun i => withLocalDeclD `j iTy fun j => do
      let v ← normState (mkView s0E i j)
      let args := v.getAppArgs
      let mut outs : List Expr := [v.getAppFn]
      for a in args do
        if a.hasFVar then
          unless (← whnfD (← inferType a)).isConstOf ``Bool do
            throwError "backward_search_gen: la vista di `s0` dipende dagli indici{indentExpr v}"
          outs := outs.flatMap fun f => [mkApp f (mkConst ``Bool.true), mkApp f (mkConst ``Bool.false)]
        else
          outs := outs.map fun f => mkApp f a
      let mut res : List Expr := []
      for e in outs do res := res ++ [← normState e]
      pure res
    -- i semi: tutte le viste cattive
    let mut seeds : List Expr := []
    for v in ← enumerateType 8 vTy do
      let pv := (mkApp badE v).headBeta
      let some ok ← evalDecidable pv
        | throwError "backward_search_gen: il predicato cattivo non è decidibile su{indentExpr pv}"
      if ok then seeds := (← normState v) :: seeds
    if seeds.isEmpty then throwError "backward_search_gen: nessuna vista soddisfa il predicato"
    -------------------------------------------------------------------------
    -- FASE 1: la ricerca all'indietro sulle viste, con il passo fatto sulle
    -- regole vere. Per ogni vista `a` si dimostra subito
    --   hstep_a : ∀ i j, i ≠ j → ∀ p t s, Inv p → trans p t s → 𝒱 s i j = a → 𝒱 p i j ∈ Preds a
    -------------------------------------------------------------------------
    -- (a, Preds a, hstep_a) con hstep_a : ∀ i j, ∀ p t s, … → 𝒱 s i j = a → 𝒱 p i j ∈ Preds a
    let stepProofs ← IO.mkRef (#[] : Array (Expr × Expr × Expr))
    let seenRef ← IO.mkRef (∅ : Std.HashSet Expr)
    let visitedRef ← IO.mkRef ([] : List Expr)
    let frontierRef ← IO.mkRef seeds
    let traceRef ← IO.mkRef (#[] : Array MessageData)
    let mut steps : Nat := 0
    repeat
      match ← frontierRef.get with
      | [] => break
      | a :: rest =>
        frontierRef.set rest
        steps := steps + 1
        if steps > 5000 then throwError "backward_search_gen: troppi stati esplorati (>5000)"
        if (← seenRef.get).contains a then
          if cfg.verbose then traceRef.modify (·.push m!"[{steps}] {a}\n      già nella lista: FATTO CENTRO")
          continue
        if v0s.contains a then
          let sofar ← if cfg.verbose then
              pure (m!"la ricerca fin qui:\n\n" ++ MessageData.joinSep (← traceRef.get).toList m!"\n" ++ m!"\n\n")
            else pure m!""
          throwError (sofar ++ m!"backward_search_gen: STOP al passo {steps}: andando all'indietro si raggiunge la vista dello stato iniziale{indentExpr a}\n"
            ++ m!"quindi uno stato cattivo è RAGGIUNGIBILE (o la vista è troppo grossolana)")
        visitedRef.modify (a :: ·)
        seenRef.modify (·.insert a)
        -- il passo backward generalizzato, sotto `i j : ι`, `hij : i ≠ j`
        let PM ← mkFreshExprMVar (← mkArrow vTy (mkSort levelZero))
        let ((preds, predsE), proof) ← withLocalDeclD `i iTy fun i => withLocalDeclD `j iTy fun j => do
            let goalTy ← withLocalDeclD `p sTy fun p => withLocalDeclD `t tTy fun t =>
              withLocalDeclD `s sTy fun s => do
                let body ← mkArrow (mkApp invE p) (← mkArrow (mkApp3 transE p t s)
                  (← mkArrow (← mkEq (mkView s i j) a) (← mkAppM ``Marker #[PM, mkView p i j])))
                mkForallFVars #[p, t, s] body
            let gM ← mkFreshExprMVar goalTy
            let leaves ← IO.mkRef (#[] : Array (MVarId × Expr))
            symStep cfg ctx gM.mvarId! fun g => do
              let X ← leafView g
              leaves.modify (·.push (g, X))
            -- i predecessori trovati; `?P := (· ∈ Preds a)`, foglie chiuse per costruttori,
            -- e la prova istanziata subito (termine chiuso e piccolo)
            let mut preds : List Expr := []
            for (_, X) in ← leaves.get do
              unless preds.contains X do preds := preds ++ [X]
            let predsE ← mkListLit vTy preds
            let PMval ← withLocalDeclD `v vTy fun v => do
              mkLambdaFVars #[v] (← mkAppM ``Membership.mem #[predsE, v])
            PM.mvarId!.assign PMval
            for (g, X) in ← leaves.get do
              let prf ← mkMemProof vTy preds X
              g.withContext do
                unless ← isDefEq (← inferType prf) (← g.getType) do
                  throwError "backward_search_gen: la foglia non combacia con i predecessori"
                g.assign prf
            let proof ← instantiateMVars gM
            if proof.hasMVar then throwError "backward_search_gen: la dimostrazione del passo ha metavariabili"
            pure ((preds, predsE), ← mkLambdaFVars #[i, j] proof)
        stepProofs.modify (·.push (a, predsE, proof))
        for X in preds do frontierRef.modify (X :: ·)
        if cfg.verbose then
          if preds.isEmpty then
            traceRef.modify (·.push m!"[{steps}] {a}\n      nessun predecessore: VINTO")
          else
            traceRef.modify (·.push (m!"[{steps}] {a}\n      {preds.length} predecessori:\n"
              ++ MessageData.joinSep (preds.map fun e => m!"        → {e}") m!"\n"))
    let visited := (← visitedRef.get).reverse
    if cfg.verbose then
      logInfo (m!"backward_search_gen: {seeds.length} viste di partenza; la ricerca all'indietro\n\n"
        ++ MessageData.joinSep (← traceRef.get).toList m!"\n"
        ++ m!"\n\nSTOP: frontiera vuota dopo {steps} passi — {visited.length} viste, nessuna è quella iniziale.")
    else
      logInfo m!"backward_search_gen: {seeds.length} viste di partenza, chiusura di {visited.length} viste ({steps} passi)"
    -------------------------------------------------------------------------
    -- FASE 2: il certificato
    -------------------------------------------------------------------------
    let UE ← mkListLit vTy visited
    let memU (x : Expr) : MetaM Expr := mkAppM ``Membership.mem #[UE, x]
    -- h0 : ∀ i j, 𝒱 s0 i j ∉ U — per casi su `i = j` (il flag della vista), `simp_all`
    -- riduce la vista a un letterale, e `decide` la esclude da `U`
    let h0Ty ← withLocalDeclD `i iTy fun i => withLocalDeclD `j iTy fun j => do
      mkForallFVars #[i, j] (mkApp (mkConst ``Not) (← memU (mkView s0E i j)))
    let h0M ← mkFreshExprMVar h0Ty
    let (fs0, g0) ← h0M.mvarId!.introN 3
    -- `simp_all` sull'intera ipotesi `𝒱 s0 i j ∈ U` ricorre dentro il letterale di `U`
    -- (centinaia di `cons`) e sfonda la profondità di ricorsione: si semplifica solo
    -- l'elemento, e si trasporta l'appartenenza con `congrArg`.
    let closeInit (g : MVarId) (hne? : Option FVarId) : TermElabM Unit := g.withContext do
      let mut memDecl : Option LocalDecl := none
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isAppOfArity ``Membership.mem 5 then memDecl := some d
      let some d := memDecl
        | throwError "backward_search_gen: ipotesi di appartenenza non trovata in{indentD (MessageData.ofGoal g)}"
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
        throwError "backward_search_gen: la vista di `s0` non si riduce{indentExpr x''}"
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
    -- hclosed
    let hclosedTy ← withLocalDeclD `i iTy fun i => withLocalDeclD `j iTy fun j => do
      withLocalDeclD `a vTy fun a => do
      let memA ← memU a
      withLocalDeclD `ha memA fun ha => do
        let inner ← withLocalDeclD `p sTy fun p => withLocalDeclD `t tTy fun t =>
          withLocalDeclD `s sTy fun s => do
            let body ← mkArrow (mkApp invE p) (← mkArrow (mkApp3 transE p t s)
              (← mkArrow (← mkEq (mkView s i j) a) (← memU (mkView p i j))))
            mkForallFVars #[p, t, s] body
        mkForallFVars #[i, j, a, ha] inner
    let proofs ← stepProofs.get
    -- `Preds a ⊆ U`, per costruttori
    let subsetProof (preds : List Expr) : MetaM Expr := do
      let PU ← withLocalDeclD `x vTy fun x => do mkLambdaFVars #[x] (← memU x)
      let rec go : List Expr → MetaM Expr
        | [] => pure (mkAppN (mkConst ``forall_mem_nil') #[vTy, PU])
        | y :: rest => do
          let restE ← mkListLit vTy rest
          let hy ← mkMemProof vTy visited y
          let hrest ← go rest
          pure (mkAppN (mkConst ``forall_mem_cons') #[vTy, PU, y, restE, hy, hrest])
      go preds
    let hclosedM ← withLocalDeclD `i iTy fun i => withLocalDeclD `j iTy fun j => do
        -- Q a := ∀ p t s, Inv p → trans p t s → 𝒱 s i j = a → 𝒱 p i j ∈ U
        let Q ← withLocalDeclD `a vTy fun a => do
          let inner ← withLocalDeclD `p sTy fun p => withLocalDeclD `t tTy fun t =>
            withLocalDeclD `s sTy fun s => do
              let body ← mkArrow (mkApp invE p) (← mkArrow (mkApp3 transE p t s)
                (← mkArrow (← mkEq (mkView s i j) a) (← memU (mkView p i j))))
              mkForallFVars #[p, t, s] body
          mkLambdaFVars #[a] inner
        -- la prova di Q a_k
        let qProof (k : Nat) : MetaM Expr := do
          let (_, predsE, hstep) := proofs[k]!
          let preds := (predsE.listLit?.map (·.2)).getD []
          let sub ← subsetProof preds
          withLocalDeclD `p sTy fun p => withLocalDeclD `t tTy fun t =>
            withLocalDeclD `s sTy fun s => do
              let hinvTy := mkApp invE p
              let hstTy := mkApp3 transE p t s
              withLocalDeclD `hinv hinvTy fun hinv => withLocalDeclD `hst hstTy fun hst => do
                let hvTy ← mkEq (mkView s i j) (proofs[k]!.1)
                withLocalDeclD `hv hvTy fun hv => do
                  let hs := mkAppN hstep #[i, j, p, t, s, hinv, hst, hv]
                  let body := mkApp2 sub (mkView p i j) hs
                  mkLambdaFVars #[p, t, s, hinv, hst, hv] body
        let rec chain (k : Nat) (rest : List Expr) : MetaM Expr := do
          match rest with
          | [] => pure (mkAppN (mkConst ``forall_mem_nil') #[vTy, Q])
          | a :: rest' => do
            let restE ← mkListLit vTy rest'
            let hq ← qProof k
            let hrest ← chain (k + 1) rest'
            pure (mkAppN (mkConst ``forall_mem_cons') #[vTy, Q, a, restE, hq, hrest])
        let body ← chain 0 visited
        mkLambdaFVars #[i, j] body
    unless ← isDefEq (← inferType hclosedM) hclosedTy do
      throwError "backward_search_gen: l'obbligazione di chiusura non combacia"
    -- hbad : ∀ v, bad v → v ∈ U
    let hbadTy ← withLocalDeclD `v vTy fun v => do
      mkForallFVars #[v] (← mkArrow (mkApp badE v).headBeta (← memU v))
    let hbadM ← mkFreshExprMVar hbadTy
    let (_, gb) ← hbadM.mvarId!.intro `v
    splitFiniteNoSimp gb fun g => g.withContext do
      let (hF, g1) ← g.intro `hp
      g1.withContext do
        let gty1 ← instantiateMVars (← g1.getType)
        let hpTy ← instantiateMVars (← hF.getType)
        -- la vista concreta: l'argomento di `∈`
        let v ← normState gty1.appArg!
        match ← evalDecidable hpTy with
        | some true => g1.assign (← mkMemProof vTy visited v)
        | some false =>
          let hn ← decideProp (mkApp (mkConst ``Not) hpTy)
          g1.assign (← mkAppOptM ``absurd #[none, some gty1, some (mkFVar hF), some hn])
        | none => throwError "backward_search_gen: predicato cattivo non decidibile su{indentExpr v}"
    -- il certificato
    let cert := mkAppN (mkConst ``SymSetup.certificate) #[sTy, tTy, iTy, vTy, setupE, UE, h0M, hclosedM, hbadM]
    if tgt.isAppOf ``SymSetup.Unreachable then
      unless ← isDefEq (← inferType cert) tgt do
        throwError "backward_search_gen: il setup non è quello del goal"
      mainGoal.assign cert
    else
      -- forma `∀ s, B s → ¬ R s` dove `R s` si srotola in
      -- `∀ s_init, init s_init → ReflTransGen _ s_init s` (come `MI.LTS.reachable`)
      let prf ← forallBoundedTelescope tgt (some 2) fun xs body => do
        let some nbody := body.not?
          | throwError "backward_search_gen: il goal deve essere `st.Unreachable` o `∀ s, B s → ¬ reachable s`"
        let rb ← whnfD nbody
        unless rb.isForall && (rb.bindingBody!).isForall do
          throwError "backward_search_gen: atteso `¬ reachable s` (∀ s_init, init s_init → …), trovato{indentExpr nbody}"
        let hinitTy ← whnfD ((rb.bindingBody!.instantiate1 s0E).bindingDomain!)
        let hinit ← (do
          try decideProp hinitTy
          catch _ =>
            if hinitTy.isConstOf ``True then pure (mkConst ``True.intro)
            else
              let m ← mkFreshExprMVar hinitTy
              let gs ← runTac m.mvarId! (← `(tactic| first | rfl | trivial | (repeat' first | intro _ | constructor)))
              unless gs.isEmpty do throwError "backward_search_gen: non riesco a dimostrare `l.init s0`"
              instantiateMVars m)
        withLocalDeclD `hreach nbody fun hreach => do
          let inner := mkApp (mkApp2 cert xs[0]! xs[1]!) (mkApp2 hreach s0E hinit)
          mkLambdaFVars (xs.push hreach) inner
      -- il termine è controllato dal kernel; qui basta che sia ben tipato
      discard <| inferType prf
      mainGoal.assign prf
    replaceMainGoal []

end Gen

syntax (name := backwardSearchGenTac) "backward_search_gen" term:max
  " simp " "[" ident,* "]" " fwd " "[" ident,* "]" " split " ident ident " upd " ident
  " inv " "[" ident,* "]" : tactic
syntax (name := backwardSearchGenVerboseTac) "backward_search_gen?" term:max
  " simp " "[" ident,* "]" " fwd " "[" ident,* "]" " split " ident ident " upd " ident
  " inv " "[" ident,* "]" : tactic

def Gen.parseCfg (verbose : Bool) (simps fwds : Array Syntax) (spl fn updS : Syntax)
    (invs : Array Syntax) : TacticM Gen.Cfg := do
  let names (xs : Array Syntax) : TacticM (Array Name) :=
    xs.mapM fun x => realizeGlobalConstNoOverloadWithInfo x
  return { simps := ← names simps, fwds := ← names fwds,
           splitLemma := ← realizeGlobalConstNoOverloadWithInfo spl,
           splitFn := ← realizeGlobalConstNoOverloadWithInfo fn,
           updFn := ← realizeGlobalConstNoOverloadWithInfo updS,
           invs := ← names invs, verbose }

@[tactic backwardSearchGenTac] def Gen.evalTac : Tactic := fun stx => do
  match stx with
  | `(tactic| backward_search_gen $setup simp [$simps,*] fwd [$fwds,*] split $spl $fn upd $updS inv [$invs,*]) =>
    let cfg ← Gen.parseCfg false simps.getElems fwds.getElems spl fn updS invs.getElems
    Gen.core cfg setup
  | _ => throwUnsupportedSyntax

@[tactic backwardSearchGenVerboseTac] def Gen.evalTacVerbose : Tactic := fun stx => do
  match stx with
  | `(tactic| backward_search_gen? $setup simp [$simps,*] fwd [$fwds,*] split $spl $fn upd $updS inv [$invs,*]) =>
    let cfg ← Gen.parseCfg true simps.getElems fwds.getElems spl fn updS invs.getElems
    Gen.core cfg setup
  | _ => throwUnsupportedSyntax

end BackwardGen
