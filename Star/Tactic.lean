import Lean

syntax (name := namedSorry) "named_sorry " ident : tactic

open Lean Elab Tactic Meta
@[tactic namedSorry]
meta def evalNamedSorry : Tactic := fun stx => do
  let userName := stx[1].getId.eraseMacroScopes
  let currDecl ← Term.getDeclName?

  let declId :=
    match currDecl with
    | some n => n ++ userName
    | none   => userName

  if (← getEnv).contains declId then
    throwError "declaration '{declId}' already exists"

  let goal ← getMainGoal

  goal.withContext do
    let target ← instantiateMVars (← goal.getType)

    let lctx ← getLCtx
    let fvars := lctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc
      else acc.push decl.toExpr

    let axiomType ← mkForallFVars fvars target
    let axiomType ← instantiateMVars axiomType

    /- let levelParams := (collectLevelParams {} axiomType)..toList -/

    addDecl <| Declaration.axiomDecl {
      name        := declId
      levelParams := []
      type        := axiomType
      isUnsafe    := false
    }

    let proof := mkAppN (mkConst declId []) fvars
    goal.assign proof

  replaceMainGoal []
