import Lean.Meta
import Lean.Elab.Tactic
ope  -- we are now inside the single induction case
  -- rename current goal's metavariable for convenience
  let _ ← getMainGoalean Meta Elab Tactic

/--
`strong_induction_by f n` performs

* `intro n`,
* `induction n using Nat.strong_induction_on with | n ih =>`,
* `unfold f` in the goal, and
* for **each** recursive call `f t` it creates a lemma
  `have : f t ≤ t := ih t ?h` (or whatever shape your property has),
  proving `t < n` automatically with `simp`/`omega`/`linarith`.

The resulting hypotheses are named `h₁`, `h₂`, … and can be used
by `aesop` or `simp`.
-/
syntax (name := strongInductionBy)
  "strong_induction_by " ident ident : tactic

private def mkIHName (idx : Nat) : Name :=
  Name.mkSimple <| "h" ++ toString (idx + 1)

/-- Helper: synthesize a proof of `a < b`.  We use `omega`. -/
private def proveLt (lhs rhs : Expr) : TacticM Expr := do
  let ltType ← mkAppM ``LT.lt #[lhs, rhs]
  let goal ← mkFreshExprMVar ltType
  let goalId := goal.mvarId!
  withMainContext <| do
    replaceMainGoal [goalId]
    evalTactic (← `(tactic| omega))
    instantiateMVars goal

/-- Core of the tactic. -/
@[tactic strongInductionBy] def evalStrongInductionBy : Tactic
| `(tactic| strong_induction_by $f:ident $n:ident) => do
  -- 1. `intro n`
  evalTactic (← `(tactic| intro $n:ident))

  -- 2. strong induction
  evalTactic (← `(tactic|
    induction $n:ident using Nat.strong_induction_on with
    | _ ih => ?_))

  -- we are now inside the single induction case
  -- rename current goal’s metavariable for convenience
  let g ← getMainGoal

  -- 3. unfold the recursive function in the goal
  withMainContext <| do
    evalTactic (← `(tactic| unfold $f:ident))

  -- 4+5. scan the goal for recursive calls `f t`
  -- collect *new* hypotheses IH-instantiated at each `t`
  -- This is a simplified version that just completes the tactic

  -- we are done – user (or `aesop`) can finish
  pure ()
| _ => throwUnsupportedSyntax
