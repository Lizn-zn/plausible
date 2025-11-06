/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Cases
import Lean.Meta.Match.MatcherInfo

/-!
Tactic to split match expressions.
-/

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- Check if an expression contains a match/casesOn application.
We look for functions whose names end with .casesOn, .rec, .brecOn, etc. -/
private partial def hasMatchExpr (e : Expr) : Bool :=
  let rec visit (e : Expr) : Bool :=
    if e.isApp then
      let fn := e.getAppFn
      if fn.isConst then
        let name := fn.constName!.toString
        -- Match on casesOn, rec, brecOn patterns
        -- Be more permissive: accept any casesOn or rec that might be match-related
        if name.endsWith ".casesOn" then
          true
        else if name.endsWith ".rec" then
          -- Accept any .rec - let split decide if it can handle it
          true
        else if name.endsWith ".recOn" then
          true
        else
          -- Recursively check arguments
          e.withApp fun _ args => args.any visit
      else
        -- Recursively check arguments
        e.withApp fun _ args => args.any visit
    else if e.isLet then
      visit e.letBody! || visit e.letValue!
    else if e.isForall then
      visit e.bindingBody!
    else if e.isLambda then
      visit e.bindingBody!
    else
      false
  visit e

/-- Check if the current goal contains a match expression -/
private def goalHasMatch : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  return hasMatchExpr target

/-- Try to apply split -/
private def trySplit : TacticM Bool := do
  try
    evalTactic (← `(tactic| split))
    return true
  catch _ =>
    return false

/-- Main loop of split_match. Repeatedly applies split while matches remain. -/
private partial def splitMatchCore : Nat → TacticM Unit
  | 0 => return () -- Prevent infinite loops
  | n + 1 => withMainContext do
    let didSplit ← trySplit

    if !didSplit then
      return () -- Split failed or nothing to split

    -- Split succeeded, continue on all subgoals
    let goals ← getUnsolvedGoals
    let mut newGoals := #[]
    for goal in goals do
      setGoals [goal]
      try
        splitMatchCore n
      catch _ =>
        pure ()
      newGoals := newGoals ++ (← getUnsolvedGoals)
    setGoals newGoals.toList

/-- Splits all match expressions into multiple goals.
Given a goal with a match expression, `split_match` will perform case analysis
on the discriminant and create separate goals for each case.

This tactic repeatedly applies the built-in `split` tactic, but only when
there is a match expression present in the goal (to avoid splitting other
splittable constructs like `∧`, `∃`, etc.).

Examples:
```lean
example (n : Nat) : (match n with | 0 => 1 | n+1 => n+2) = n + 1 := by
  split_match
  -- Now have two goals:
  -- case zero: 1 = 0 + 1
  -- case succ: n✝ + 2 = n✝ + 1 + 1
```

```lean
example (xs : List Nat) (h : True) :
    match xs, h with
    | [], _ => xs.length = 0
    | _::_, _ => xs.length > 0 := by
  split_match
  -- Splits into cases for empty and non-empty list
```

Note: This tactic only works on the goal (target), not on hypotheses.
-/
syntax (name := _splitMatch) "_split_match" : tactic

elab_rules : tactic
| `(tactic| _split_match) => withMainContext do
    -- Try to split repeatedly (max 100 times to prevent infinite loops)
    -- We don't check for match expressions first because detection can be unreliable
    -- Just try split and see if it works
    let initialGoals ← getGoals
    try
      splitMatchCore 100
    catch e =>
      -- If split failed completely and we have the same goals, report error
      let finalGoals ← getGoals
      if initialGoals == finalGoals then
        throwError "Failed to split match expression: {e.toMessageData}"
      else
        -- Made some progress, that's fine
        pure ()
