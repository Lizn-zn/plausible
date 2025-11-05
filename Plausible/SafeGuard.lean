/-
Safe guards for Plausible to prevent runtime panics from partial functions.

This module provides a mechanism to automatically verify safety conditions
(like list non-emptiness) before evaluating Decidable instances.
-/

import Lean

namespace Plausible.SafeGuard

open Lean Meta Elab Term

/-- List of partial function names to check -/
def partialFunctions : List Name := [
  ``List.getLast!,
  ``List.head!,
  ``List.tail!,
  ``GetElem?.getElem!
]

/-- Extract all applications of partial functions in an expression -/
partial def findPartialFunctionCalls (e : Expr) : MetaM (Array (Name × Expr)) := do
  let rec visit (e : Expr) : MetaM (Array (Name × Expr)) := do
    let mut result := #[]

    -- Check if this is a call to any partial function
    for fnName in partialFunctions do
      if e.isAppOf fnName then
        -- Try to extract the relevant argument (usually the collection being accessed)
        -- For most partial functions, it's one of the early arguments
        if e.getAppNumArgs >= 1 then
          -- We'll just record the function name and the whole expression
          -- The exact argument extraction can be refined per function if needed
          result := result.push (fnName, e)

    -- Recursively visit all subexpressions
    match e with
    | .app f a =>
      let fCalls ← visit f
      let aCalls ← visit a
      result := result ++ fCalls ++ aCalls
    | .lam _ _ b _ =>
      let bCalls ← visit b
      result := result ++ bCalls
    | .forallE _ d b _ =>
      let dCalls ← visit d
      let bCalls ← visit b
      result := result ++ dCalls ++ bCalls
    | .letE _ t v b _ =>
      let tCalls ← visit t
      let vCalls ← visit v
      let bCalls ← visit b
      result := result ++ tCalls ++ vCalls ++ bCalls
    | .mdata _ e' =>
      let eCalls ← visit e'
      result := result ++ eCalls
    | .proj _ _ e' =>
      let eCalls ← visit e'
      result := result ++ eCalls
    | _ => pure ()
    return result

  visit e

/-- Maximum depth for unfolding function definitions -/
def maxUnfoldDepth : Nat := 3

/-- Collect all constants (function names) used in an expression -/
partial def collectConstants (e : Expr) : Array Name :=
  let rec visit (e : Expr) (acc : Array Name) : Array Name :=
    let acc := if let .const name _ := e then acc.push name else acc
    match e with
    | .app f a => visit a (visit f acc)
    | .lam _ _ b _ => visit b acc
    | .forallE _ d b _ => visit b (visit d acc)
    | .letE _ t v b _ => visit b (visit v (visit t acc))
    | .mdata _ e' => visit e' acc
    | .proj _ _ e' => visit e' acc
    | _ => acc
  visit e #[]

/-- Unfold function definitions recursively to check their bodies -/
partial def unfoldAndCheck (e : Expr) (depth : Nat := 0) (visited : Std.HashSet Name := {}) : MetaM (Array (Name × Expr)) := do
  if depth >= maxUnfoldDepth then
    return #[]
  
  let mut allCalls := #[]
  
  -- First check the current expression
  let directCalls ← findPartialFunctionCalls e
  allCalls := allCalls ++ directCalls
  
  -- Then collect all constants and try to unfold them
  let constants := collectConstants e
  
  for constName in constants do
    -- Skip if we've already visited this function
    if visited.contains constName then
      continue
    
    -- Try to get the function's definition
    try
      let constInfo ← getConstInfo constName
      match constInfo with
      | .defnInfo info =>
        -- We found a function definition, check its body recursively
        let newVisited := visited.insert constName
        let bodyCalls ← unfoldAndCheck info.value (depth + 1) newVisited
        allCalls := allCalls ++ bodyCalls
      | _ => pure ()  -- Not a definition, skip
    catch _ =>
      pure ()  -- Couldn't get definition, skip
  
  return allCalls

/-- Check if an expression contains unsafe calls to partial functions and report them -/
def checkGetLastSafety (e : Expr) : MetaM Unit := do
  -- Recursively unfold and find all partial function calls (max 3 levels deep)
  let calls ← unfoldAndCheck e
  
  if calls.isEmpty then
    return ()
  
  -- Conservative approach: report ALL partial function uses (deduplicated)
  let mut fnSet : Std.HashSet Name := {}
  
  for (fnName, _) in calls do
    fnSet := fnSet.insert fnName
  
  if !fnSet.isEmpty then
    let mut errors := #[]
    for fnName in fnSet.toArray do
      let safeName := match fnName with
        | ``List.getLast! => "List.getLast?"
        | ``List.head! => "List.head?"
        | ``List.tail! => "List.tail?"
        | ``GetElem?.getElem! => "getElem? or get?"
        | _ => "safe alternative (?)"
      errors := errors.push s!"Partial function `{fnName}` can panic.\nSafe alternative: {safeName}"
    
    let errorMsg := String.intercalate "\n\n" errors.toList
    throwError errorMsg

end Plausible.SafeGuard
