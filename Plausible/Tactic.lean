/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/

import Plausible.Testable
import Plausible.Attr


/-!
## Finding counterexamples automatically using `plausible`

A proposition can be tested by writing it out as:

```lean
example (xs : List Nat) (w : ∃ x ∈ xs, x < 3) : ∀ y ∈ xs, y < 5 := by plausible
-- ===================
-- Found problems!

-- xs := [0, 5]
-- x := 0
-- y := 5
-- -------------------

example (x : Nat) (h : 2 ∣ x) : x < 100 := by plausible
-- ===================
-- Found problems!

-- x := 258
-- -------------------

example (α : Type) (xs ys : List α) : xs ++ ys = ys ++ xs := by plausible
-- ===================
-- Found problems!

-- α := Int
-- xs := [-4]
-- ys := [1]
-- -------------------

example : ∀ x ∈ [1,2,3], x < 4 := by plausible
-- Success
```

In the first example, `plausible` is called on the following goal:

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

The local constants are reverted and an instance is found for
`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by instances of `Sampleable (List Nat)`,
`Decidable (x < 3)` and `Decidable (y < 5)`. `plausible` builds a
`Testable` instance step by step with:

```
- Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
                                     -: Sampleable (List xs)
- Testable ((∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
- Testable (∀ x ∈ xs, x < 3 → (∀ y ∈ xs, y < 5))
- Testable (x < 3 → (∀ y ∈ xs, y < 5))
                                     -: Decidable (x < 3)
- Testable (∀ y ∈ xs, y < 5)
                                     -: Decidable (y < 5)
```

`Sampleable (List Nat)` lets us create random data of type `List Nat` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `x < 3` and `y < 5` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, if we generate lists that only contain numbers
greater than `3`, the implication will always trivially hold but we should
conclude that we haven't found meaningful examples. Instead, when `x < 3`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`plausible` prints `Success`, it means that a hundred suitable lists
were found and successfully tested.

If no counter-examples are found, `plausible` behaves like `admit`.

`plausible` can also be invoked using `#eval`:

```lean
#eval Plausible.Testable.check (∀ (α : Type) (xs ys : List α), xs ++ ys = ys ++ xs)
-- ===================
-- Found problems!

-- α := Int
-- xs := [-4]
-- ys := [1]
-- -------------------
```

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.Plausible.Testable`.
-/

open Lean Elab Meta Tactic
open Parser.Tactic
open Plausible Decorations

/--
`plausible` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by an instance of `Sampleable (List Nat)`,
`Decidable (x < 3)` and `Decidable (y < 5)`.

Examples will be created in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!
xs := [1, 28]
x := 1
y := 28
-------------------
```

If `plausible` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.Plausible.Testable`.

Optional arguments given with `plausible (config : { ... })`
* `numInst` (default 100): number of examples to test properties with
* `maxSize` (default 100): final size argument

Options:
* `set_option trace.plausible.decoration true`: print the proposition with quantifier annotations
* `set_option trace.plausible.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.plausible.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.plausible.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.plausible.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.plausible.success true`: print the tested samples that satisfy a property
-/
syntax (name := plausibleSyntax) "plausible" (config)? : tactic
syntax (name := plausibleAllGoals) "plausible_all" (config)? : tactic

elab_rules : tactic | `(tactic| plausible $[$cfg]?) => withMainContext do
  let cfg ← elabConfig (mkOptionalNode cfg)
  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
  g.withContext do
  let tgt ← g.getType
  let tgt' ← addDecorations tgt
  
  -- Safety check: verify that any getLast! calls have provably non-empty lists
  -- This prevents runtime panics during testing
  -- Only run if enableSafeGuard is true in config
  if cfg.enableSafeGuard then
    try
      -- We reduce the target with reducible transparency to see through @[reducible] definitions
      let tgtReduced ← Meta.withTransparency .reducible (Meta.reduce tgt')
      SafeGuard.checkGetLastSafety tgtReduced
    catch e =>
      throwError "\
        [Plausible Safety Error]\
        \n{e.toMessageData}\
        \n\
        \nTo fix: wrap partial functions with guards like `if l.length > 0 then ... else True`\
        \nOr disable SafeGuard: plausible (config := \{ enableSafeGuard := false })"

  let cfg := { cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
  let inst ← try
    -- Use reducible transparency to allow type class inference to see through @[reducible] definitions
    -- This enables automatic Decidable instance synthesis for reducible Prop definitions
    Meta.withTransparency .reducible do
      synthInstance (← mkAppM ``Testable #[tgt'])
  catch _ => throwError "\
      Failed to create a `testable` instance for `{tgt}`.\
    \nWhat to do:\
    \n1. make sure that the types you are using have `Plausible.SampleableExt` instances\
    \n (you can use `#sample my_type` if you are unsure);\
    \n2. make sure that the relations and predicates that your proposition use are decidable;\
    \n3. make sure that instances of `Plausible.Testable` exist that, when combined,\
    \n  apply to your decorated proposition:\
    \n```\
    \n{tgt'}\
    \n```\
    \n\
    \nUse `set_option trace.Meta.synthInstance true` to understand what instances are missing.\
    \n\
    \nTry this:\
    \nset_option trace.Meta.synthInstance true\
    \n#synth Plausible.Testable ({tgt'})"
  let e ← mkAppOptM ``Testable.check #[tgt, toExpr cfg, tgt', inst]
  trace[plausible.decoration] "[testable decoration]\n  {tgt'}"
  -- Porting note: I have not ported support for `trace.plausible.instance`.
  -- See the commented out code below from mathlib3 if you would like to implement this.
  --   when_tracing `plausible.instance   <| do
  --   { inst ← summarize_instance inst >>= pp,
  --     trace!"\n[testable instance]{format.indent inst 2}" },
  let code ← unsafe evalExpr (CoreM PUnit) (mkApp (mkConst ``CoreM) (mkConst ``PUnit [1])) e
  _ ← code
  admitGoal g

/-- Variant of `plausible` that automatically breaks down conjunctions and applies `plausible` to all subgoals.

Usage: `plausible_all`

This tactic will:
1. Execute `repeat (any_goals constructor)` to break down conjunctions
2. Execute `plausible` on each subgoal sequentially, stopping immediately if any goal fails

This is useful when dealing with complex propositions that are conjunctions of multiple properties.
Note: Unlike `all_goals plausible`, this stops as soon as one goal finds a counter-example. -/
elab_rules : tactic | `(tactic| plausible_all $[$cfg]?) => withMainContext do
  -- Step 1: Repeat constructor to break down conjunctions (with limit to avoid infinite loops)
  -- We limit to at most 50 iterations to prevent performance issues
  let maxIterations := 50
  let mut iterations := 0
  let mut prevGoalCount := 0
  let mut shouldContinue := true
  while shouldContinue do
    let goals ← getGoals
    let currentGoalCount := goals.length
    -- Stop if we've reached max iterations or if no progress is being made
    if iterations >= maxIterations || (iterations > 0 && currentGoalCount == prevGoalCount) then
      shouldContinue := false
    else
      prevGoalCount := currentGoalCount
      iterations := iterations + 1
      Lean.Elab.Tactic.evalTactic (← `(tactic| try (any_goals constructor)))

  -- Step 2: Apply plausible to each subgoal sequentially, stopping on first failure
  -- We process goals one by one, and if plausible finds a counter-example, it will throw an error
  -- which will stop the entire tactic execution immediately
  let goals ← getGoals
  for _ in goals do
    -- Process only the first goal (if there are multiple, we'll handle them one by one)
    -- If plausible succeeds (no counter-example), it will admit the goal and we continue
    -- If plausible fails (finds counter-example), it will throw an error and stop execution
    match cfg with
    | some cfgNode =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| focus (plausible $cfgNode)))
    | none =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| focus plausible))

-- Porting note: below is the remaining code from mathlib3 which supports the
-- `trace.plausible.instance` trace option, and which has not been ported.

-- namespace tactic.interactive
-- open tactic plausible

-- open expr

-- /-- Tree structure representing a `testable` instance. -/
-- meta inductive instance_tree
-- | node : name → expr → list instance_tree → instance_tree

-- /-- Gather information about a `testable` instance. Given
-- an expression of type `testable ?p`, gather the
-- name of the `testable` instances that it is built from
-- and the proposition that they test. -/
-- meta def summarize_instance : expr → tactic instance_tree
-- | (lam n bi d b) := do
--    v ← mk_local' n bi d,
--    summarize_instance <| b.instantiate_var v
-- | e@(app f x) := do
--    `(testable %%p) ← infer_type e,
--    xs ← e.get_app_args.mmap_filter (try_core ∘ summarize_instance),
--    pure <| instance_tree.node e.get_app_fn.const_name p xs
-- | e := do
--   failed

-- /-- format an `instance_tree` -/
-- meta def instance_tree.to_format : instance_tree → tactic format
-- | (instance_tree.node n p xs) := do
--   xs ← format.join <$> (xs.mmap <| λ t, flip format.indent 2 <$> instance_tree.to_format t),
--   ys ← pformat!"testable ({p})",
--   pformat!"+ {n} :{format.indent ys 2}\n{xs}"

-- meta instance instance_tree.has_to_tactic_format : has_to_tactic_format instance_tree :=
-- ⟨ instance_tree.to_format ⟩
