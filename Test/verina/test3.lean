import Plausible

set_option linter.unusedVariables false


/-- error: Found a counter-example! -/
#guard_msgs in
example (l1 l2 : List Nat) : l1.length > 0 ∧ l2.length > 0
  ∧ (l1.all (fun x => decide (x < 10)) = true) ∧ (l2.all (fun x => decide (x < 10)) = true)
  ∧ (l1.getLast! ≠ 0 ∨ l1 = [0])
  ∧ (l2.getLast! ≠ 0 ∨ l2 = [0])
:= by
  plausible (config := {quiet := true})
