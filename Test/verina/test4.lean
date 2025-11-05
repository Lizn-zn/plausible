import Plausible

def average (xs : List Nat) : Nat :=
  xs.getLast!

def listMax (xs : List Nat) : Nat :=
  xs.foldl max 0


theorem average_spec : ∀ xs, average xs ≤ listMax xs := by
  plausible_all (config := {maxSize := 10000})
