import Plausible

import Std.Data.HashMap
open Std

set_option maxHeartbeats 0


def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0

def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first

@[reducible, simp]
def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

namespace test1

@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  Id.run do
    let mut counts : HashMap Int Nat := {}
    let n := nums.length
    for x in nums do
      let count := counts.getD x 0
      counts := counts.insert x (count + 1)
    match counts.toList.find? (fun (_, c) => c > n / 2) with
    | some (k, _) => k
    | none      => 0

@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x, x ≠ result → nums.count x ≤ n / 2

theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
    dsimp [majorityElement_postcond, majorityElement]
    plausible (config := { numInst := 1000, maxSize := 100, numRetries := 20, randomSeed := some 42})

end test1


namespace test2

def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0
  ∧ (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10)
  ∧ (l1.getLast! ≠ 0 ∨ l1 = [0])
  ∧ (l2.getLast! ≠ 0 ∨ l2 = [0])

def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  let rec addAux (l1 l2 : List Nat) (carry : Nat) : List Nat :=
    match l1, l2 with
    | [], [] =>
      if carry = 0 then [] else [carry]
    | h1::t1, [] =>
      let sum := h1 + carry
      (sum % 10) :: addAux t1 [] (sum / 10)
    | [], h2::t2 =>
      let sum := h2 + carry
      (sum % 10) :: addAux [] t2 (sum / 10)
    | h1::t1, h2::t2 =>
      let sum := h1 + h2 + carry
      (sum % 10) :: addAux t1 t2 (sum / 10)
  addAux l1 l2 0

@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  listToNat result = listToNat l1 + listToNat l2
  ∧
  (∀ d ∈ result, d < 10) ∧
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond := by
    unfold addTwoNumbers addTwoNumbers_postcond
    unfold addTwoNumbers_precond at h_precond
    plausible (config := { numInst := 1000, maxSize := 100, numRetries := 20, randomSeed := some 42})

end test2


/-- error: Found a counter-example! -/
#guard_msgs in
theorem type_u (α : Type u) (l : List α) : l = l ++ l := by
  plausible (config := {quiet := true})
