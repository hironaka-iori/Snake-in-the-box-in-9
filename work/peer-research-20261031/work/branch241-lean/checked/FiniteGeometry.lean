import Std
import Lean

/-! Small actual Q9 Boolean geometry checks; no global snake theorem is claimed. -/
namespace Q9FiniteGeometry

def adj9 (x y : Nat) : Bool :=
  (List.range 9).any (fun d => (x ^^^ y) == (1 <<< d))

def windowVertices (c d : Nat) : List Nat :=
  [0, 1, 3, 3 ^^^ (1 <<< c), (3 ^^^ (1 <<< c)) ^^^ (1 <<< d)]

def inducedWindow (c d : Nat) : Bool :=
  let vs := windowVertices c d
  (List.range 5).all fun i => (List.range 5).all fun j =>
    if i < j then (vs[i]! != vs[j]!) &&
      (adj9 vs[i]! vs[j]! == (j == i + 1)) else true

/-- After fixing the first two flips to 0 and 1, the third is fresh;
    the last cannot repeat the second or third flip. -/
theorem threeCentreDirections : ∀ c d : Fin 9,
    inducedWindow c.val d.val = true →
      c.val ≠ 0 ∧ c.val ≠ 1 ∧ d.val ≠ 1 ∧ d.val ≠ c.val := by
  decide +kernel

/-- After also naming the third flip 2, precisely 0120 and 012fresh survive.
    Renaming an arbitrary fresh coordinate to 3 is a separate symmetry argument. -/
theorem lastDirectionTable : ∀ d : Fin 9,
    inducedWindow 2 d.val = true ↔ d.val = 0 ∨ 3 ≤ d.val := by
  decide +kernel

def cycleVertex (i : Fin 8) : Nat := [0,1,3,7,15,14,12,8][i.val]!

/-- The diagram's eight vertices are distinct. -/
theorem cycleInjective : ∀ i j : Fin 8,
    cycleVertex i = cycleVertex j → i = j := by decide +kernel

/-- Every cycle vertex lies in Q9 (in fact in Q4). -/
theorem cycleInQ9 : ∀ i : Fin 8, cycleVertex i < 512 := by decide +kernel

/-- Exactly the consecutive cyclic pairs are Q9-adjacent: a genuine chordless C8. -/
theorem cycleAdjacency : ∀ i j : Fin 8, i ≠ j →
    (adj9 (cycleVertex i) (cycleVertex j) = true ↔
      (i.val + 1) % 8 = j.val ∨ (j.val + 1) % 8 = i.val) := by
  decide +kernel

#print axioms threeCentreDirections
#print axioms lastDirectionTable
#print axioms cycleInjective
#print axioms cycleInQ9
#print axioms cycleAdjacency
end Q9FiniteGeometry
