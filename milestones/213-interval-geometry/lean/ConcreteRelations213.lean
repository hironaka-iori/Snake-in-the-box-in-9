import ConcreteData213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

def partners : Nat → List Nat
  | 2 => [12,32,44,46,48,50,60,68,76]
  | 6 => [14,34,36,38,40,42,62,64,66]
  | 8 => [14,34,36,38,40,42,62,64,66]
  | 10 => [14,34,36,38,40,42,62,64,66]
  | 15 => [5,7,9,21,23,55,57,71]
  | 18 => [12,32,44,46,48,50,60,68,76]
  | 22 => [14,34,36,38,40,42,62,64,66]
  | 26 => [12,32,44,46,48,50,60,68,76]
  | 28 => [12,32,44,46,48,50,60,68,76]
  | 35 => [5,7,9,21,23,55,57,71]
  | 37 => [5,7,9,21,23,55,57,71]
  | 39 => [5,7,9,21,23,55,57,71]
  | 41 => [5,7,9,21,23,55,57,71]
  | 45 => [1,3,17,19,25,27,29,53,73]
  | 47 => [1,3,17,19,25,27,29,53,73]
  | 49 => [1,3,17,19,25,27,29,53,73]
  | 56 => [14,34,36,38,40,42,62,64,66]
  | 59 => [1,3,17,19,25,27,29,53,73]
  | 63 => [5,7,9,21,23,55,57,71]
  | 65 => [5,7,9,21,23,55,57,71]
  | 69 => [1,3,17,19,25,27,29,53,73]
  | 77 => [1,3,17,19,25,27,29,53,73]
  | _ => []

def withinPairs (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap (fun x => (xs.filter (fun y => decide (x < y))).map (fun y => (x,y)))

def familyPairs (C O : List Nat) : List (Nat × Nat) :=
  withinPairs C ++ withinPairs O ++
    O.flatMap (fun x => (C.filter (fun y => !(partners x).contains y)).map (fun y => (x,y)))

def requiredPairs : List (Nat × Nat) :=
  familyPairs chosen0 outside0 ++ familyPairs chosen1 outside1

def firstIndex : List Nat := [0,2,3,4,5,7,8,9,10,11,12,13,15,16,18,19,20,22,23,24,25,27,28,29,30,32,33,34,35,36,37,39,41,42,44,45,46,47,48,49,50,51,52,53,55,56,57,58,59,60,61,62,64,66,67,69,70,71,72,74,75,76,78,79,80,81,82,83,85,86,87,89,90,92,93,95,97,98]
def secondIndex : List Nat := [1,2,3,4,6,7,8,9,10,11,12,14,15,17,18,19,21,22,23,24,26,27,28,29,31,32,33,34,35,36,38,40,41,43,44,45,46,47,48,49,50,51,52,54,55,56,57,58,59,60,61,63,65,66,68,69,70,71,73,74,75,77,78,79,80,81,82,84,85,86,88,89,91,92,94,96,97,98]

def makeCertificate (xy : Nat × Nat) : Nat × Nat × Nat × Nat :=
  let x := xy.1
  let y := xy.2
  let a := firstIndex[x]!
  let b := firstIndex[y]!
  let i := if baseRaw a = opposite (baseRaw b) then secondIndex[x]! else a
  let j := if baseRaw i = opposite (baseRaw b) then secondIndex[y]! else b
  (x,y,i,j)

def certificates : List (Nat × Nat × Nat × Nat) := requiredPairs.map makeCertificate

def validCertificate (c : Nat × Nat × Nat × Nat) : Bool :=
  let (x,y,i,j) := c
  decide (i < 99 ∧ j < 99 ∧ groups[i]! = x ∧ groups[j]! = y ∧
    x ≠ y ∧ x % 2 = y % 2 ∧ baseRaw i ≠ opposite (baseRaw j))

theorem certificate_pair (xy : Nat × Nat) :
    ((makeCertificate xy).1, (makeCertificate xy).2.1) = xy := by rfl

#print axioms certificate_pair
end ConcreteGeometry213
