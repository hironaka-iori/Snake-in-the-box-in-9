import ConcreteData213
import WordParity214

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteParity214
open ConcreteGeometry213 WordParity214 IndexedCriterion206

def word (u : Nat) : List Bool := (List.range 6).map (fun k => u.testBit k)

def boundary : List Nat := [1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 21, 22, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 38, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 63, 65, 66, 68, 69, 70, 71, 73, 74, 75, 77, 78, 79, 80, 81, 82, 84, 85, 86, 88, 89, 91, 92, 94, 96, 97]

theorem boundary_certificate :
    (List.range 77).all (fun g => decide
      (boundary[g]! < 98 ∧ groups[boundary[g]!]! = g ∧
       groups[boundary[g]!+1]! = g+1 ∧
       baseRaw (boundary[g]!) = baseRaw (boundary[g]!+1))) = true := by
  decide +kernel

def pool (b : Bool) : List Nat :=
  (List.range 64).filter (fun u => parity (word u) == b)

def parityMask (b : Bool) : Nat := if b then 7608434000728254870 else 10838310072981296745

theorem pool_lengths : (pool false).length = 32 ∧ (pool true).length = 32 := by
  decide +kernel

theorem mask_certificate :
    (List.range 64).all (fun u =>
      (parityMask false).testBit u == (parity (word u) == false) &&
      (parityMask true).testBit u == (parity (word u) == true)) = true := by
  decide +kernel

#print axioms boundary_certificate
#print axioms pool_lengths
#print axioms mask_certificate
end ConcreteParity214
