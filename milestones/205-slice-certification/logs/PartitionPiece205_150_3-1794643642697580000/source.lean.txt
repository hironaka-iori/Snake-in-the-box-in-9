import PartitionData205_150
namespace PartitionCover205_150
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0])
    (d3 : a 3 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    : a 2 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 2 ≠ 6 := exclude [0] (edge r8) (a 2) (a 6) 6 d6 c8 (by decide +kernel)
  have t0 : a 2 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] d2 b0
  have b1 : a 2 ≠ 7 := exclude [0] (edge r8) (a 2) (a 6) 7 d6 c8 (by decide +kernel)
  have t1 : a 2 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 2 ≠ 8 := exclude [0] (edge r8) (a 2) (a 6) 8 d6 c8 (by decide +kernel)
  have t2 : a 2 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 2) 8 [0,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 2 ≠ 9 := exclude [0] (edge r8) (a 2) (a 6) 9 d6 c8 (by decide +kernel)
  have t3 : a 2 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 2) 9 [0,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 2 ≠ 10 := exclude [0] (edge r8) (a 2) (a 6) 10 d6 c8 (by decide +kernel)
  have t4 : a 2 ∈ [0,11,12,13,14,15,16,17] := remove (a 2) 10 [0,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 2 ≠ 11 := exclude [0] (edge r8) (a 2) (a 6) 11 d6 c8 (by decide +kernel)
  have t5 : a 2 ∈ [0,12,13,14,15,16,17] := remove (a 2) 11 [0,11,12,13,14,15,16,17] t4 b5
  have b6 : a 2 ≠ 12 := exclude [0] (edge r8) (a 2) (a 6) 12 d6 c8 (by decide +kernel)
  have t6 : a 2 ∈ [0,13,14,15,16,17] := remove (a 2) 12 [0,12,13,14,15,16,17] t5 b6
  have b7 : a 2 ≠ 13 := exclude [0] (edge r8) (a 2) (a 6) 13 d6 c8 (by decide +kernel)
  have t7 : a 2 ∈ [0,14,15,16,17] := remove (a 2) 13 [0,13,14,15,16,17] t6 b7
  have b8 : a 2 ≠ 14 := exclude [0] (edge r8) (a 2) (a 6) 14 d6 c8 (by decide +kernel)
  have t8 : a 2 ∈ [0,15,16,17] := remove (a 2) 14 [0,14,15,16,17] t7 b8
  have b9 : a 2 ≠ 15 := exclude [0] (edge r8) (a 2) (a 6) 15 d6 c8 (by decide +kernel)
  have t9 : a 2 ∈ [0,16,17] := remove (a 2) 15 [0,15,16,17] t8 b9
  have b10 : a 2 ≠ 16 := exclude [0] (edge r8) (a 2) (a 6) 16 d6 c8 (by decide +kernel)
  have t10 : a 2 ∈ [0,17] := remove (a 2) 16 [0,16,17] t9 b10
  have b11 : a 2 ≠ 17 := exclude [0] (edge r8) (a 2) (a 6) 17 d6 c8 (by decide +kernel)
  have t11 : a 2 ∈ [0] := remove (a 2) 17 [0,17] t10 b11
  have b12 : a 3 ≠ 1 := exclude [0] (edge r10) (a 3) (a 7) 1 d7 c10 (by decide +kernel)
  have t12 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b12
  exact And.intro t11 (t12)
#print axioms chunk12
end PartitionCover205_150
