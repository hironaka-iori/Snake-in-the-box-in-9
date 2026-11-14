import PartitionData205_161
namespace PartitionCover205_161
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d1 : a 1 ∈ [0,1,2,3,4,5,6])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 1 ∈ [0] := by
  have b0 : a 1 ≠ 2 := exclude [0] (edge r4) (a 1) (a 3) 2 d3 c4 (by decide +kernel)
  have t0 : a 1 ∈ [0,1,3,4,5,6] := remove (a 1) 2 [0,1,2,3,4,5,6] d1 b0
  have b1 : a 1 ≠ 3 := exclude [0] (edge r4) (a 1) (a 3) 3 d3 c4 (by decide +kernel)
  have t1 : a 1 ∈ [0,1,4,5,6] := remove (a 1) 3 [0,1,3,4,5,6] t0 b1
  have b2 : a 1 ≠ 4 := exclude [0] (edge r4) (a 1) (a 3) 4 d3 c4 (by decide +kernel)
  have t2 : a 1 ∈ [0,1,5,6] := remove (a 1) 4 [0,1,4,5,6] t1 b2
  have b3 : a 1 ≠ 5 := exclude [0] (edge r4) (a 1) (a 3) 5 d3 c4 (by decide +kernel)
  have t3 : a 1 ∈ [0,1,6] := remove (a 1) 5 [0,1,5,6] t2 b3
  have b4 : a 1 ≠ 6 := exclude [0] (edge r4) (a 1) (a 3) 6 d3 c4 (by decide +kernel)
  have t4 : a 1 ∈ [0,1] := remove (a 1) 6 [0,1,6] t3 b4
  have b5 : a 1 ≠ 1 := exclude [0] (edge r5) (a 1) (a 5) 1 d5 c5 (by decide +kernel)
  have t5 : a 1 ∈ [0] := remove (a 1) 1 [0,1] t4 b5
  exact t5
#print axioms chunk20
end PartitionCover205_161
