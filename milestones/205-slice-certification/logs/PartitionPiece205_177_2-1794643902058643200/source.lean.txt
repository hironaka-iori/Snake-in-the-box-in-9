import PartitionData205_177
namespace PartitionCover205_177
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d18 : a 18 ∈ [1])
    (d6 : a 6 ∈ [0,4])
    (d14 : a 14 ∈ [1])
    (d7 : a 7 ∈ [0,5])
    (d15 : a 15 ∈ [1])
    (d20 : a 20 ∈ [0,8])
    (d28 : a 28 ∈ [3])
    (d3 : a 3 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d5 : a 5 ∈ [0,4])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 2 ∈ [1] ∧ a 6 ∈ [4] ∧ a 7 ∈ [5] ∧ a 20 ∈ [8] ∧ a 3 ∈ [2] ∧ a 4 ∈ [4] ∧ a 5 ∈ [4] := by
  have b0 : a 2 ≠ 0 := exclude [1] (edge r12) (a 2) (a 18) 0 d18 c12 (by decide +kernel)
  have t0 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b0
  have b1 : a 6 ≠ 0 := exclude [1] (edge r24) (a 6) (a 14) 0 d14 c24 (by decide +kernel)
  have t1 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b1
  have b2 : a 7 ≠ 0 := exclude [1] (edge r26) (a 7) (a 15) 0 d15 c26 (by decide +kernel)
  have t2 : a 7 ∈ [5] := remove (a 7) 0 [0,5] d7 b2
  have b3 : a 20 ≠ 0 := exclude [3] (edge r62) (a 20) (a 28) 0 d28 c62 (by decide +kernel)
  have t3 : a 20 ∈ [8] := remove (a 20) 0 [0,8] d20 b3
  have b4 : a 3 ≠ 0 := exclude [5] (edge r13) (a 3) (a 7) 0 t2 c13 (by decide +kernel)
  have t4 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b4
  have b5 : a 4 ≠ 0 := exclude [4] (edge r17) (a 4) (a 6) 0 t1 c17 (by decide +kernel)
  have t5 : a 4 ∈ [4] := remove (a 4) 0 [0,4] d4 b5
  have b6 : a 5 ≠ 0 := exclude [5] (edge r20) (a 5) (a 7) 0 t2 c20 (by decide +kernel)
  have t6 : a 5 ∈ [4] := remove (a 5) 0 [0,4] d5 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk8
end PartitionCover205_177
