import PartitionData205_194
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,3])
    (d31 : a 31 ∈ [3])
    (d29 : a 29 ∈ [0,6])
    (d28 : a 28 ∈ [6])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [1])
    (d17 : a 17 ∈ [0,4])
    (d16 : a 16 ∈ [2])
    (d21 : a 21 ∈ [0,4])
    (d25 : a 25 ∈ [0,6])
    (d5 : a 5 ∈ [0,4])
    (d9 : a 9 ∈ [0,4])
    (d13 : a 13 ∈ [0,4])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 27 ∈ [3] ∧ a 29 ∈ [6] ∧ a 8 ∈ [1] ∧ a 17 ∈ [4] ∧ a 21 ∈ [4] ∧ a 25 ∈ [6] ∧ a 5 ∈ [4] ∧ a 9 ∈ [4] ∧ a 13 ∈ [4] := by
  have b0 : a 27 ≠ 0 := exclude [3] (edge r75) (a 27) (a 31) 0 d31 c75 (by decide +kernel)
  have t0 : a 27 ∈ [3] := remove (a 27) 0 [0,3] d27 b0
  have b1 : a 29 ≠ 0 := exclude [6] (fun u v => edge r76 v u) (a 29) (a 28) 0 d28 c76 (by decide +kernel)
  have t1 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b1
  have b2 : a 8 ≠ 0 := exclude [1] (edge r29) (a 8) (a 10) 0 d10 c29 (by decide +kernel)
  have t2 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b2
  have b3 : a 17 ≠ 0 := exclude [2] (fun u v => edge r48 v u) (a 17) (a 16) 0 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [4] := remove (a 17) 0 [0,4] d17 b3
  have b4 : a 21 ≠ 0 := exclude [4] (fun u v => edge r53 v u) (a 21) (a 17) 0 t3 c53 (by decide +kernel)
  have t4 : a 21 ∈ [4] := remove (a 21) 0 [0,4] d21 b4
  have b5 : a 25 ≠ 0 := exclude [3] (edge r71) (a 25) (a 27) 0 t0 c71 (by decide +kernel)
  have t5 : a 25 ∈ [6] := remove (a 25) 0 [0,6] d25 b5
  have b6 : a 5 ≠ 0 := exclude [4] (edge r22) (a 5) (a 21) 0 t4 c22 (by decide +kernel)
  have t6 : a 5 ∈ [4] := remove (a 5) 0 [0,4] d5 b6
  have b7 : a 9 ≠ 0 := exclude [1] (fun u v => edge r28 v u) (a 9) (a 8) 0 t2 c28 (by decide +kernel)
  have t7 : a 9 ∈ [4] := remove (a 9) 0 [0,4] d9 b7
  have b8 : a 13 ≠ 0 := exclude [4] (fun u v => edge r33 v u) (a 13) (a 9) 0 t7 c33 (by decide +kernel)
  have t8 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))
#print axioms chunk16
end PartitionCover205_194
