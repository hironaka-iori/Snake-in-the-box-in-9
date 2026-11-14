import PartitionData205_193
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,6])
    (d30 : a 30 ∈ [6])
    (d31 : a 31 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [4])
    (d9 : a 9 ∈ [0,3])
    (d8 : a 8 ∈ [3])
    (d17 : a 17 ∈ [0,3])
    (d16 : a 16 ∈ [3])
    (d18 : a 18 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (d25 : a 25 ∈ [6])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 26 ∈ [6] ∧ a 31 ∈ [1] ∧ a 5 ∈ [1] ∧ a 9 ∈ [3] ∧ a 17 ∈ [3] ∧ a 18 ∈ [6] ∧ a 27 ∈ [3] := by
  have b0 : a 26 ≠ 0 := exclude [6] (edge r74) (a 26) (a 30) 0 d30 c74 (by decide +kernel)
  have t0 : a 26 ∈ [6] := remove (a 26) 0 [0,6] d26 b0
  have b1 : a 31 ≠ 0 := exclude [6] (fun u v => edge r79 v u) (a 31) (a 30) 0 d30 c79 (by decide +kernel)
  have t1 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b1
  have b2 : a 5 ≠ 0 := exclude [4] (fun u v => edge r16 v u) (a 5) (a 4) 0 d4 c16 (by decide +kernel)
  have t2 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b2
  have b3 : a 9 ≠ 0 := exclude [3] (fun u v => edge r28 v u) (a 9) (a 8) 0 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [3] := remove (a 9) 0 [0,3] d9 b3
  have b4 : a 17 ≠ 0 := exclude [3] (fun u v => edge r48 v u) (a 17) (a 16) 0 d16 c48 (by decide +kernel)
  have t4 : a 17 ∈ [3] := remove (a 17) 0 [0,3] d17 b4
  have b5 : a 18 ≠ 0 := exclude [3] (fun u v => edge r49 v u) (a 18) (a 16) 0 d16 c49 (by decide +kernel)
  have t5 : a 18 ∈ [6] := remove (a 18) 0 [0,6] d18 b5
  have b6 : a 27 ≠ 0 := exclude [6] (fun u v => edge r71 v u) (a 27) (a 25) 0 d25 c71 (by decide +kernel)
  have t6 : a 27 ∈ [3] := remove (a 27) 0 [0,3] d27 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk16
end PartitionCover205_193
