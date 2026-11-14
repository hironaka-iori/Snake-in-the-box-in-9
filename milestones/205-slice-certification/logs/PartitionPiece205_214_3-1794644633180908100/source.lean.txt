import PartitionData205_214
namespace PartitionCover205_214
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2])
    (d3 : a 3 ∈ [0])
    (d19 : a 19 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d10 : a 10 ∈ [0,2])
    (d8 : a 8 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d18 : a 18 ∈ [0,2])
    (d26 : a 26 ∈ [0])
    (d1 : a 1 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 5 ∈ [0] ∧ a 10 ∈ [0] ∧ a 27 ∈ [0] ∧ a 18 ∈ [0] ∧ a 1 ∈ [0] ∧ a 2 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b0
  have b1 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b1
  have b2 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t2 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b2
  have b3 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b3
  have b4 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t0 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b4
  have b5 : a 18 ≠ 2 := exclude [0] (edge r57) (a 18) (a 26) 2 d26 c57 (by decide +kernel)
  have t5 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b5
  have b6 : a 1 ≠ 1 := exclude [0] (edge r5) (a 1) (a 3) 1 d3 c5 (by decide +kernel)
  have t6 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b6
  have b7 : a 2 ≠ 1 := exclude [0] (edge r9) (a 2) (a 3) 1 d3 c9 (by decide +kernel)
  have t7 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b7
  have b8 : a 22 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 2 t5 c56 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))
#print axioms chunk12
end PartitionCover205_214
