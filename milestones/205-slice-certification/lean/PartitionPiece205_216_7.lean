import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk28 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,8])
    (d22 : a 22 ∈ [0])
    (d21 : a 21 ∈ [0,2])
    (d29 : a 29 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,6,12,17])
    (d7 : a 7 ∈ [0,6,12])
    (d4 : a 4 ∈ [0,4])
    (d6 : a 6 ∈ [0])
    (d16 : a 16 ∈ [0,12])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 18 ∈ [0] ∧ a 21 ∈ [0] ∧ a 26 ∈ [0] ∧ a 28 ∈ [0] ∧ a 1 ∈ [0] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 18 ≠ 8 := exclude [0] (edge r56) (a 18) (a 22) 8 d22 c56 (by decide +kernel)
  have t0 : a 18 ∈ [0,2] := remove (a 18) 8 [0,2,8] d18 b0
  have b1 : a 21 ≠ 2 := exclude [0] (edge r64) (a 21) (a 29) 2 d29 c64 (by decide +kernel)
  have t1 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b1
  have b2 : a 26 ≠ 1 := exclude [0] (edge r74) (a 26) (a 30) 1 d30 c74 (by decide +kernel)
  have t2 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b2
  have b3 : a 28 ≠ 2 := exclude [0] (edge r77) (a 28) (a 30) 2 d30 c77 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b3
  have b4 : a 1 ≠ 1 := exclude [0] (edge r5) (a 1) (a 3) 1 d3 c5 (by decide +kernel)
  have t4 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b4
  have b5 : a 5 ≠ 6 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 6 t4 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,12,17] := remove (a 5) 6 [0,6,12,17] d5 b5
  have b6 : a 5 ≠ 12 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 12 t4 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,17] := remove (a 5) 12 [0,12,17] t5 b6
  have b7 : a 7 ≠ 6 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 6 d3 c13 (by decide +kernel)
  have t7 : a 7 ∈ [0,12] := remove (a 7) 6 [0,6,12] d7 b7
  have b8 : a 7 ≠ 12 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 12 d3 c13 (by decide +kernel)
  have t8 : a 7 ∈ [0] := remove (a 7) 12 [0,12] t7 b8
  have b9 : a 4 ≠ 4 := exclude [0] (edge r17) (a 4) (a 6) 4 d6 c17 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b9
  have b10 : a 5 ≠ 17 := exclude [0] (edge r20) (a 5) (a 7) 17 t8 c20 (by decide +kernel)
  have t10 : a 5 ∈ [0] := remove (a 5) 17 [0,17] t6 b10
  have b11 : a 16 ≠ 12 := exclude [0,2] (edge r49) (a 16) (a 18) 12 t0 c49 (by decide +kernel)
  have t11 : a 16 ∈ [0] := remove (a 16) 12 [0,12] d16 b11
  have b12 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t11 c49 (by decide +kernel)
  have t12 : a 18 ∈ [0] := remove (a 18) 2 [0,2] t0 b12
  exact And.intro t12 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t10 (And.intro t8 (And.intro t9 (t11))))))))
#print axioms chunk28
end PartitionCover205_216
