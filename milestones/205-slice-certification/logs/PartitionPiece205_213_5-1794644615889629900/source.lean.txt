import PartitionData205_213
namespace PartitionCover205_213
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,13,14,15,16,17])
    (d27 : a 27 ∈ [0])
    (d1 : a 1 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (d3 : a 3 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (d10 : a 10 ∈ [0,2])
    (d8 : a 8 ∈ [0])
    (d9 : a 9 ∈ [0,6])
    (d11 : a 11 ∈ [0])
    (d18 : a 18 ∈ [0,1,18,19])
    (d16 : a 16 ∈ [0])
    (d22 : a 22 ∈ [0,10])
    (d2 : a 2 ∈ [0,1])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 31 ∈ [0] ∧ a 1 ∈ [0] ∧ a 3 ∈ [0] ∧ a 10 ∈ [0] ∧ a 9 ∈ [0] ∧ a 18 ∈ [0] ∧ a 22 ∈ [0] ∧ a 2 ∈ [0] := by
  have b0 : a 31 ≠ 13 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 13 d27 c75 (by decide +kernel)
  have t0 : a 31 ∈ [0,14,15,16,17] := remove (a 31) 13 [0,13,14,15,16,17] d31 b0
  have b1 : a 31 ≠ 14 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 14 d27 c75 (by decide +kernel)
  have t1 : a 31 ∈ [0,15,16,17] := remove (a 31) 14 [0,14,15,16,17] t0 b1
  have b2 : a 31 ≠ 15 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 15 d27 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,16,17] := remove (a 31) 15 [0,15,16,17] t1 b2
  have b3 : a 31 ≠ 16 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 16 d27 c75 (by decide +kernel)
  have t3 : a 31 ∈ [0,17] := remove (a 31) 16 [0,16,17] t2 b3
  have b4 : a 31 ≠ 17 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 17 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 17 [0,17] t3 b4
  have b5 : a 1 ≠ 1 := exclude [0] (edge r6) (a 1) (a 5) 1 d5 c6 (by decide +kernel)
  have t5 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b5
  have b6 : a 3 ≠ 1 := exclude [0] (edge r13) (a 3) (a 7) 1 d7 c13 (by decide +kernel)
  have t6 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b6
  have b7 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b7
  have b8 : a 9 ≠ 6 := exclude [0] (edge r32) (a 9) (a 11) 6 d11 c32 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 6 [0,6] d9 b8
  have b9 : a 18 ≠ 18 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 18 d16 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,19] := remove (a 18) 18 [0,1,18,19] d18 b9
  have b10 : a 18 ≠ 19 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 19 d16 c49 (by decide +kernel)
  have t10 : a 18 ∈ [0,1] := remove (a 18) 19 [0,1,19] t9 b10
  have b11 : a 18 ≠ 1 := exclude [0,10] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 1 [0,1] t10 b11
  have b12 : a 22 ≠ 10 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 10 t11 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0] := remove (a 22) 10 [0,10] d22 b12
  have b13 : a 2 ≠ 1 := exclude [0] (edge r9) (a 2) (a 3) 1 t6 c9 (by decide +kernel)
  have t13 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b13
  exact And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t11 (And.intro t12 (t13)))))))
#print axioms chunk20
end PartitionCover205_213
