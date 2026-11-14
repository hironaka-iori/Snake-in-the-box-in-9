import PartitionData205_158
namespace PartitionCover205_158
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,7,8,9,10,11,12,13])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,4])
    (d10 : a 10 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (d9 : a 9 ∈ [0,1])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    : a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0,6,7] := by
  have b0 : a 15 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,8,9,10,11,12,13] := remove (a 15) 7 [0,7,8,9,10,11,12,13] d15 b0
  have b1 : a 15 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 8 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,9,10,11,12,13] := remove (a 15) 8 [0,8,9,10,11,12,13] t0 b1
  have b2 : a 15 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 9 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,10,11,12,13] := remove (a 15) 9 [0,9,10,11,12,13] t1 b2
  have b3 : a 15 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 10 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,11,12,13] := remove (a 15) 10 [0,10,11,12,13] t2 b3
  have b4 : a 15 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 11 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,12,13] := remove (a 15) 11 [0,11,12,13] t3 b4
  have b5 : a 15 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 12 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,13] := remove (a 15) 12 [0,12,13] t4 b5
  have b6 : a 15 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 13 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0] := remove (a 15) 13 [0,13] t5 b6
  have b7 : a 8 ≠ 4 := exclude [0,1,2,3] (edge r21) (a 8) (a 10) 4 d10 c21 (by decide +kernel)
  have t7 : a 8 ∈ [0] := remove (a 8) 4 [0,4] d8 b7
  have b8 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 1 t7 c21 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b8
  have b9 : a 10 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 2 t7 c21 (by decide +kernel)
  have t9 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t8 b9
  have b10 : a 10 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 3 t7 c21 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t9 b10
  have b11 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 1 d9 c23 (by decide +kernel)
  have t11 : a 11 ∈ [0,2,3,4,5,6,7] := remove (a 11) 1 [0,1,2,3,4,5,6,7] d11 b11
  have b12 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 2 d9 c23 (by decide +kernel)
  have t12 : a 11 ∈ [0,3,4,5,6,7] := remove (a 11) 2 [0,2,3,4,5,6,7] t11 b12
  have b13 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 3 d9 c23 (by decide +kernel)
  have t13 : a 11 ∈ [0,4,5,6,7] := remove (a 11) 3 [0,3,4,5,6,7] t12 b13
  have b14 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 4 d9 c23 (by decide +kernel)
  have t14 : a 11 ∈ [0,5,6,7] := remove (a 11) 4 [0,4,5,6,7] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 5 d9 c23 (by decide +kernel)
  have t15 : a 11 ∈ [0,6,7] := remove (a 11) 5 [0,5,6,7] t14 b15
  exact And.intro t6 (And.intro t7 (And.intro t10 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,6,7])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,8])
    (d12 : a 12 ∈ [0,8])
    (d3 : a 3 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    : a 11 ∈ [0] ∧ a 13 ∈ [0] ∧ a 12 ∈ [0] ∧ a 3 ∈ [0] ∧ a 9 ∈ [0] := by
  have b0 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 6 d9 c23 (by decide +kernel)
  have t0 : a 11 ∈ [0,7] := remove (a 11) 6 [0,6,7] d11 b0
  have b1 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r23 v u) (a 11) (a 9) 7 d9 c23 (by decide +kernel)
  have t1 : a 11 ∈ [0] := remove (a 11) 7 [0,7] t0 b1
  have b2 : a 13 ≠ 8 := exclude [0,1] (fun u v => edge r24 v u) (a 13) (a 9) 8 d9 c24 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 8 [0,8] d13 b2
  have b3 : a 12 ≠ 8 := exclude [0] (edge r28) (a 12) (a 13) 8 t2 c28 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 8 [0,8] d12 b3
  have b4 : a 3 ≠ 1 := exclude [0] (edge r10) (a 3) (a 7) 1 d7 c10 (by decide +kernel)
  have t4 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b4
  have b5 : a 9 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 1 d8 c20 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b5
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_158
