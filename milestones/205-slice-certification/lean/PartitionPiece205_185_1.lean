import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,3,4,6,7,8,9,10,11,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,2,6,8,12,13,14,16])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d5 : a 5 ∈ [0,3,4,5,6,7,9,10,12,13,14,15,17,18])
    (d9 : a 9 ∈ [0,1,3,4,5,7])
    (d8 : a 8 ∈ [0,1,2,3])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 11 ∈ [0,2,3,4,6,7,8,9,10,11,18,20,21,22] ∧ a 19 ∈ [0,2,6,7,10,11] ∧ a 12 ∈ [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] ∧ a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] ∧ a 9 ∈ [0,4,5,7] := by
  have b0 : a 11 ≠ 19 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r14 v u) (a 11) (a 3) 19 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,3,4,6,7,8,9,10,11,18,20,21,22,23] := remove (a 11) 19 [0,2,3,4,6,7,8,9,10,11,18,19,20,21,22,23] d11 b0
  have b1 : a 11 ≠ 23 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r14 v u) (a 11) (a 3) 23 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,3,4,6,7,8,9,10,11,18,20,21,22] := remove (a 11) 23 [0,2,3,4,6,7,8,9,10,11,18,20,21,22,23] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 19 ≠ 4 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 19) 4 [0,2,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 19 ≠ 5 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,2,6,7,8,9,10,11] := remove (a 19) 5 [0,2,5,6,7,8,9,10,11] t4 b5
  have b6 : a 19 ≠ 8 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0,2,6,7,9,10,11] := remove (a 19) 8 [0,2,6,7,8,9,10,11] t5 b6
  have b7 : a 19 ≠ 9 := exclude [0,2,6,8,12,13,14,16] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,2,6,7,10,11] := remove (a 19) 9 [0,2,6,7,9,10,11] t6 b7
  have b8 : a 12 ≠ 1 := exclude [0,1,2,3,4,5] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b8
  have b9 : a 12 ≠ 5 := exclude [0,1,2,3,4,5] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 8 := exclude [0,1,2,3,4,5] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 22 := exclude [0,1,2,3,4,5] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 22 [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 13 ≠ 18 := exclude [0,3,4,5,6,7,9,10,12,13,14,15,17,18] (fun u v => edge r21 v u) (a 13) (a 5) 18 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23] := remove (a 13) 18 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d13 b12
  have b13 : a 13 ≠ 19 := exclude [0,3,4,5,6,7,9,10,12,13,14,15,17,18] (fun u v => edge r21 v u) (a 13) (a 5) 19 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 19 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23] t12 b13
  have b14 : a 9 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,3,4,5,7] := remove (a 9) 1 [0,1,3,4,5,7] d9 b14
  have b15 : a 9 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,4,5,7] := remove (a 9) 3 [0,3,4,5,7] t14 b15
  exact And.intro t1 (And.intro t7 (And.intro t11 (And.intro t13 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,4,5,7])
    (d8 : a 8 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,2,8,10,14,15,16,17,18,20,22,23])
    (d12 : a 12 ∈ [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 9 ∈ [0,4] ∧ a 8 ∈ [0,2] ∧ a 10 ∈ [0,23] ∧ a 12 ∈ [0,2,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] := by
  have b0 : a 9 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t0 : a 9 ∈ [0,4,7] := remove (a 9) 5 [0,4,5,7] d9 b0
  have b1 : a 9 ≠ 7 := exclude [0,1,2,3] (fun u v => edge r28 v u) (a 9) (a 8) 7 d8 c28 (by decide +kernel)
  have t1 : a 9 ∈ [0,4] := remove (a 9) 7 [0,4,7] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0,2,8,10,14,15,16,17,18,20,22,23] (edge r29) (a 8) (a 10) 1 d10 c29 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0,2,8,10,14,15,16,17,18,20,22,23] (edge r29) (a 8) (a 10) 3 d10 c29 (by decide +kernel)
  have t3 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t2 b3
  have b4 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 2 t3 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,8,10,14,15,16,17,18,20,22,23] := remove (a 10) 2 [0,2,8,10,14,15,16,17,18,20,22,23] d10 b4
  have b5 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 8 t3 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0,10,14,15,16,17,18,20,22,23] := remove (a 10) 8 [0,8,10,14,15,16,17,18,20,22,23] t4 b5
  have b6 : a 10 ≠ 10 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 10 t3 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,14,15,16,17,18,20,22,23] := remove (a 10) 10 [0,10,14,15,16,17,18,20,22,23] t5 b6
  have b7 : a 10 ≠ 14 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 14 t3 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,15,16,17,18,20,22,23] := remove (a 10) 14 [0,14,15,16,17,18,20,22,23] t6 b7
  have b8 : a 10 ≠ 15 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 15 t3 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,16,17,18,20,22,23] := remove (a 10) 15 [0,15,16,17,18,20,22,23] t7 b8
  have b9 : a 10 ≠ 16 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 16 t3 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,17,18,20,22,23] := remove (a 10) 16 [0,16,17,18,20,22,23] t8 b9
  have b10 : a 10 ≠ 17 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 17 t3 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,18,20,22,23] := remove (a 10) 17 [0,17,18,20,22,23] t9 b10
  have b11 : a 10 ≠ 18 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 18 t3 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0,20,22,23] := remove (a 10) 18 [0,18,20,22,23] t10 b11
  have b12 : a 10 ≠ 20 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 20 t3 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0,22,23] := remove (a 10) 20 [0,20,22,23] t11 b12
  have b13 : a 10 ≠ 22 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 22 t3 c29 (by decide +kernel)
  have t13 : a 10 ∈ [0,23] := remove (a 10) 22 [0,22,23] t12 b13
  have b14 : a 12 ≠ 4 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 4 t3 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 4 [0,2,3,4,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] d12 b14
  have b15 : a 12 ≠ 6 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 6 t3 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,2,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 6 [0,2,3,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t13 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,2,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23])
    (d8 : a 8 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 12 ∈ [0,2,3,9] ∧ a 24 ∈ [0,3,4,5,6] := by
  have b0 : a 12 ≠ 7 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 7 [0,2,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,23] d12 b0
  have b1 : a 12 ≠ 10 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 10 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,2,3,9,11,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 10 [0,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,23] t0 b1
  have b2 : a 12 ≠ 11 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 11 d8 c30 (by decide +kernel)
  have t2 : a 12 ∈ [0,2,3,9,12,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 11 [0,2,3,9,11,12,13,14,15,16,17,18,19,20,21,23] t1 b2
  have b3 : a 12 ≠ 12 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 12 d8 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0,2,3,9,13,14,15,16,17,18,19,20,21,23] := remove (a 12) 12 [0,2,3,9,12,13,14,15,16,17,18,19,20,21,23] t2 b3
  have b4 : a 12 ≠ 13 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 13 d8 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,2,3,9,14,15,16,17,18,19,20,21,23] := remove (a 12) 13 [0,2,3,9,13,14,15,16,17,18,19,20,21,23] t3 b4
  have b5 : a 12 ≠ 14 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 14 d8 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,2,3,9,15,16,17,18,19,20,21,23] := remove (a 12) 14 [0,2,3,9,14,15,16,17,18,19,20,21,23] t4 b5
  have b6 : a 12 ≠ 15 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 15 d8 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3,9,16,17,18,19,20,21,23] := remove (a 12) 15 [0,2,3,9,15,16,17,18,19,20,21,23] t5 b6
  have b7 : a 12 ≠ 16 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 16 d8 c30 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,3,9,17,18,19,20,21,23] := remove (a 12) 16 [0,2,3,9,16,17,18,19,20,21,23] t6 b7
  have b8 : a 12 ≠ 17 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 17 d8 c30 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,3,9,18,19,20,21,23] := remove (a 12) 17 [0,2,3,9,17,18,19,20,21,23] t7 b8
  have b9 : a 12 ≠ 18 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 18 d8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [0,2,3,9,19,20,21,23] := remove (a 12) 18 [0,2,3,9,18,19,20,21,23] t8 b9
  have b10 : a 12 ≠ 19 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 19 d8 c30 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,3,9,20,21,23] := remove (a 12) 19 [0,2,3,9,19,20,21,23] t9 b10
  have b11 : a 12 ≠ 20 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 20 d8 c30 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,3,9,21,23] := remove (a 12) 20 [0,2,3,9,20,21,23] t10 b11
  have b12 : a 12 ≠ 21 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 21 d8 c30 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,3,9,23] := remove (a 12) 21 [0,2,3,9,21,23] t11 b12
  have b13 : a 12 ≠ 23 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 23 d8 c30 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,3,9] := remove (a 12) 23 [0,2,3,9,23] t12 b13
  have b14 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,3,4,5,6] := remove (a 24) 1 [0,1,2,3,4,5,6] d24 b14
  have b15 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,3,4,5,6] := remove (a 24) 2 [0,2,3,4,5,6] t14 b15
  exact And.intro t13 (t15)

theorem chunk7 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,3,4,5,6])
    (d8 : a 8 ∈ [0,2])
    (d11 : a 11 ∈ [0,2,3,4,6,7,8,9,10,11,18,20,21,22])
    (d9 : a 9 ∈ [0,4])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 24 ∈ [0,4] ∧ a 11 ∈ [0,2,7,9,10,11,18,20] ∧ a 13 ∈ [0,1,2,10,11,12,13,14,15,16,17,20,21,22,23] := by
  have b0 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,4,5,6] := remove (a 24) 3 [0,3,4,5,6] d24 b0
  have b1 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,4,6] := remove (a 24) 5 [0,4,5,6] t0 b1
  have b2 : a 24 ≠ 6 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,4] := remove (a 24) 6 [0,4,6] t1 b2
  have b3 : a 11 ≠ 3 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,4,6,7,8,9,10,11,18,20,21,22] := remove (a 11) 3 [0,2,3,4,6,7,8,9,10,11,18,20,21,22] d11 b3
  have b4 : a 11 ≠ 4 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 4 d9 c32 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,6,7,8,9,10,11,18,20,21,22] := remove (a 11) 4 [0,2,4,6,7,8,9,10,11,18,20,21,22] t3 b4
  have b5 : a 11 ≠ 6 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 6 d9 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,7,8,9,10,11,18,20,21,22] := remove (a 11) 6 [0,2,6,7,8,9,10,11,18,20,21,22] t4 b5
  have b6 : a 11 ≠ 8 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 8 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,2,7,9,10,11,18,20,21,22] := remove (a 11) 8 [0,2,7,8,9,10,11,18,20,21,22] t5 b6
  have b7 : a 11 ≠ 21 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 21 d9 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,2,7,9,10,11,18,20,22] := remove (a 11) 21 [0,2,7,9,10,11,18,20,21,22] t6 b7
  have b8 : a 11 ≠ 22 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 22 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,7,9,10,11,18,20] := remove (a 11) 22 [0,2,7,9,10,11,18,20,22] t7 b8
  have b9 : a 13 ≠ 3 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] d13 b9
  have b10 : a 13 ≠ 4 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 4 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] t9 b10
  have b11 : a 13 ≠ 5 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 5 [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] t10 b11
  have b12 : a 13 ≠ 6 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 6 d9 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 6 [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] t11 b12
  have b13 : a 13 ≠ 7 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 7 d9 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,8,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 7 [0,1,2,7,8,9,10,11,12,13,14,15,16,17,20,21,22,23] t12 b13
  have b14 : a 13 ≠ 8 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 8 d9 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,2,9,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 8 [0,1,2,8,9,10,11,12,13,14,15,16,17,20,21,22,23] t13 b14
  have b15 : a 13 ≠ 9 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 9 d9 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,2,10,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 9 [0,1,2,9,10,11,12,13,14,15,16,17,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t8 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_185
