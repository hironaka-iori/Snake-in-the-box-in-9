import PartitionData205_200
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,2,3,4,7,16,19,22,23])
    (d4 : a 4 ∈ [0,1,4,5,6,7,8,9])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2])
    (d6 : a 6 ∈ [0,4])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 12 ∈ [0,1,2,3,4,7,16,19] ∧ a 20 ∈ [0,1,2,3] ∧ a 7 ∈ [0,2] ∧ a 14 ∈ [0,1,2,12,13,14,17] := by
  have b0 : a 12 ≠ 22 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,2,3,4,7,16,19,23] := remove (a 12) 22 [0,1,2,3,4,7,16,19,22,23] d12 b0
  have b1 : a 12 ≠ 23 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 23 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,2,3,4,7,16,19] := remove (a 12) 23 [0,1,2,3,4,7,16,19,23] t0 b1
  have b2 : a 20 ≠ 4 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,2,3,5] := remove (a 20) 4 [0,1,2,3,4,5] d20 b2
  have b3 : a 20 ≠ 5 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,2,3] := remove (a 20) 5 [0,1,2,3,5] t2 b3
  have b4 : a 7 ≠ 1 := exclude [0,4] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t4 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b4
  have b5 : a 14 ≠ 3 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b5
  have b6 : a 14 ≠ 4 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,2,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,1,2,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 8 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,1,2,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 9 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,1,2,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 14 ≠ 10 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,11,12,13,14,15,16,17] := remove (a 14) 10 [0,1,2,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 14 ≠ 11 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,2,12,13,14,15,16,17] := remove (a 14) 11 [0,1,2,11,12,13,14,15,16,17] t12 b13
  have b14 : a 14 ≠ 15 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,2,12,13,14,16,17] := remove (a 14) 15 [0,1,2,12,13,14,15,16,17] t13 b14
  have b15 : a 14 ≠ 16 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,2,12,13,14,17] := remove (a 14) 16 [0,1,2,12,13,14,16,17] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,12,13,14,17])
    (d6 : a 6 ∈ [0,4])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,3,8,11,15,17])
    (d12 : a 12 ∈ [0,1,2,3,4,7,16,19])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 14 ∈ [0,1,2,12,13,14] ∧ a 22 ∈ [0,1,3,4] ∧ a 15 ∈ [0,1,2,6,7,8] ∧ a 9 ∈ [0,1,4,5,9,11] ∧ a 8 ∈ [0,3,8,11] ∧ a 12 ∈ [0,1,4,7,16,19] := by
  have b0 : a 14 ≠ 17 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,2,12,13,14] := remove (a 14) 17 [0,1,2,12,13,14,17] d14 b0
  have b1 : a 22 ≠ 2 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,3,4,5] := remove (a 22) 2 [0,1,2,3,4,5] d22 b1
  have b2 : a 22 ≠ 5 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,1,3,4] := remove (a 22) 5 [0,1,3,4,5] t1 b2
  have b3 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,4,5,6,7,8] := remove (a 15) 3 [0,1,2,3,4,5,6,7,8] d15 b3
  have b4 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,5,6,7,8] := remove (a 15) 4 [0,1,2,4,5,6,7,8] t3 b4
  have b5 : a 15 ≠ 5 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,2,6,7,8] := remove (a 15) 5 [0,1,2,5,6,7,8] t4 b5
  have b6 : a 9 ≠ 2 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d9 b6
  have b7 : a 9 ≠ 3 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 9 ≠ 6 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t8 : a 9 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 9) 6 [0,1,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 9 ≠ 7 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 7 d8 c28 (by decide +kernel)
  have t9 : a 9 ∈ [0,1,4,5,8,9,10,11] := remove (a 9) 7 [0,1,4,5,7,8,9,10,11] t8 b9
  have b10 : a 9 ≠ 8 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 8 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,4,5,9,10,11] := remove (a 9) 8 [0,1,4,5,8,9,10,11] t9 b10
  have b11 : a 9 ≠ 10 := exclude [0,3,8,11,15,17] (fun u v => edge r28 v u) (a 9) (a 8) 10 d8 c28 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,4,5,9,11] := remove (a 9) 10 [0,1,4,5,9,10,11] t10 b11
  have b12 : a 8 ≠ 15 := exclude [0,1,2,3,4,7,16,19] (edge r30) (a 8) (a 12) 15 d12 c30 (by decide +kernel)
  have t12 : a 8 ∈ [0,3,8,11,17] := remove (a 8) 15 [0,3,8,11,15,17] d8 b12
  have b13 : a 8 ≠ 17 := exclude [0,1,2,3,4,7,16,19] (edge r30) (a 8) (a 12) 17 d12 c30 (by decide +kernel)
  have t13 : a 8 ∈ [0,3,8,11] := remove (a 8) 17 [0,3,8,11,17] t12 b13
  have b14 : a 12 ≠ 2 := exclude [0,3,8,11] (fun u v => edge r30 v u) (a 12) (a 8) 2 t13 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,3,4,7,16,19] := remove (a 12) 2 [0,1,2,3,4,7,16,19] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,3,8,11] (fun u v => edge r30 v u) (a 12) (a 8) 3 t13 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,4,7,16,19] := remove (a 12) 3 [0,1,3,4,7,16,19] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t5 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk6 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,7,16,19])
    (d8 : a 8 ∈ [0,3,8,11])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,1,4,5,9,11])
    (d11 : a 11 ∈ [0,4,6,10,12,16])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 12 ∈ [0,1,4,19] ∧ a 24 ∈ [0,1,4,5,10,16] ∧ a 9 ∈ [0,4,9,11] := by
  have b0 : a 12 ≠ 7 := exclude [0,3,8,11] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,4,16,19] := remove (a 12) 7 [0,1,4,7,16,19] d12 b0
  have b1 : a 12 ≠ 16 := exclude [0,3,8,11] (fun u v => edge r30 v u) (a 12) (a 8) 16 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,4,19] := remove (a 12) 16 [0,1,4,16,19] t0 b1
  have b2 : a 24 ≠ 2 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 24 ≠ 6 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 24 ≠ 7 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 24 ≠ 8 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 24 ≠ 9 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,4,5,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 24 ≠ 11 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,4,5,10,12,13,14,15,16,17] := remove (a 24) 11 [0,1,4,5,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 24 ≠ 12 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 12 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,4,5,10,13,14,15,16,17] := remove (a 24) 12 [0,1,4,5,10,12,13,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 13 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,4,5,10,14,15,16,17] := remove (a 24) 13 [0,1,4,5,10,13,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 14 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,4,5,10,15,16,17] := remove (a 24) 14 [0,1,4,5,10,14,15,16,17] t10 b11
  have b12 : a 24 ≠ 15 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,4,5,10,16,17] := remove (a 24) 15 [0,1,4,5,10,15,16,17] t11 b12
  have b13 : a 24 ≠ 17 := exclude [0,3,8,11] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,4,5,10,16] := remove (a 24) 17 [0,1,4,5,10,16,17] t12 b13
  have b14 : a 9 ≠ 1 := exclude [0,4,6,10,12,16] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t14 : a 9 ∈ [0,4,5,9,11] := remove (a 9) 1 [0,1,4,5,9,11] d9 b14
  have b15 : a 9 ≠ 5 := exclude [0,4,6,10,12,16] (edge r32) (a 9) (a 11) 5 d11 c32 (by decide +kernel)
  have t15 : a 9 ∈ [0,4,9,11] := remove (a 9) 5 [0,4,5,9,11] t14 b15
  exact And.intro t1 (And.intro t13 (t15))

theorem chunk7 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,4,9,11])
    (d11 : a 11 ∈ [0,4,6,10,12,16])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 9 ∈ [0,4] ∧ a 11 ∈ [0,12] ∧ a 13 ∈ [0,1,12,13,14,15,16,17] := by
  have b0 : a 9 ≠ 9 := exclude [0,4,6,10,12,16] (edge r32) (a 9) (a 11) 9 d11 c32 (by decide +kernel)
  have t0 : a 9 ∈ [0,4,11] := remove (a 9) 9 [0,4,9,11] d9 b0
  have b1 : a 9 ≠ 11 := exclude [0,4,6,10,12,16] (edge r32) (a 9) (a 11) 11 d11 c32 (by decide +kernel)
  have t1 : a 9 ∈ [0,4] := remove (a 9) 11 [0,4,11] t0 b1
  have b2 : a 11 ≠ 4 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 4 t1 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,6,10,12,16] := remove (a 11) 4 [0,4,6,10,12,16] d11 b2
  have b3 : a 11 ≠ 6 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 6 t1 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,10,12,16] := remove (a 11) 6 [0,6,10,12,16] t2 b3
  have b4 : a 11 ≠ 10 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 10 t1 c32 (by decide +kernel)
  have t4 : a 11 ∈ [0,12,16] := remove (a 11) 10 [0,10,12,16] t3 b4
  have b5 : a 11 ≠ 16 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 16 t1 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0,12] := remove (a 11) 16 [0,12,16] t4 b5
  have b6 : a 13 ≠ 2 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 2 t1 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d13 b6
  have b7 : a 13 ≠ 3 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 3 t1 c33 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 13 ≠ 4 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 4 t1 c33 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 13 ≠ 5 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 5 t1 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 13 ≠ 6 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 6 t1 c33 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 13 ≠ 7 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 7 t1 c33 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 13 ≠ 8 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 8 t1 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 13) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 13 ≠ 9 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 9 t1 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 13) 9 [0,1,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 13 ≠ 10 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 10 t1 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 13) 10 [0,1,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 13 ≠ 11 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 11 t1 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,12,13,14,15,16,17] := remove (a 13) 11 [0,1,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t5 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_200
