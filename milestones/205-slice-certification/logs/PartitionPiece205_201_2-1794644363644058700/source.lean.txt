import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,4,5])
    (d6 : a 6 ∈ [0,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 7 ∈ [0,4] ∧ a 14 ∈ [0,1,2,12,13,16] ∧ a 22 ∈ [0,1,2,3,7,8,9,10,11] := by
  have b0 : a 7 ≠ 5 := exclude [0,5] (fun u v => edge r23 v u) (a 7) (a 6) 5 d6 c23 (by decide +kernel)
  have t0 : a 7 ∈ [0,4] := remove (a 7) 5 [0,4,5] d7 b0
  have b1 : a 14 ≠ 3 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b1
  have b2 : a 14 ≠ 4 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 5 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 6 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 7 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,1,2,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 8 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,1,2,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 9 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,2,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,1,2,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 10 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,2,11,12,13,14,15,16,17] := remove (a 14) 10 [0,1,2,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 11 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,2,12,13,14,15,16,17] := remove (a 14) 11 [0,1,2,11,12,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 14 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,12,13,15,16,17] := remove (a 14) 14 [0,1,2,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 15 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,12,13,16,17] := remove (a 14) 15 [0,1,2,12,13,15,16,17] t10 b11
  have b12 : a 14 ≠ 17 := exclude [0,5] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,12,13,16] := remove (a 14) 17 [0,1,2,12,13,16,17] t11 b12
  have b13 : a 22 ≠ 4 := exclude [0,5] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 22) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b13
  have b14 : a 22 ≠ 5 := exclude [0,5] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 22) 5 [0,1,2,3,5,6,7,8,9,10,11] t13 b14
  have b15 : a 22 ≠ 6 := exclude [0,5] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 22) 6 [0,1,2,3,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t12 (t15))

theorem chunk9 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,7,8,9,10,11])
    (d6 : a 6 ∈ [0,5])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,4])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,8])
    (d12 : a 12 ∈ [0,1,3,4,5,7,8,9,11,13,15,17])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 22 ∈ [0,1,2,3,8,9,10,11] ∧ a 15 ∈ [0,1,2,6,7,8] ∧ a 23 ∈ [0,1,2] ∧ a 9 ∈ [0,2] ∧ a 12 ∈ [0,4,5,7,8,9,11,13,15,17] := by
  have b0 : a 22 ≠ 7 := exclude [0,5] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,2,3,8,9,10,11] := remove (a 22) 7 [0,1,2,3,7,8,9,10,11] d22 b0
  have b1 : a 15 ≠ 3 := exclude [0,4] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,4,5,6,7,8] := remove (a 15) 3 [0,1,2,3,4,5,6,7,8] d15 b1
  have b2 : a 15 ≠ 4 := exclude [0,4] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,5,6,7,8] := remove (a 15) 4 [0,1,2,4,5,6,7,8] t1 b2
  have b3 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,6,7,8] := remove (a 15) 5 [0,1,2,5,6,7,8] t2 b3
  have b4 : a 23 ≠ 3 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,4,5,6,7,8] := remove (a 23) 3 [0,1,2,3,4,5,6,7,8] d23 b4
  have b5 : a 23 ≠ 4 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,5,6,7,8] := remove (a 23) 4 [0,1,2,4,5,6,7,8] t4 b5
  have b6 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,6,7,8] := remove (a 23) 5 [0,1,2,5,6,7,8] t5 b6
  have b7 : a 23 ≠ 6 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,7,8] := remove (a 23) 6 [0,1,2,6,7,8] t6 b7
  have b8 : a 23 ≠ 7 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,8] := remove (a 23) 7 [0,1,2,7,8] t7 b8
  have b9 : a 23 ≠ 8 := exclude [0,4] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2] := remove (a 23) 8 [0,1,2,8] t8 b9
  have b10 : a 9 ≠ 1 := exclude [0,8] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b10
  have b11 : a 9 ≠ 3 := exclude [0,8] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t11 : a 9 ∈ [0,2,4,5] := remove (a 9) 3 [0,2,3,4,5] t10 b11
  have b12 : a 9 ≠ 4 := exclude [0,8] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,5] := remove (a 9) 4 [0,2,4,5] t11 b12
  have b13 : a 9 ≠ 5 := exclude [0,8] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,2] := remove (a 9) 5 [0,2,5] t12 b13
  have b14 : a 12 ≠ 1 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,3,4,5,7,8,9,11,13,15,17] := remove (a 12) 1 [0,1,3,4,5,7,8,9,11,13,15,17] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 3 d8 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,4,5,7,8,9,11,13,15,17] := remove (a 12) 3 [0,3,4,5,7,8,9,11,13,15,17] t14 b15
  exact And.intro t0 (And.intro t3 (And.intro t9 (And.intro t13 (t15))))

theorem chunk10 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,4,5,7,8,9,11,13,15,17])
    (d8 : a 8 ∈ [0,8])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 12 ∈ [0,8,15,17] ∧ a 24 ∈ [0,6,12,13,14,15,16,17] := by
  have b0 : a 12 ≠ 4 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 4 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,5,7,8,9,11,13,15,17] := remove (a 12) 4 [0,4,5,7,8,9,11,13,15,17] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 5 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,7,8,9,11,13,15,17] := remove (a 12) 5 [0,5,7,8,9,11,13,15,17] t0 b1
  have b2 : a 12 ≠ 7 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t2 : a 12 ∈ [0,8,9,11,13,15,17] := remove (a 12) 7 [0,7,8,9,11,13,15,17] t1 b2
  have b3 : a 12 ≠ 9 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 9 d8 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0,8,11,13,15,17] := remove (a 12) 9 [0,8,9,11,13,15,17] t2 b3
  have b4 : a 12 ≠ 11 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 11 d8 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,8,13,15,17] := remove (a 12) 11 [0,8,11,13,15,17] t3 b4
  have b5 : a 12 ≠ 13 := exclude [0,8] (fun u v => edge r30 v u) (a 12) (a 8) 13 d8 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,8,15,17] := remove (a 12) 13 [0,8,13,15,17] t4 b5
  have b6 : a 24 ≠ 1 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b6
  have b7 : a 24 ≠ 2 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 24 ≠ 3 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 24 ≠ 4 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 5 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 7 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 24 ≠ 8 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 24 ≠ 9 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,6,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 24 ≠ 10 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 24) 10 [0,6,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 24 ≠ 11 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,6,12,13,14,15,16,17] := remove (a 24) 11 [0,6,11,12,13,14,15,16,17] t14 b15
  exact And.intro t5 (t15)

theorem chunk11 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,12,13,14,15,16,17])
    (d8 : a 8 ∈ [0,8])
    (d11 : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,16,17])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,2,4])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,6,14,15] ∧ a 11 ∈ [0,1,16,17] ∧ a 13 ∈ [0,4] ∧ a 25 ∈ [0,1,3,4,7,8] := by
  have b0 : a 24 ≠ 12 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 12 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,6,13,14,15,16,17] := remove (a 24) 12 [0,6,12,13,14,15,16,17] d24 b0
  have b1 : a 24 ≠ 13 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,6,14,15,16,17] := remove (a 24) 13 [0,6,13,14,15,16,17] t0 b1
  have b2 : a 24 ≠ 16 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,6,14,15,17] := remove (a 24) 16 [0,6,14,15,16,17] t1 b2
  have b3 : a 24 ≠ 17 := exclude [0,8] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,6,14,15] := remove (a 24) 17 [0,6,14,15,17] t2 b3
  have b4 : a 11 ≠ 4 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 4 d9 c32 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,5,6,7,10,11,12,13,16,17] := remove (a 11) 4 [0,1,4,5,6,7,10,11,12,13,16,17] d11 b4
  have b5 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 5 d9 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,6,7,10,11,12,13,16,17] := remove (a 11) 5 [0,1,5,6,7,10,11,12,13,16,17] t4 b5
  have b6 : a 11 ≠ 6 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 6 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,7,10,11,12,13,16,17] := remove (a 11) 6 [0,1,6,7,10,11,12,13,16,17] t5 b6
  have b7 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,10,11,12,13,16,17] := remove (a 11) 7 [0,1,7,10,11,12,13,16,17] t6 b7
  have b8 : a 11 ≠ 10 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 10 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,11,12,13,16,17] := remove (a 11) 10 [0,1,10,11,12,13,16,17] t7 b8
  have b9 : a 11 ≠ 11 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 11 d9 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,12,13,16,17] := remove (a 11) 11 [0,1,11,12,13,16,17] t8 b9
  have b10 : a 11 ≠ 12 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 12 d9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,13,16,17] := remove (a 11) 12 [0,1,12,13,16,17] t9 b10
  have b11 : a 11 ≠ 13 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 13 d9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,1,16,17] := remove (a 11) 13 [0,1,13,16,17] t10 b11
  have b12 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,4] := remove (a 13) 2 [0,2,4] d13 b12
  have b13 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,3,4,5,6,7,8] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8] d25 b13
  have b14 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,3,4,6,7,8] := remove (a 25) 5 [0,1,3,4,5,6,7,8] t13 b14
  have b15 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,3,4,7,8] := remove (a 25) 6 [0,1,3,4,6,7,8] t14 b15
  exact And.intro t3 (And.intro t11 (And.intro t12 (t15)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_201
