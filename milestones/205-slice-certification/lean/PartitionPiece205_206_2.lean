import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,3,4,5,11,12,14,20,21,22,23])
    (d5 : a 5 ∈ [0,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,1,4])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 13 ∈ [0,1,3,4,5,11,12,14] ∧ a 21 ∈ [0,2] ∧ a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,20,21,22,23] := by
  have b0 : a 13 ≠ 20 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 20 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,3,4,5,11,12,14,21,22,23] := remove (a 13) 20 [0,1,3,4,5,11,12,14,20,21,22,23] d13 b0
  have b1 : a 13 ≠ 21 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 21 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,3,4,5,11,12,14,22,23] := remove (a 13) 21 [0,1,3,4,5,11,12,14,21,22,23] t0 b1
  have b2 : a 13 ≠ 22 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 22 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,3,4,5,11,12,14,23] := remove (a 13) 22 [0,1,3,4,5,11,12,14,22,23] t1 b2
  have b3 : a 13 ≠ 23 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 23 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,3,4,5,11,12,14] := remove (a 13) 23 [0,1,3,4,5,11,12,14,23] t2 b3
  have b4 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b4
  have b5 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,2,4,5] := remove (a 21) 3 [0,2,3,4,5] t4 b5
  have b6 : a 21 ≠ 4 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,2,5] := remove (a 21) 4 [0,2,4,5] t5 b6
  have b7 : a 21 ≠ 5 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,2] := remove (a 21) 5 [0,2,5] t6 b7
  have b8 : a 14 ≠ 8 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 8 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b8
  have b9 : a 14 ≠ 9 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 9 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 14 ≠ 10 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 10 [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 14 ≠ 11 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 11 [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 14 ≠ 16 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,17,18,19,20,21,22,23] := remove (a 14) 16 [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 14 ≠ 17 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,18,19,20,21,22,23] := remove (a 14) 17 [0,1,2,3,4,5,6,7,12,13,14,15,17,18,19,20,21,22,23] t12 b13
  have b14 : a 14 ≠ 18 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 18 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,19,20,21,22,23] := remove (a 14) 18 [0,1,2,3,4,5,6,7,12,13,14,15,18,19,20,21,22,23] t13 b14
  have b15 : a 14 ≠ 19 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 19 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,20,21,22,23] := remove (a 14) 19 [0,1,2,3,4,5,6,7,12,13,14,15,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t7 (t15))

theorem chunk9 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,20,21,22,23])
    (d6 : a 6 ∈ [0,1,4])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,2])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15] ∧ a 22 ∈ [0,1,4,5,6,7,10,11] ∧ a 15 ∈ [0,1,4,5,6,7,8,9,10,11] := by
  have b0 : a 14 ≠ 20 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 20 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,21,22,23] := remove (a 14) 20 [0,1,2,3,4,5,6,7,12,13,14,15,20,21,22,23] d14 b0
  have b1 : a 14 ≠ 21 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 21 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,22,23] := remove (a 14) 21 [0,1,2,3,4,5,6,7,12,13,14,15,21,22,23] t0 b1
  have b2 : a 14 ≠ 22 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 22 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,23] := remove (a 14) 22 [0,1,2,3,4,5,6,7,12,13,14,15,22,23] t1 b2
  have b3 : a 14 ≠ 23 := exclude [0,1,4] (fun u v => edge r24 v u) (a 14) (a 6) 23 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15] := remove (a 14) 23 [0,1,2,3,4,5,6,7,12,13,14,15,23] t2 b3
  have b4 : a 22 ≠ 2 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d22 b4
  have b5 : a 22 ≠ 3 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 22 ≠ 8 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] := remove (a 22) 8 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 22 ≠ 9 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,4,5,6,7,10,11,12,13,14,15,16,17] := remove (a 22) 9 [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 22 ≠ 12 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 12 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,4,5,6,7,10,11,13,14,15,16,17] := remove (a 22) 12 [0,1,4,5,6,7,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 22 ≠ 13 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 13 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,4,5,6,7,10,11,14,15,16,17] := remove (a 22) 13 [0,1,4,5,6,7,10,11,13,14,15,16,17] t8 b9
  have b10 : a 22 ≠ 14 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 14 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,4,5,6,7,10,11,15,16,17] := remove (a 22) 14 [0,1,4,5,6,7,10,11,14,15,16,17] t9 b10
  have b11 : a 22 ≠ 15 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 15 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,4,5,6,7,10,11,16,17] := remove (a 22) 15 [0,1,4,5,6,7,10,11,15,16,17] t10 b11
  have b12 : a 22 ≠ 16 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,4,5,6,7,10,11,17] := remove (a 22) 16 [0,1,4,5,6,7,10,11,16,17] t11 b12
  have b13 : a 22 ≠ 17 := exclude [0,1,4] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,4,5,6,7,10,11] := remove (a 22) 17 [0,1,4,5,6,7,10,11,17] t12 b13
  have b14 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b14
  have b15 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t13 (t15))

theorem chunk10 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,4,5,6,10,11])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 15 ∈ [0,1,4,5] ∧ a 23 ∈ [0,1,4,5] ∧ a 9 ∈ [0,1,2,3] := by
  have b0 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 15) 6 [0,1,4,5,6,7,8,9,10,11] d15 b0
  have b1 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,4,5,8,9,10,11] := remove (a 15) 7 [0,1,4,5,7,8,9,10,11] t0 b1
  have b2 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4,5,9,10,11] := remove (a 15) 8 [0,1,4,5,8,9,10,11] t1 b2
  have b3 : a 15 ≠ 9 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,4,5,10,11] := remove (a 15) 9 [0,1,4,5,9,10,11] t2 b3
  have b4 : a 15 ≠ 10 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,4,5,11] := remove (a 15) 10 [0,1,4,5,10,11] t3 b4
  have b5 : a 15 ≠ 11 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 11 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,4,5] := remove (a 15) 11 [0,1,4,5,11] t4 b5
  have b6 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 23) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 6 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 23) 6 [0,1,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 7 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,4,5,8,9,10,11] := remove (a 23) 7 [0,1,4,5,7,8,9,10,11] t8 b9
  have b10 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,4,5,9,10,11] := remove (a 23) 8 [0,1,4,5,8,9,10,11] t9 b10
  have b11 : a 23 ≠ 9 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,4,5,10,11] := remove (a 23) 9 [0,1,4,5,9,10,11] t10 b11
  have b12 : a 23 ≠ 10 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,4,5,11] := remove (a 23) 10 [0,1,4,5,10,11] t11 b12
  have b13 : a 23 ≠ 11 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,4,5] := remove (a 23) 11 [0,1,4,5,11] t12 b13
  have b14 : a 9 ≠ 4 := exclude [0,4,5,6,10,11] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,2,3,5] := remove (a 9) 4 [0,1,2,3,4,5] d9 b14
  have b15 : a 9 ≠ 5 := exclude [0,4,5,6,10,11] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,2,3] := remove (a 9) 5 [0,1,2,3,5] t14 b15
  exact And.intro t5 (And.intro t13 (t15))

theorem chunk11 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,4,5,6,10,11])
    (d10 : a 10 ∈ [0,1,4,5])
    (d12 : a 12 ∈ [0,1,12,13])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 8 ∈ [0,4,6,10] ∧ a 10 ∈ [0,4] ∧ a 12 ∈ [0,12] ∧ a 24 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 8 ≠ 5 := exclude [0,1,4,5] (edge r29) (a 8) (a 10) 5 d10 c29 (by decide +kernel)
  have t0 : a 8 ∈ [0,4,6,10,11] := remove (a 8) 5 [0,4,5,6,10,11] d8 b0
  have b1 : a 8 ≠ 11 := exclude [0,1,4,5] (edge r29) (a 8) (a 10) 11 d10 c29 (by decide +kernel)
  have t1 : a 8 ∈ [0,4,6,10] := remove (a 8) 11 [0,4,6,10,11] t0 b1
  have b2 : a 10 ≠ 1 := exclude [0,4,6,10] (fun u v => edge r29 v u) (a 10) (a 8) 1 t1 c29 (by decide +kernel)
  have t2 : a 10 ∈ [0,4,5] := remove (a 10) 1 [0,1,4,5] d10 b2
  have b3 : a 10 ≠ 5 := exclude [0,4,6,10] (fun u v => edge r29 v u) (a 10) (a 8) 5 t1 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,4] := remove (a 10) 5 [0,4,5] t2 b3
  have b4 : a 12 ≠ 1 := exclude [0,4,6,10] (fun u v => edge r30 v u) (a 12) (a 8) 1 t1 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,12,13] := remove (a 12) 1 [0,1,12,13] d12 b4
  have b5 : a 12 ≠ 13 := exclude [0,4,6,10] (fun u v => edge r30 v u) (a 12) (a 8) 13 t1 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,12] := remove (a 12) 13 [0,12,13] t4 b5
  have b6 : a 24 ≠ 1 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 1 t1 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b6
  have b7 : a 24 ≠ 2 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 2 t1 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 24 ≠ 3 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 3 t1 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 24 ≠ 4 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 4 t1 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 24 ≠ 5 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 5 t1 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 24 ≠ 6 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 6 t1 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 24 ≠ 7 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 7 t1 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 24 ≠ 8 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 8 t1 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 24 ≠ 9 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 9 t1 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 24 ≠ 10 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 10 t1 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (t15)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_206
