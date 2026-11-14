import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,2,4,14,15,16,17,18,19,20,21,22,23])
    (d5 : a 5 ∈ [0,6,12,17])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,2,12,14])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 21 ∈ [0,1,2,4] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 21 ≠ 14 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 14 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,2,4,15,16,17,18,19,20,21,22,23] := remove (a 21) 14 [0,1,2,4,14,15,16,17,18,19,20,21,22,23] d21 b0
  have b1 : a 21 ≠ 15 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 15 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,2,4,16,17,18,19,20,21,22,23] := remove (a 21) 15 [0,1,2,4,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 21 ≠ 16 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 16 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,2,4,17,18,19,20,21,22,23] := remove (a 21) 16 [0,1,2,4,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 21 ≠ 17 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 17 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,2,4,18,19,20,21,22,23] := remove (a 21) 17 [0,1,2,4,17,18,19,20,21,22,23] t2 b3
  have b4 : a 21 ≠ 18 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 18 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,2,4,19,20,21,22,23] := remove (a 21) 18 [0,1,2,4,18,19,20,21,22,23] t3 b4
  have b5 : a 21 ≠ 19 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 19 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,2,4,20,21,22,23] := remove (a 21) 19 [0,1,2,4,19,20,21,22,23] t4 b5
  have b6 : a 21 ≠ 20 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 20 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,2,4,21,22,23] := remove (a 21) 20 [0,1,2,4,20,21,22,23] t5 b6
  have b7 : a 21 ≠ 21 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 21 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,2,4,22,23] := remove (a 21) 21 [0,1,2,4,21,22,23] t6 b7
  have b8 : a 21 ≠ 22 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 22 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,2,4,23] := remove (a 21) 22 [0,1,2,4,22,23] t7 b8
  have b9 : a 21 ≠ 23 := exclude [0,6,12,17] (fun u v => edge r22 v u) (a 21) (a 5) 23 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,2,4] := remove (a 21) 23 [0,1,2,4,23] t8 b9
  have b10 : a 14 ≠ 1 := exclude [0,2,12,14] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b10
  have b11 : a 14 ≠ 2 := exclude [0,2,12,14] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,3] := remove (a 14) 2 [0,2,3] t10 b11
  have b12 : a 14 ≠ 3 := exclude [0,2,12,14] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 3 [0,3] t11 b12
  have b13 : a 22 ≠ 1 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d22 b13
  have b14 : a 22 ≠ 3 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 22 ≠ 4 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t9 (And.intro t12 (t15))

theorem chunk13 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,2,12,14])
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 22 ∈ [0,2,12,14,23] := by
  have b0 : a 22 ≠ 5 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d22 b0
  have b1 : a 22 ≠ 6 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 22 ≠ 7 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 22 ≠ 8 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 22 ≠ 9 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 22 ≠ 10 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 22 ≠ 11 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 22 ≠ 13 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 13 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,12,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 13 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 22 ≠ 15 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 15 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,12,14,16,17,18,19,20,21,22,23] := remove (a 22) 15 [0,2,12,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 22 ≠ 16 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,12,14,17,18,19,20,21,22,23] := remove (a 22) 16 [0,2,12,14,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 22 ≠ 17 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,12,14,18,19,20,21,22,23] := remove (a 22) 17 [0,2,12,14,17,18,19,20,21,22,23] t9 b10
  have b11 : a 22 ≠ 18 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 18 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,12,14,19,20,21,22,23] := remove (a 22) 18 [0,2,12,14,18,19,20,21,22,23] t10 b11
  have b12 : a 22 ≠ 19 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 19 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,12,14,20,21,22,23] := remove (a 22) 19 [0,2,12,14,19,20,21,22,23] t11 b12
  have b13 : a 22 ≠ 20 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 20 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,12,14,21,22,23] := remove (a 22) 20 [0,2,12,14,20,21,22,23] t12 b13
  have b14 : a 22 ≠ 21 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 21 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,12,14,22,23] := remove (a 22) 21 [0,2,12,14,21,22,23] t13 b14
  have b15 : a 22 ≠ 22 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 22 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,12,14,23] := remove (a 22) 22 [0,2,12,14,22,23] t14 b15
  exact t15

theorem chunk14 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,12,14,23])
    (d6 : a 6 ∈ [0,2,12,14])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,6,7,12,13,16,17])
    (d23 : a 23 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1,3,5,7])
    (d9 : a 9 ∈ [0,6,12])
    (d10 : a 10 ∈ [0,3,7,11])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 22 ∈ [0,2,12,14] ∧ a 15 ∈ [0,1,5,6,9,10,11] ∧ a 23 ∈ [0,1,3] ∧ a 8 ∈ [0,1,7] ∧ a 10 ∈ [0,3] ∧ a 24 ∈ [0,1,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 22 ≠ 23 := exclude [0,2,12,14] (fun u v => edge r25 v u) (a 22) (a 6) 23 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,12,14] := remove (a 22) 23 [0,2,12,14,23] d22 b0
  have b1 : a 15 ≠ 2 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b1
  have b2 : a 15 ≠ 3 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 15 ≠ 4 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 15) 4 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 15 ≠ 7 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,5,6,8,9,10,11] := remove (a 15) 7 [0,1,5,6,7,8,9,10,11] t3 b4
  have b5 : a 15 ≠ 8 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,5,6,9,10,11] := remove (a 15) 8 [0,1,5,6,8,9,10,11] t4 b5
  have b6 : a 23 ≠ 2 := exclude [0,1,6,7,12,13,16,17] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b6
  have b7 : a 8 ≠ 3 := exclude [0,6,12] (edge r28) (a 8) (a 9) 3 d9 c28 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,5,7] := remove (a 8) 3 [0,1,3,5,7] d8 b7
  have b8 : a 8 ≠ 5 := exclude [0,6,12] (edge r28) (a 8) (a 9) 5 d9 c28 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,7] := remove (a 8) 5 [0,1,5,7] t7 b8
  have b9 : a 10 ≠ 7 := exclude [0,1,7] (fun u v => edge r29 v u) (a 10) (a 8) 7 t8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,3,11] := remove (a 10) 7 [0,3,7,11] d10 b9
  have b10 : a 10 ≠ 11 := exclude [0,1,7] (fun u v => edge r29 v u) (a 10) (a 8) 11 t8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,3] := remove (a 10) 11 [0,3,11] t9 b10
  have b11 : a 24 ≠ 2 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 2 t8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b11
  have b12 : a 24 ≠ 3 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 3 t8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 24 ≠ 4 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 4 t8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 24 ≠ 6 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 6 t8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,1,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 6 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 24 ≠ 7 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 7 t8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,1,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 7 [0,1,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (t15)))))

theorem chunk15 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d8 : a 8 ∈ [0,1,7])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,6,12])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 24 ∈ [0,1,5,14,18,19] ∧ a 11 ∈ [0,2,4] := by
  have b0 : a 24 ≠ 8 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,1,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 8 [0,1,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b0
  have b1 : a 24 ≠ 9 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,1,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 9 [0,1,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 24 ≠ 10 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 10 [0,1,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 24 ≠ 11 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 11 [0,1,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 24 ≠ 12 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 12 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 12 [0,1,5,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 24 ≠ 13 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,5,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 13 [0,1,5,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 15 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,5,14,16,17,18,19,20,21,22,23] := remove (a 24) 15 [0,1,5,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 24 ≠ 16 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,5,14,17,18,19,20,21,22,23] := remove (a 24) 16 [0,1,5,14,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 24 ≠ 17 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,5,14,18,19,20,21,22,23] := remove (a 24) 17 [0,1,5,14,17,18,19,20,21,22,23] t7 b8
  have b9 : a 24 ≠ 20 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 20 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,5,14,18,19,21,22,23] := remove (a 24) 20 [0,1,5,14,18,19,20,21,22,23] t8 b9
  have b10 : a 24 ≠ 21 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 21 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,5,14,18,19,22,23] := remove (a 24) 21 [0,1,5,14,18,19,21,22,23] t9 b10
  have b11 : a 24 ≠ 22 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 22 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,5,14,18,19,23] := remove (a 24) 22 [0,1,5,14,18,19,22,23] t10 b11
  have b12 : a 24 ≠ 23 := exclude [0,1,7] (fun u v => edge r31 v u) (a 24) (a 8) 23 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,5,14,18,19] := remove (a 24) 23 [0,1,5,14,18,19,23] t11 b12
  have b13 : a 11 ≠ 1 := exclude [0,6,12] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b13
  have b14 : a 11 ≠ 3 := exclude [0,6,12] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,4,5] := remove (a 11) 3 [0,2,3,4,5] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0,6,12] (fun u v => edge r32 v u) (a 11) (a 9) 5 d9 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,4] := remove (a 11) 5 [0,2,4,5] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_216
