import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,3,4,5,6,7])
    (d5 : a 5 ∈ [0,4,20,22])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 13 ∈ [0,1,3,4,5,7] ∧ a 21 ∈ [0,1,6,7,18,19,21,22,23] := by
  have b0 : a 13 ≠ 6 := exclude [0,4,20,22] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,3,4,5,7] := remove (a 13) 6 [0,1,3,4,5,6,7] d13 b0
  have b1 : a 21 ≠ 2 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d21 b1
  have b2 : a 21 ≠ 3 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 21 ≠ 4 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 21 ≠ 5 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 21 ≠ 8 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 21 ≠ 9 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 9 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 21 ≠ 10 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 10 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 10 [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 21 ≠ 11 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 11 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 11 [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 21 ≠ 12 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 12 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 12 [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 21 ≠ 13 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 13 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,6,7,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 13 [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 21 ≠ 14 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 14 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,6,7,15,16,17,18,19,20,21,22,23] := remove (a 21) 14 [0,1,6,7,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 21 ≠ 15 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 15 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,6,7,16,17,18,19,20,21,22,23] := remove (a 21) 15 [0,1,6,7,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 21 ≠ 16 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 16 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,6,7,17,18,19,20,21,22,23] := remove (a 21) 16 [0,1,6,7,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 21 ≠ 17 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 17 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,6,7,18,19,20,21,22,23] := remove (a 21) 17 [0,1,6,7,17,18,19,20,21,22,23] t13 b14
  have b15 : a 21 ≠ 20 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 20 d5 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,1,6,7,18,19,21,22,23] := remove (a 21) 20 [0,1,6,7,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

theorem chunk9 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,6,7,18,19,21,22,23])
    (d5 : a 5 ∈ [0,4,20,22])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,8])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 21 ∈ [0,1,6,7,18,19] ∧ a 7 ∈ [0,3] ∧ a 14 ∈ [0,2,11] := by
  have b0 : a 21 ≠ 21 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 21 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,6,7,18,19,22,23] := remove (a 21) 21 [0,1,6,7,18,19,21,22,23] d21 b0
  have b1 : a 21 ≠ 22 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 22 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,6,7,18,19,23] := remove (a 21) 22 [0,1,6,7,18,19,22,23] t0 b1
  have b2 : a 21 ≠ 23 := exclude [0,4,20,22] (fun u v => edge r22 v u) (a 21) (a 5) 23 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,6,7,18,19] := remove (a 21) 23 [0,1,6,7,18,19,23] t1 b2
  have b3 : a 7 ≠ 1 := exclude [0,8] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t3 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b3
  have b4 : a 7 ≠ 2 := exclude [0,8] (fun u v => edge r23 v u) (a 7) (a 6) 2 d6 c23 (by decide +kernel)
  have t4 : a 7 ∈ [0,3,4,5] := remove (a 7) 2 [0,2,3,4,5] t3 b4
  have b5 : a 7 ≠ 4 := exclude [0,8] (fun u v => edge r23 v u) (a 7) (a 6) 4 d6 c23 (by decide +kernel)
  have t5 : a 7 ∈ [0,3,5] := remove (a 7) 4 [0,3,4,5] t4 b5
  have b6 : a 7 ≠ 5 := exclude [0,8] (fun u v => edge r23 v u) (a 7) (a 6) 5 d6 c23 (by decide +kernel)
  have t6 : a 7 ∈ [0,3] := remove (a 7) 5 [0,3,5] t5 b6
  have b7 : a 14 ≠ 1 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b7
  have b8 : a 14 ≠ 3 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 14 ≠ 4 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 14 ≠ 5 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,6,7,8,9,10,11] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11] t9 b10
  have b11 : a 14 ≠ 6 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,7,8,9,10,11] := remove (a 14) 6 [0,2,6,7,8,9,10,11] t10 b11
  have b12 : a 14 ≠ 7 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,8,9,10,11] := remove (a 14) 7 [0,2,7,8,9,10,11] t11 b12
  have b13 : a 14 ≠ 8 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,9,10,11] := remove (a 14) 8 [0,2,8,9,10,11] t12 b13
  have b14 : a 14 ≠ 9 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,10,11] := remove (a 14) 9 [0,2,9,10,11] t13 b14
  have b15 : a 14 ≠ 10 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,11] := remove (a 14) 10 [0,2,10,11] t14 b15
  exact And.intro t2 (And.intro t6 (t15))

theorem chunk10 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,11])
    (d6 : a 6 ∈ [0,8])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d7 : a 7 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 14 ∈ [0,2] ∧ a 22 ∈ [0,11] ∧ a 15 ∈ [0,1,2,3,7,8] ∧ a 23 ∈ [0,1,2,3,4,6,7,8,9,10,11] := by
  have b0 : a 14 ≠ 11 := exclude [0,8] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,2] := remove (a 14) 11 [0,2,11] d14 b0
  have b1 : a 22 ≠ 1 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b1
  have b2 : a 22 ≠ 2 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 22 ≠ 3 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 22 ≠ 4 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,5,6,7,8,9,10,11] := remove (a 22) 4 [0,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 22 ≠ 5 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,6,7,8,9,10,11] := remove (a 22) 5 [0,5,6,7,8,9,10,11] t4 b5
  have b6 : a 22 ≠ 6 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,7,8,9,10,11] := remove (a 22) 6 [0,6,7,8,9,10,11] t5 b6
  have b7 : a 22 ≠ 7 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,8,9,10,11] := remove (a 22) 7 [0,7,8,9,10,11] t6 b7
  have b8 : a 22 ≠ 8 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,9,10,11] := remove (a 22) 8 [0,8,9,10,11] t7 b8
  have b9 : a 22 ≠ 9 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,10,11] := remove (a 22) 9 [0,9,10,11] t8 b9
  have b10 : a 22 ≠ 10 := exclude [0,8] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,11] := remove (a 22) 10 [0,10,11] t9 b10
  have b11 : a 15 ≠ 4 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,2,3,5,6,7,8,9] := remove (a 15) 4 [0,1,2,3,4,5,6,7,8,9] d15 b11
  have b12 : a 15 ≠ 5 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,2,3,6,7,8,9] := remove (a 15) 5 [0,1,2,3,5,6,7,8,9] t11 b12
  have b13 : a 15 ≠ 6 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,2,3,7,8,9] := remove (a 15) 6 [0,1,2,3,6,7,8,9] t12 b13
  have b14 : a 15 ≠ 9 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,2,3,7,8] := remove (a 15) 9 [0,1,2,3,7,8,9] t13 b14
  have b15 : a 23 ≠ 5 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,2,3,4,6,7,8,9,10,11] := remove (a 23) 5 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b15
  exact And.intro t0 (And.intro t10 (And.intro t14 (t15)))

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,3])
    (d10 : a 10 ∈ [0,2,3,5])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,3,4,5,7])
    (d9 : a 9 ∈ [0,2])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 23 ∈ [0,1,2,3,4,7,9,10,11] ∧ a 10 ∈ [0,2] ∧ a 24 ∈ [0,6,8,9] ∧ a 13 ∈ [0,4] := by
  have b0 : a 23 ≠ 6 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,4,7,8,9,10,11] := remove (a 23) 6 [0,1,2,3,4,6,7,8,9,10,11] d23 b0
  have b1 : a 23 ≠ 8 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,4,7,9,10,11] := remove (a 23) 8 [0,1,2,3,4,7,8,9,10,11] t0 b1
  have b2 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,5] := remove (a 10) 3 [0,2,3,5] d10 b2
  have b3 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,2] := remove (a 10) 5 [0,2,5] t2 b3
  have b4 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b4
  have b5 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,6,8,9,10,11] := remove (a 24) 7 [0,6,7,8,9,10,11] t8 b9
  have b10 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,6,8,9,11] := remove (a 24) 10 [0,6,8,9,10,11] t9 b10
  have b11 : a 24 ≠ 11 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,6,8,9] := remove (a 24) 11 [0,6,8,9,11] t10 b11
  have b12 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,3,4,5,7] := remove (a 13) 1 [0,1,3,4,5,7] d13 b12
  have b13 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,4,5,7] := remove (a 13) 3 [0,3,4,5,7] t12 b13
  have b14 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0,4,7] := remove (a 13) 5 [0,4,5,7] t13 b14
  have b15 : a 13 ≠ 7 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 7 d9 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0,4] := remove (a 13) 7 [0,4,7] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t11 (t15)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_187
