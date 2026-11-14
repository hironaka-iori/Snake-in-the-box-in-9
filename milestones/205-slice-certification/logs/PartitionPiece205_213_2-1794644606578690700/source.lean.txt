import PartitionData205_213
namespace PartitionCover205_213
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,5,6,7,8])
    (d4 : a 4 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,1])
    (d7 : a 7 ∈ [0,1,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 12 ∈ [0,1] ∧ a 20 ∈ [0,1,6,7,8] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0,1] ∧ a 13 ∈ [0,3,4,5,6,7,8] := by
  have b0 : a 12 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,5,6,7,8] := remove (a 12) 4 [0,1,4,5,6,7,8] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,6,7,8] := remove (a 12) 5 [0,1,5,6,7,8] t0 b1
  have b2 : a 12 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,7,8] := remove (a 12) 6 [0,1,6,7,8] t1 b2
  have b3 : a 12 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,8] := remove (a 12) 7 [0,1,7,8] t2 b3
  have b4 : a 12 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1] := remove (a 12) 8 [0,1,8] t3 b4
  have b5 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b5
  have b6 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 20 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,6,7,8,9,10,11] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11] t7 b8
  have b9 : a 20 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,6,7,8,10,11] := remove (a 20) 9 [0,1,6,7,8,9,10,11] t8 b9
  have b10 : a 20 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,6,7,8,11] := remove (a 20) 10 [0,1,6,7,8,10,11] t9 b10
  have b11 : a 20 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,6,7,8] := remove (a 20) 11 [0,1,6,7,8,11] t10 b11
  have b12 : a 5 ≠ 1 := exclude [0,1,2] (edge r20) (a 5) (a 7) 1 d7 c20 (by decide +kernel)
  have t12 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b12
  have b13 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 t12 c20 (by decide +kernel)
  have t13 : a 7 ∈ [0,1] := remove (a 7) 2 [0,1,2] d7 b13
  have b14 : a 13 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 1 t12 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,2,3,4,5,6,7,8] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8] d13 b14
  have b15 : a 13 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 2 t12 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,3,4,5,6,7,8] := remove (a 13) 2 [0,2,3,4,5,6,7,8] t14 b15
  exact And.intro t4 (And.intro t11 (And.intro t12 (And.intro t13 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 13 ∈ [0] ∧ a 21 ∈ [0,4] ∧ a 7 ∈ [0] ∧ a 22 ∈ [0,1,2,8,9,10,11] := by
  have b0 : a 13 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,4,5,6,7,8] := remove (a 13) 3 [0,3,4,5,6,7,8] d13 b0
  have b1 : a 13 ≠ 4 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,5,6,7,8] := remove (a 13) 4 [0,4,5,6,7,8] t0 b1
  have b2 : a 13 ≠ 5 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,6,7,8] := remove (a 13) 5 [0,5,6,7,8] t1 b2
  have b3 : a 13 ≠ 6 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,7,8] := remove (a 13) 6 [0,6,7,8] t2 b3
  have b4 : a 13 ≠ 7 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,8] := remove (a 13) 7 [0,7,8] t3 b4
  have b5 : a 13 ≠ 8 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 8 [0,8] t4 b5
  have b6 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b6
  have b7 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t6 b7
  have b8 : a 21 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,4,5] := remove (a 21) 3 [0,3,4,5] t7 b8
  have b9 : a 21 ≠ 5 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,4] := remove (a 21) 5 [0,4,5] t8 b9
  have b10 : a 7 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t10 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b10
  have b11 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b11
  have b12 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 22) 4 [0,1,2,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 22) 5 [0,1,2,5,6,7,8,9,10,11] t12 b13
  have b14 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2,7,8,9,10,11] := remove (a 22) 6 [0,1,2,6,7,8,9,10,11] t13 b14
  have b15 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,2,8,9,10,11] := remove (a 22) 7 [0,1,2,7,8,9,10,11] t14 b15
  exact And.intro t5 (And.intro t9 (And.intro t10 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,8,9,10,11])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0])
    (d23 : a 23 ∈ [0,1,2])
    (d8 : a 8 ∈ [0,1,4,5])
    (d9 : a 9 ∈ [0,6])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 22 ∈ [0,1,2,9,10,11] ∧ a 15 ∈ [0,1] ∧ a 23 ∈ [0,1] ∧ a 8 ∈ [0] ∧ a 24 ∈ [0,4,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,2,9,10,11] := remove (a 22) 8 [0,1,2,8,9,10,11] d22 b0
  have b1 : a 15 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b1
  have b2 : a 15 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] t1 b2
  have b3 : a 15 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,5] := remove (a 15) 4 [0,1,4,5] t2 b3
  have b4 : a 15 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1] := remove (a 15) 5 [0,1,5] t3 b4
  have b5 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1] := remove (a 23) 2 [0,1,2] d23 b5
  have b6 : a 8 ≠ 1 := exclude [0,6] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t6 : a 8 ∈ [0,4,5] := remove (a 8) 1 [0,1,4,5] d8 b6
  have b7 : a 8 ≠ 5 := exclude [0,6] (edge r28) (a 8) (a 9) 5 d9 c28 (by decide +kernel)
  have t7 : a 8 ∈ [0,4] := remove (a 8) 5 [0,4,5] t6 b7
  have b8 : a 8 ≠ 4 := exclude [0,1] (edge r30) (a 8) (a 12) 4 d12 c30 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 4 [0,4] t7 b8
  have b9 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b9
  have b10 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 t8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 t8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 t8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 t8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t8 (t15))))

theorem chunk11 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,4,9,10,11,12,13,14,15,16,17])
    (d8 : a 8 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,6])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,4] ∧ a 25 ∈ [0,2,7,10,11,12,13,14,15,16,17] := by
  have b0 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,4,9,10,11,12,13,14,15,16,17] d24 b0
  have b1 : a 24 ≠ 10 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,4,11,12,13,14,15,16,17] := remove (a 24) 10 [0,4,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 24 ≠ 11 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,4,12,13,14,15,16,17] := remove (a 24) 11 [0,4,11,12,13,14,15,16,17] t1 b2
  have b3 : a 24 ≠ 12 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 12 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,4,13,14,15,16,17] := remove (a 24) 12 [0,4,12,13,14,15,16,17] t2 b3
  have b4 : a 24 ≠ 13 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,4,14,15,16,17] := remove (a 24) 13 [0,4,13,14,15,16,17] t3 b4
  have b5 : a 24 ≠ 14 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,4,15,16,17] := remove (a 24) 14 [0,4,14,15,16,17] t4 b5
  have b6 : a 24 ≠ 15 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,4,16,17] := remove (a 24) 15 [0,4,15,16,17] t5 b6
  have b7 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,4,17] := remove (a 24) 16 [0,4,16,17] t6 b7
  have b8 : a 24 ≠ 17 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4] := remove (a 24) 17 [0,4,17] t7 b8
  have b9 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b9
  have b10 : a 25 ≠ 3 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 25 ≠ 5 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 25 ≠ 6 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 25 ≠ 8 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,7,9,10,11,12,13,14,15,16,17] := remove (a 25) 8 [0,2,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 25 ≠ 9 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,7,10,11,12,13,14,15,16,17] := remove (a 25) 9 [0,2,7,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t8 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_213
