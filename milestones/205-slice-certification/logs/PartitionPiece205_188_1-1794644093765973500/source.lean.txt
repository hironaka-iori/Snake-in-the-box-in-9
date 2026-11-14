import PartitionData205_188
namespace PartitionCover205_188
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,5,9,10,11])
    (d3 : a 3 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    : a 19 ∈ [0,5,9] ∧ a 12 ∈ [0,2,4,6,7,8,9,10,11] ∧ a 7 ∈ [0,3] ∧ a 21 ∈ [0,2,3,5] ∧ a 6 ∈ [0,2,3,5] := by
  have b0 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,5,9,11] := remove (a 19) 10 [0,5,9,10,11] d19 b0
  have b1 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 11 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,5,9] := remove (a 19) 11 [0,5,9,11] t0 b1
  have b2 : a 12 ≠ 1 := exclude [0,1,2] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b2
  have b3 : a 12 ≠ 3 := exclude [0,1,2] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 12) 3 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 12 ≠ 5 := exclude [0,1,2] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,2,4,6,7,8,9,10,11] := remove (a 12) 5 [0,2,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 7 ≠ 1 := exclude [0,1,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t5 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b5
  have b6 : a 7 ≠ 4 := exclude [0,1,2] (fun u v => edge r20 v u) (a 7) (a 5) 4 d5 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0,2,3,5] := remove (a 7) 4 [0,2,3,4,5] t5 b6
  have b7 : a 21 ≠ 1 := exclude [0,1,2] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,2,3,4,5,6,7,8] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8] d21 b7
  have b8 : a 21 ≠ 4 := exclude [0,1,2] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,2,3,5,6,7,8] := remove (a 21) 4 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 21 ≠ 6 := exclude [0,1,2] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,3,5,7,8] := remove (a 21) 6 [0,2,3,5,6,7,8] t8 b9
  have b10 : a 21 ≠ 7 := exclude [0,1,2] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,2,3,5,8] := remove (a 21) 7 [0,2,3,5,7,8] t9 b10
  have b11 : a 21 ≠ 8 := exclude [0,1,2] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,3,5] := remove (a 21) 8 [0,2,3,5,8] t10 b11
  have b12 : a 6 ≠ 1 := exclude [0,2,3,5] (edge r23) (a 6) (a 7) 1 t6 c23 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b12
  have b13 : a 6 ≠ 4 := exclude [0,2,3,5] (edge r23) (a 6) (a 7) 4 t6 c23 (by decide +kernel)
  have t13 : a 6 ∈ [0,2,3,5] := remove (a 6) 4 [0,2,3,4,5] t12 b13
  have b14 : a 7 ≠ 2 := exclude [0,2,3,5] (fun u v => edge r23 v u) (a 7) (a 6) 2 t13 c23 (by decide +kernel)
  have t14 : a 7 ∈ [0,3,5] := remove (a 7) 2 [0,2,3,5] t6 b14
  have b15 : a 7 ≠ 5 := exclude [0,2,3,5] (fun u v => edge r23 v u) (a 7) (a 6) 5 t13 c23 (by decide +kernel)
  have t15 : a 7 ∈ [0,3] := remove (a 7) 5 [0,3,5] t14 b15
  exact And.intro t1 (And.intro t4 (And.intro t15 (And.intro t11 (t13))))

theorem chunk5 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0,2,3,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 14 ∈ [0,1,4,5,6,7,10,11] ∧ a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 14 ≠ 2 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b0
  have b1 : a 14 ≠ 3 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 14 ≠ 8 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 9 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,4,5,6,7,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 12 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 12 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,4,5,6,7,10,11,13,14,15,16,17] := remove (a 14) 12 [0,1,4,5,6,7,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 13 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,4,5,6,7,10,11,14,15,16,17] := remove (a 14) 13 [0,1,4,5,6,7,10,11,13,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 14 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,4,5,6,7,10,11,15,16,17] := remove (a 14) 14 [0,1,4,5,6,7,10,11,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 15 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,4,5,6,7,10,11,16,17] := remove (a 14) 15 [0,1,4,5,6,7,10,11,15,16,17] t6 b7
  have b8 : a 14 ≠ 16 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,4,5,6,7,10,11,17] := remove (a 14) 16 [0,1,4,5,6,7,10,11,16,17] t7 b8
  have b9 : a 14 ≠ 17 := exclude [0,2,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,4,5,6,7,10,11] := remove (a 14) 17 [0,1,4,5,6,7,10,11,17] t8 b9
  have b10 : a 22 ≠ 12 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 12 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] := remove (a 22) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d22 b10
  have b11 : a 22 ≠ 13 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 13 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] := remove (a 22) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] t10 b11
  have b12 : a 22 ≠ 14 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 14 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] := remove (a 22) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] t11 b12
  have b13 : a 22 ≠ 15 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 15 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := remove (a 22) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] t12 b13
  have b14 : a 22 ≠ 16 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17] := remove (a 22) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17] t13 b14
  have b15 : a 22 ≠ 17 := exclude [0,2,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 22) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17] t14 b15
  exact And.intro t9 (t15)

theorem chunk6 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d9 : a 9 ∈ [0,2,6,8])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,2,4,6,7,8,9,10,11])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 15 ∈ [0,1,2,3,4,5] ∧ a 23 ∈ [0,1,2] ∧ a 9 ∈ [0,2] ∧ a 12 ∈ [0,4,7,8,9,10,11] := by
  have b0 : a 15 ≠ 6 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,2,3,4,5,7,8] := remove (a 15) 6 [0,1,2,3,4,5,6,7,8] d15 b0
  have b1 : a 15 ≠ 7 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,3,4,5,8] := remove (a 15) 7 [0,1,2,3,4,5,7,8] t0 b1
  have b2 : a 15 ≠ 8 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,3,4,5] := remove (a 15) 8 [0,1,2,3,4,5,8] t1 b2
  have b3 : a 23 ≠ 3 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b3
  have b4 : a 23 ≠ 4 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 23) 4 [0,1,2,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 23 ≠ 5 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 23) 5 [0,1,2,5,6,7,8,9,10,11] t4 b5
  have b6 : a 23 ≠ 6 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,7,8,9,10,11] := remove (a 23) 6 [0,1,2,6,7,8,9,10,11] t5 b6
  have b7 : a 23 ≠ 7 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,8,9,10,11] := remove (a 23) 7 [0,1,2,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 8 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,9,10,11] := remove (a 23) 8 [0,1,2,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 9 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,10,11] := remove (a 23) 9 [0,1,2,9,10,11] t8 b9
  have b10 : a 23 ≠ 10 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,11] := remove (a 23) 10 [0,1,2,10,11] t9 b10
  have b11 : a 23 ≠ 11 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2] := remove (a 23) 11 [0,1,2,11] t10 b11
  have b12 : a 9 ≠ 6 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,8] := remove (a 9) 6 [0,2,6,8] d9 b12
  have b13 : a 9 ≠ 8 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 8 d8 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,2] := remove (a 9) 8 [0,2,8] t12 b13
  have b14 : a 12 ≠ 2 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 2 d8 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,4,6,7,8,9,10,11] := remove (a 12) 2 [0,2,4,6,7,8,9,10,11] d12 b14
  have b15 : a 12 ≠ 6 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 6 d8 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,4,7,8,9,10,11] := remove (a 12) 6 [0,4,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t11 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,4,7,8,9,10,11])
    (d8 : a 8 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,2])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 12 ∈ [0,4] ∧ a 24 ∈ [0,2,4,8] ∧ a 13 ∈ [0,1,5] := by
  have b0 : a 12 ≠ 7 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,4,8,9,10,11] := remove (a 12) 7 [0,4,7,8,9,10,11] d12 b0
  have b1 : a 12 ≠ 8 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 8 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,4,9,10,11] := remove (a 12) 8 [0,4,8,9,10,11] t0 b1
  have b2 : a 12 ≠ 9 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 9 d8 c30 (by decide +kernel)
  have t2 : a 12 ∈ [0,4,10,11] := remove (a 12) 9 [0,4,9,10,11] t1 b2
  have b3 : a 12 ≠ 10 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 10 d8 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0,4,11] := remove (a 12) 10 [0,4,10,11] t2 b3
  have b4 : a 12 ≠ 11 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 11 d8 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,4] := remove (a 12) 11 [0,4,11] t3 b4
  have b5 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b5
  have b6 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,2,4,6,7,8,9,10,11] := remove (a 24) 5 [0,2,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 6 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,4,7,8,9,10,11] := remove (a 24) 6 [0,2,4,6,7,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 7 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,4,8,9,10,11] := remove (a 24) 7 [0,2,4,7,8,9,10,11] t8 b9
  have b10 : a 24 ≠ 9 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,2,4,8,10,11] := remove (a 24) 9 [0,2,4,8,9,10,11] t9 b10
  have b11 : a 24 ≠ 10 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,4,8,11] := remove (a 24) 10 [0,2,4,8,10,11] t10 b11
  have b12 : a 24 ≠ 11 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,4,8] := remove (a 24) 11 [0,2,4,8,11] t11 b12
  have b13 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b13
  have b14 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t13 b14
  have b15 : a 13 ≠ 4 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] t14 b15
  exact And.intro t4 (And.intro t12 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_188
