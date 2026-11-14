import PartitionData205_186
namespace PartitionCover205_186
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,4,5,11])
    (d4 : a 4 ∈ [0])
    (d5 : a 5 ∈ [0,1,4,5])
    (d7 : a 7 ∈ [0,4,6])
    (d13 : a 13 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (d6 : a 6 ∈ [0,19])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 20 ∈ [0,4,5] ∧ a 5 ∈ [0,4] ∧ a 7 ∈ [0,6] ∧ a 13 ∈ [0,1,3] ∧ a 21 ∈ [0,1,2,3,4,6,7] ∧ a 6 ∈ [0] ∧ a 14 ∈ [0,10,11] := by
  have b0 : a 20 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,4,5] := remove (a 20) 11 [0,4,5,11] d20 b0
  have b1 : a 5 ≠ 1 := exclude [0,4,6] (edge r20) (a 5) (a 7) 1 d7 c20 (by decide +kernel)
  have t1 : a 5 ∈ [0,4,5] := remove (a 5) 1 [0,1,4,5] d5 b1
  have b2 : a 5 ≠ 5 := exclude [0,4,6] (edge r20) (a 5) (a 7) 5 d7 c20 (by decide +kernel)
  have t2 : a 5 ∈ [0,4] := remove (a 5) 5 [0,4,5] t1 b2
  have b3 : a 7 ≠ 4 := exclude [0,4] (fun u v => edge r20 v u) (a 7) (a 5) 4 t2 c20 (by decide +kernel)
  have t3 : a 7 ∈ [0,6] := remove (a 7) 4 [0,4,6] d7 b3
  have b4 : a 13 ≠ 2 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 2 t2 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3] := remove (a 13) 2 [0,1,2,3] d13 b4
  have b5 : a 21 ≠ 5 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 5 t2 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,2,3,4,6,7] := remove (a 21) 5 [0,1,2,3,4,5,6,7] d21 b5
  have b6 : a 6 ≠ 19 := exclude [0,6] (edge r23) (a 6) (a 7) 19 t3 c23 (by decide +kernel)
  have t6 : a 6 ∈ [0] := remove (a 6) 19 [0,19] d6 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b7
  have b8 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 t6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 14 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 4 t6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,5,6,7,8,9,10,11] := remove (a 14) 4 [0,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 14 ≠ 5 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 5 t6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,6,7,8,9,10,11] := remove (a 14) 5 [0,5,6,7,8,9,10,11] t10 b11
  have b12 : a 14 ≠ 6 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 6 t6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,7,8,9,10,11] := remove (a 14) 6 [0,6,7,8,9,10,11] t11 b12
  have b13 : a 14 ≠ 7 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 7 t6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,8,9,10,11] := remove (a 14) 7 [0,7,8,9,10,11] t12 b13
  have b14 : a 14 ≠ 8 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 8 t6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,9,10,11] := remove (a 14) 8 [0,8,9,10,11] t13 b14
  have b15 : a 14 ≠ 9 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 9 t6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,10,11] := remove (a 14) 9 [0,9,10,11] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t15))))))

theorem chunk9 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,10,11])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,6])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 14 ∈ [0] ∧ a 22 ∈ [0,4] ∧ a 15 ∈ [0,1,5,7,8] := by
  have b0 : a 14 ≠ 10 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,11] := remove (a 14) 10 [0,10,11] d14 b0
  have b1 : a 14 ≠ 11 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0] := remove (a 14) 11 [0,11] t0 b1
  have b2 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b2
  have b3 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,4,6,7,8,9,10,11] := remove (a 22) 5 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,4,7,8,9,10,11] := remove (a 22) 6 [0,4,6,7,8,9,10,11] t5 b6
  have b7 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,4,8,9,10,11] := remove (a 22) 7 [0,4,7,8,9,10,11] t6 b7
  have b8 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,4,9,10,11] := remove (a 22) 8 [0,4,8,9,10,11] t7 b8
  have b9 : a 22 ≠ 9 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,4,10,11] := remove (a 22) 9 [0,4,9,10,11] t8 b9
  have b10 : a 22 ≠ 10 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,4,11] := remove (a 22) 10 [0,4,10,11] t9 b10
  have b11 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,4] := remove (a 22) 11 [0,4,11] t10 b11
  have b12 : a 15 ≠ 2 := exclude [0,6] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,3,4,5,6,7,8] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8] d15 b12
  have b13 : a 15 ≠ 3 := exclude [0,6] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,4,5,6,7,8] := remove (a 15) 3 [0,1,3,4,5,6,7,8] t12 b13
  have b14 : a 15 ≠ 4 := exclude [0,6] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,5,6,7,8] := remove (a 15) 4 [0,1,4,5,6,7,8] t13 b14
  have b15 : a 15 ≠ 6 := exclude [0,6] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,5,7,8] := remove (a 15) 6 [0,1,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t11 (t15))

theorem chunk10 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,5,7,8])
    (d7 : a 7 ∈ [0,6])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 15 ∈ [0,1,5,7] ∧ a 23 ∈ [0,1,2,3,4,5,21,22,23] := by
  have b0 : a 15 ≠ 8 := exclude [0,6] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,5,7] := remove (a 15) 8 [0,1,5,7,8] d15 b0
  have b1 : a 23 ≠ 6 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d23 b1
  have b2 : a 23 ≠ 7 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 23 ≠ 8 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 23 ≠ 9 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 23 ≠ 10 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 23 ≠ 11 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 23 ≠ 12 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 12 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 23 ≠ 13 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 13 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 23 ≠ 14 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 14 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 23) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 23 ≠ 15 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 15 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 23) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 23 ≠ 16 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 16 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 23) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 23 ≠ 17 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 17 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 23) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t11 b12
  have b13 : a 23 ≠ 18 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 18 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 23) 18 [0,1,2,3,4,5,18,19,20,21,22,23] t12 b13
  have b14 : a 23 ≠ 19 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 19 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 23) 19 [0,1,2,3,4,5,19,20,21,22,23] t13 b14
  have b15 : a 23 ≠ 20 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 20 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 23) 20 [0,1,2,3,4,5,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,21,22,23])
    (d7 : a 7 ∈ [0,6])
    (d10 : a 10 ∈ [0,3,6,11,12,14,15,18,21,23])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,1,6,9])
    (d9 : a 9 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,3])
    (d25 : a 25 ∈ [0,1,2,3])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 23 ∈ [0,1,2,3,4,5] ∧ a 10 ∈ [0,12] ∧ a 11 ∈ [0,1,9] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0,3] := by
  have b0 : a 23 ≠ 21 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 21 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,4,5,22,23] := remove (a 23) 21 [0,1,2,3,4,5,21,22,23] d23 b0
  have b1 : a 23 ≠ 22 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 22 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,4,5,23] := remove (a 23) 22 [0,1,2,3,4,5,22,23] t0 b1
  have b2 : a 23 ≠ 23 := exclude [0,6] (fun u v => edge r27 v u) (a 23) (a 7) 23 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,2,3,4,5] := remove (a 23) 23 [0,1,2,3,4,5,23] t1 b2
  have b3 : a 10 ≠ 3 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,6,11,12,14,15,18,21,23] := remove (a 10) 3 [0,3,6,11,12,14,15,18,21,23] d10 b3
  have b4 : a 10 ≠ 6 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 6 d8 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,11,12,14,15,18,21,23] := remove (a 10) 6 [0,6,11,12,14,15,18,21,23] t3 b4
  have b5 : a 10 ≠ 11 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 11 d8 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0,12,14,15,18,21,23] := remove (a 10) 11 [0,11,12,14,15,18,21,23] t4 b5
  have b6 : a 10 ≠ 14 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 14 d8 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,12,15,18,21,23] := remove (a 10) 14 [0,12,14,15,18,21,23] t5 b6
  have b7 : a 10 ≠ 15 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 15 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,12,18,21,23] := remove (a 10) 15 [0,12,15,18,21,23] t6 b7
  have b8 : a 10 ≠ 18 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 18 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,12,21,23] := remove (a 10) 18 [0,12,18,21,23] t7 b8
  have b9 : a 10 ≠ 21 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 21 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,12,23] := remove (a 10) 21 [0,12,21,23] t8 b9
  have b10 : a 10 ≠ 23 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 23 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,12] := remove (a 10) 23 [0,12,23] t9 b10
  have b11 : a 11 ≠ 6 := exclude [0,3] (fun u v => edge r32 v u) (a 11) (a 9) 6 d9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,1,9] := remove (a 11) 6 [0,1,6,9] d11 b11
  have b12 : a 13 ≠ 1 := exclude [0,3] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,3] := remove (a 13) 1 [0,1,3] d13 b12
  have b13 : a 13 ≠ 3 := exclude [0,3] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0] := remove (a 13) 3 [0,3] t12 b13
  have b14 : a 25 ≠ 1 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b14
  have b15 : a 25 ≠ 2 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,3] := remove (a 25) 2 [0,2,3] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_186
