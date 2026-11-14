import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,8,14,15,16,17,18,19,20,21,22,23])
    (d5 : a 5 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,2])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 21 ∈ [0,8] ∧ a 14 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 21 ≠ 14 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 14 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,8,15,16,17,18,19,20,21,22,23] := remove (a 21) 14 [0,8,14,15,16,17,18,19,20,21,22,23] d21 b0
  have b1 : a 21 ≠ 15 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 15 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,8,16,17,18,19,20,21,22,23] := remove (a 21) 15 [0,8,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 21 ≠ 16 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 16 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,8,17,18,19,20,21,22,23] := remove (a 21) 16 [0,8,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 21 ≠ 17 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 17 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,8,18,19,20,21,22,23] := remove (a 21) 17 [0,8,17,18,19,20,21,22,23] t2 b3
  have b4 : a 21 ≠ 18 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 18 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,8,19,20,21,22,23] := remove (a 21) 18 [0,8,18,19,20,21,22,23] t3 b4
  have b5 : a 21 ≠ 19 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 19 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,8,20,21,22,23] := remove (a 21) 19 [0,8,19,20,21,22,23] t4 b5
  have b6 : a 21 ≠ 20 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 20 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,8,21,22,23] := remove (a 21) 20 [0,8,20,21,22,23] t5 b6
  have b7 : a 21 ≠ 21 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 21 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,8,22,23] := remove (a 21) 21 [0,8,21,22,23] t6 b7
  have b8 : a 21 ≠ 22 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 22 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,8,23] := remove (a 21) 22 [0,8,22,23] t7 b8
  have b9 : a 21 ≠ 23 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 23 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,8] := remove (a 21) 23 [0,8,23] t8 b9
  have b10 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b10
  have b11 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t9 (t15)

theorem chunk17 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,2])
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 14 ∈ [0,2] := by
  have b0 : a 14 ≠ 8 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b0
  have b1 : a 14 ≠ 9 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 14 ≠ 10 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 14 ≠ 11 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 14 ≠ 12 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 12 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 12 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 14 ≠ 13 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 13 [0,2,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 14 ≠ 14 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,2,15,16,17,18,19,20,21,22,23] := remove (a 14) 14 [0,2,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 14 ≠ 15 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,16,17,18,19,20,21,22,23] := remove (a 14) 15 [0,2,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 14 ≠ 16 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,17,18,19,20,21,22,23] := remove (a 14) 16 [0,2,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 14 ≠ 17 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,18,19,20,21,22,23] := remove (a 14) 17 [0,2,17,18,19,20,21,22,23] t8 b9
  have b10 : a 14 ≠ 18 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 18 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,19,20,21,22,23] := remove (a 14) 18 [0,2,18,19,20,21,22,23] t9 b10
  have b11 : a 14 ≠ 19 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 19 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,20,21,22,23] := remove (a 14) 19 [0,2,19,20,21,22,23] t10 b11
  have b12 : a 14 ≠ 20 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 20 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,21,22,23] := remove (a 14) 20 [0,2,20,21,22,23] t11 b12
  have b13 : a 14 ≠ 21 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 21 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,22,23] := remove (a 14) 21 [0,2,21,22,23] t12 b13
  have b14 : a 14 ≠ 22 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 22 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,23] := remove (a 14) 22 [0,2,22,23] t13 b14
  have b15 : a 14 ≠ 23 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 23 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2] := remove (a 14) 23 [0,2,23] t14 b15
  exact t15

theorem chunk18 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,2])
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 22 ∈ [0,2,18,19,20,21,22,23] := by
  have b0 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d22 b0
  have b1 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 22 ≠ 4 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 22 ≠ 6 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 22 ≠ 7 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 22 ≠ 8 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 22 ≠ 9 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 22 ≠ 10 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 22 ≠ 11 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 22 ≠ 12 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 12 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 12 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 22 ≠ 13 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 13 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 13 [0,2,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 22 ≠ 14 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 14 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,15,16,17,18,19,20,21,22,23] := remove (a 22) 14 [0,2,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 22 ≠ 15 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 15 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,16,17,18,19,20,21,22,23] := remove (a 22) 15 [0,2,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 22 ≠ 16 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,17,18,19,20,21,22,23] := remove (a 22) 16 [0,2,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 22 ≠ 17 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,18,19,20,21,22,23] := remove (a 22) 17 [0,2,17,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk19 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,2])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 22 ∈ [0,2] ∧ a 23 ∈ [0,2] := by
  have b0 : a 22 ≠ 18 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 18 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,19,20,21,22,23] := remove (a 22) 18 [0,2,18,19,20,21,22,23] d22 b0
  have b1 : a 22 ≠ 19 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 19 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,20,21,22,23] := remove (a 22) 19 [0,2,19,20,21,22,23] t0 b1
  have b2 : a 22 ≠ 20 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 20 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,21,22,23] := remove (a 22) 20 [0,2,20,21,22,23] t1 b2
  have b3 : a 22 ≠ 21 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 21 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,22,23] := remove (a 22) 21 [0,2,21,22,23] t2 b3
  have b4 : a 22 ≠ 22 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 22 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,23] := remove (a 22) 22 [0,2,22,23] t3 b4
  have b5 : a 22 ≠ 23 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 23 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,2] := remove (a 22) 23 [0,2,23] t4 b5
  have b6 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 4 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 23) 4 [0,2,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,2,6,7,8,9,10,11] := remove (a 23) 5 [0,2,5,6,7,8,9,10,11] t8 b9
  have b10 : a 23 ≠ 6 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,2,7,8,9,10,11] := remove (a 23) 6 [0,2,6,7,8,9,10,11] t9 b10
  have b11 : a 23 ≠ 7 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,2,8,9,10,11] := remove (a 23) 7 [0,2,7,8,9,10,11] t10 b11
  have b12 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,2,9,10,11] := remove (a 23) 8 [0,2,8,9,10,11] t11 b12
  have b13 : a 23 ≠ 9 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,2,10,11] := remove (a 23) 9 [0,2,9,10,11] t12 b13
  have b14 : a 23 ≠ 10 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,2,11] := remove (a 23) 10 [0,2,10,11] t13 b14
  have b15 : a 23 ≠ 11 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,2] := remove (a 23) 11 [0,2,11] t14 b15
  exact And.intro t5 (t15)

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_217
