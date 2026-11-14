import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0,4])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 12 ∈ [0,12,16,20] ∧ a 13 ∈ [0,1,2,6,7,8] ∧ a 21 ∈ [0,3,4,5] := by
  have b0 : a 12 ≠ 10 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b0
  have b1 : a 12 ≠ 11 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 12 ≠ 13 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 13 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,12,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 13 [0,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 12 ≠ 14 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,12,15,16,17,18,19,20,21,22,23] := remove (a 12) 14 [0,12,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 12 ≠ 15 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,12,16,17,18,19,20,21,22,23] := remove (a 12) 15 [0,12,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 12 ≠ 17 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 17 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,12,16,18,19,20,21,22,23] := remove (a 12) 17 [0,12,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 12 ≠ 18 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 18 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,12,16,19,20,21,22,23] := remove (a 12) 18 [0,12,16,18,19,20,21,22,23] t5 b6
  have b7 : a 12 ≠ 19 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 19 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,12,16,20,21,22,23] := remove (a 12) 19 [0,12,16,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 21 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 21 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,12,16,20,22,23] := remove (a 12) 21 [0,12,16,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 22 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,12,16,20,23] := remove (a 12) 22 [0,12,16,20,22,23] t8 b9
  have b10 : a 12 ≠ 23 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 23 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,12,16,20] := remove (a 12) 23 [0,12,16,20,23] t9 b10
  have b11 : a 13 ≠ 3 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,4,5,6,7,8] := remove (a 13) 3 [0,1,2,3,4,5,6,7,8] d13 b11
  have b12 : a 13 ≠ 4 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,5,6,7,8] := remove (a 13) 4 [0,1,2,4,5,6,7,8] t11 b12
  have b13 : a 13 ≠ 5 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,6,7,8] := remove (a 13) 5 [0,1,2,5,6,7,8] t12 b13
  have b14 : a 21 ≠ 1 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b14
  have b15 : a 21 ≠ 2 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t14 b15
  exact And.intro t10 (And.intro t13 (t15))

theorem chunk5 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,3,4,5])
    (d5 : a 5 ∈ [0,4])
    (d7 : a 7 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,9])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 21 ∈ [0,4] ∧ a 7 ∈ [0,1,3] ∧ a 14 ∈ [0,9] ∧ a 22 ∈ [0,3,5] := by
  have b0 : a 21 ≠ 3 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,4,5] := remove (a 21) 3 [0,3,4,5] d21 b0
  have b1 : a 21 ≠ 5 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,4] := remove (a 21) 5 [0,4,5] t0 b1
  have b2 : a 7 ≠ 2 := exclude [0,9] (fun u v => edge r23 v u) (a 7) (a 6) 2 d6 c23 (by decide +kernel)
  have t2 : a 7 ∈ [0,1,3] := remove (a 7) 2 [0,1,2,3] d7 b2
  have b3 : a 14 ≠ 1 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b3
  have b4 : a 14 ≠ 2 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 3 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 14 ≠ 4 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,5,6,7,8,9,10,11] := remove (a 14) 4 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 14 ≠ 5 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,6,7,8,9,10,11] := remove (a 14) 5 [0,5,6,7,8,9,10,11] t6 b7
  have b8 : a 14 ≠ 6 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,7,8,9,10,11] := remove (a 14) 6 [0,6,7,8,9,10,11] t7 b8
  have b9 : a 14 ≠ 7 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,8,9,10,11] := remove (a 14) 7 [0,7,8,9,10,11] t8 b9
  have b10 : a 14 ≠ 8 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,9,10,11] := remove (a 14) 8 [0,8,9,10,11] t9 b10
  have b11 : a 14 ≠ 10 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,9,11] := remove (a 14) 10 [0,9,10,11] t10 b11
  have b12 : a 14 ≠ 11 := exclude [0,9] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,9] := remove (a 14) 11 [0,9,11] t11 b12
  have b13 : a 22 ≠ 1 := exclude [0,9] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b13
  have b14 : a 22 ≠ 2 := exclude [0,9] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] t13 b14
  have b15 : a 22 ≠ 4 := exclude [0,9] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,3,5] := remove (a 22) 4 [0,3,4,5] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t12 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,3,5])
    (d6 : a 6 ∈ [0,9])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d7 : a 7 ∈ [0,1,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,17,20,21,22,23])
    (d8 : a 8 ∈ [0,1,2,3])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 22 ∈ [0,3] ∧ a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] ∧ a 23 ∈ [0,1,2,3,4,5,6,7,12,13,16,17,18,19] ∧ a 10 ∈ [0,4,5,6,7,10,11,15,17,20,21,22,23] := by
  have b0 : a 22 ≠ 5 := exclude [0,9] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,3] := remove (a 22) 5 [0,3,5] d22 b0
  have b1 : a 15 ≠ 6 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d15 b1
  have b2 : a 15 ≠ 7 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 15 ≠ 8 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 15 ≠ 9 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 15 ≠ 16 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 16 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,17,18,19,20,21,22,23] := remove (a 15) 16 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 15 ≠ 17 := exclude [0,1,3] (fun u v => edge r26 v u) (a 15) (a 7) 17 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 17 [0,1,2,3,4,5,10,11,12,13,14,15,17,18,19,20,21,22,23] t5 b6
  have b7 : a 23 ≠ 8 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 8 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d23 b7
  have b8 : a 23 ≠ 9 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 9 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 23 ≠ 10 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19] := remove (a 23) 10 [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 23 ≠ 11 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19] := remove (a 23) 11 [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 23 ≠ 14 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 14 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,3,4,5,6,7,12,13,15,16,17,18,19] := remove (a 23) 14 [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 23 ≠ 15 := exclude [0,1,3] (fun u v => edge r27 v u) (a 23) (a 7) 15 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3,4,5,6,7,12,13,16,17,18,19] := remove (a 23) 15 [0,1,2,3,4,5,6,7,12,13,15,16,17,18,19] t11 b12
  have b13 : a 10 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t13 : a 10 ∈ [0,2,3,4,5,6,7,10,11,15,17,20,21,22,23] := remove (a 10) 1 [0,1,2,3,4,5,6,7,10,11,15,17,20,21,22,23] d10 b13
  have b14 : a 10 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t14 : a 10 ∈ [0,3,4,5,6,7,10,11,15,17,20,21,22,23] := remove (a 10) 2 [0,2,3,4,5,6,7,10,11,15,17,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t15 : a 10 ∈ [0,4,5,6,7,10,11,15,17,20,21,22,23] := remove (a 10) 3 [0,3,4,5,6,7,10,11,15,17,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t6 (And.intro t12 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,4,5,6,7,10,11,15,17,20,21,22,23])
    (d8 : a 8 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 10 ∈ [0,5,7,23] ∧ a 24 ∈ [0,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 10 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t0 : a 10 ∈ [0,5,6,7,10,11,15,17,20,21,22,23] := remove (a 10) 4 [0,4,5,6,7,10,11,15,17,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 6 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 6 d8 c29 (by decide +kernel)
  have t1 : a 10 ∈ [0,5,7,10,11,15,17,20,21,22,23] := remove (a 10) 6 [0,5,6,7,10,11,15,17,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 10 d8 c29 (by decide +kernel)
  have t2 : a 10 ∈ [0,5,7,11,15,17,20,21,22,23] := remove (a 10) 10 [0,5,7,10,11,15,17,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 11 d8 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,5,7,15,17,20,21,22,23] := remove (a 10) 11 [0,5,7,11,15,17,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 15 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 15 d8 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,5,7,17,20,21,22,23] := remove (a 10) 15 [0,5,7,15,17,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 17 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 17 d8 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0,5,7,20,21,22,23] := remove (a 10) 17 [0,5,7,17,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 20 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 20 d8 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,5,7,21,22,23] := remove (a 10) 20 [0,5,7,20,21,22,23] t5 b6
  have b7 : a 10 ≠ 21 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 21 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,5,7,22,23] := remove (a 10) 21 [0,5,7,21,22,23] t6 b7
  have b8 : a 10 ≠ 22 := exclude [0,1,2,3] (fun u v => edge r29 v u) (a 10) (a 8) 22 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,5,7,23] := remove (a 10) 22 [0,5,7,22,23] t7 b8
  have b9 : a 24 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b9
  have b10 : a 24 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 24 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 24 ≠ 6 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 6 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 24 ≠ 7 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 7 [0,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 24 ≠ 8 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 8 [0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 24 ≠ 9 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 9 [0,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_191
