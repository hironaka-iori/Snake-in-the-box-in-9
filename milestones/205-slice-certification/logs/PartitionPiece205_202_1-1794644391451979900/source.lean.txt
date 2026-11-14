import PartitionData205_202
namespace PartitionCover205_202
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,6,7])
    (d4 : a 4 ∈ [0,12])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 5 ∈ [0,6] ∧ a 20 ∈ [0,6] ∧ a 13 ∈ [0,2] ∧ a 21 ∈ [0,3,5] := by
  have b0 : a 5 ≠ 7 := exclude [0,12] (fun u v => edge r16 v u) (a 5) (a 4) 7 d4 c16 (by decide +kernel)
  have t0 : a 5 ∈ [0,6] := remove (a 5) 7 [0,6,7] d5 b0
  have b1 : a 20 ≠ 1 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b1
  have b2 : a 20 ≠ 2 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 20 ≠ 3 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 20 ≠ 4 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,5,6,7,8,9,10,11] := remove (a 20) 4 [0,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 20 ≠ 5 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,6,7,8,9,10,11] := remove (a 20) 5 [0,5,6,7,8,9,10,11] t4 b5
  have b6 : a 20 ≠ 7 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,6,8,9,10,11] := remove (a 20) 7 [0,6,7,8,9,10,11] t5 b6
  have b7 : a 20 ≠ 8 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,6,9,10,11] := remove (a 20) 8 [0,6,8,9,10,11] t6 b7
  have b8 : a 20 ≠ 9 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,6,10,11] := remove (a 20) 9 [0,6,9,10,11] t7 b8
  have b9 : a 20 ≠ 10 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,6,11] := remove (a 20) 10 [0,6,10,11] t8 b9
  have b10 : a 20 ≠ 11 := exclude [0,12] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,6] := remove (a 20) 11 [0,6,11] t9 b10
  have b11 : a 13 ≠ 1 := exclude [0,6] (fun u v => edge r21 v u) (a 13) (a 5) 1 t0 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b11
  have b12 : a 13 ≠ 3 := exclude [0,6] (fun u v => edge r21 v u) (a 13) (a 5) 3 t0 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t11 b12
  have b13 : a 21 ≠ 1 := exclude [0,6] (fun u v => edge r22 v u) (a 21) (a 5) 1 t0 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b13
  have b14 : a 21 ≠ 2 := exclude [0,6] (fun u v => edge r22 v u) (a 21) (a 5) 2 t0 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t13 b14
  have b15 : a 21 ≠ 4 := exclude [0,6] (fun u v => edge r22 v u) (a 21) (a 5) 4 t0 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,3,5] := remove (a 21) 4 [0,3,4,5] t14 b15
  exact And.intro t0 (And.intro t10 (And.intro t12 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,3,5])
    (d5 : a 5 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 21 ∈ [0,3] ∧ a 14 ∈ [0,1,8,9] ∧ a 22 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 21 ≠ 5 := exclude [0,6] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,3] := remove (a 21) 5 [0,3,5] d21 b0
  have b1 : a 14 ≠ 2 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b1
  have b2 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 14) 4 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,6,7,8,9,10,11] := remove (a 14) 5 [0,1,5,6,7,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,7,8,9,10,11] := remove (a 14) 6 [0,1,6,7,8,9,10,11] t4 b5
  have b6 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,8,9,10,11] := remove (a 14) 7 [0,1,7,8,9,10,11] t5 b6
  have b7 : a 14 ≠ 10 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,8,9,11] := remove (a 14) 10 [0,1,8,9,10,11] t6 b7
  have b8 : a 14 ≠ 11 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,8,9] := remove (a 14) 11 [0,1,8,9,11] t7 b8
  have b9 : a 22 ≠ 4 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d22 b9
  have b10 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 22 ≠ 6 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 22 ≠ 7 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 22 ≠ 8 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 22 ≠ 9 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19] := remove (a 22) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 22 ≠ 10 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19] := remove (a 22) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t0 (And.intro t8 (t15))

theorem chunk6 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19])
    (d6 : a 6 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7])
    (d7 : a 7 ∈ [0,2])
    (d10 : a 10 ∈ [0,2,8,10])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 22 ∈ [0,1,2,3,12,13,14,15] ∧ a 15 ∈ [0,1,4,5] ∧ a 10 ∈ [0,8] ∧ a 24 ∈ [0,6,7,8,9,10,11] := by
  have b0 : a 22 ≠ 11 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,2,3,12,13,14,15,16,17,18,19] := remove (a 22) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19] d22 b0
  have b1 : a 22 ≠ 16 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,2,3,12,13,14,15,17,18,19] := remove (a 22) 16 [0,1,2,3,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 22 ≠ 17 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,1,2,3,12,13,14,15,18,19] := remove (a 22) 17 [0,1,2,3,12,13,14,15,17,18,19] t1 b2
  have b3 : a 22 ≠ 18 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 18 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,1,2,3,12,13,14,15,19] := remove (a 22) 18 [0,1,2,3,12,13,14,15,18,19] t2 b3
  have b4 : a 22 ≠ 19 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 19 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,2,3,12,13,14,15] := remove (a 22) 19 [0,1,2,3,12,13,14,15,19] t3 b4
  have b5 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,3,4,5,6,7] := remove (a 15) 2 [0,1,2,3,4,5,6,7] d15 b5
  have b6 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,4,5,6,7] := remove (a 15) 3 [0,1,3,4,5,6,7] t5 b6
  have b7 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,4,5,7] := remove (a 15) 6 [0,1,4,5,6,7] t6 b7
  have b8 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,4,5] := remove (a 15) 7 [0,1,4,5,7] t7 b8
  have b9 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,8,10] := remove (a 10) 2 [0,2,8,10] d10 b9
  have b10 : a 10 ≠ 10 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 10 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,8] := remove (a 10) 10 [0,8,10] t9 b10
  have b11 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b11
  have b12 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] t14 b15
  exact And.intro t4 (And.intro t8 (And.intro t10 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7])
    (d9 : a 9 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0,8])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 24 ∈ [0,6] ∧ a 25 ∈ [0,2,4,6] ∧ a 26 ∈ [0,4,6,10,11] := by
  have b0 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,6,8,9,10,11] := remove (a 24) 7 [0,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 8 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,6,9,10,11] := remove (a 24) 8 [0,6,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 9 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,6,10,11] := remove (a 24) 9 [0,6,9,10,11] t1 b2
  have b3 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,6,11] := remove (a 24) 10 [0,6,10,11] t2 b3
  have b4 : a 24 ≠ 11 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,6] := remove (a 24) 11 [0,6,11] t3 b4
  have b5 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,3,4,5,6,7] := remove (a 25) 1 [0,1,2,3,4,5,6,7] d25 b5
  have b6 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,4,5,6,7] := remove (a 25) 3 [0,2,3,4,5,6,7] t5 b6
  have b7 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,4,6,7] := remove (a 25) 5 [0,2,4,5,6,7] t6 b7
  have b8 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,4,6] := remove (a 25) 7 [0,2,4,6,7] t7 b8
  have b9 : a 26 ≠ 1 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b9
  have b10 : a 26 ≠ 2 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 3 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 26 ≠ 5 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,4,6,7,8,9,10,11] := remove (a 26) 5 [0,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 26 ≠ 7 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,6,8,9,10,11] := remove (a 26) 7 [0,4,6,7,8,9,10,11] t12 b13
  have b14 : a 26 ≠ 8 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,6,9,10,11] := remove (a 26) 8 [0,4,6,8,9,10,11] t13 b14
  have b15 : a 26 ≠ 9 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,6,10,11] := remove (a 26) 9 [0,4,6,9,10,11] t14 b15
  exact And.intro t4 (And.intro t8 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_202
