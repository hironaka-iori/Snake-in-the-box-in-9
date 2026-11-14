import PartitionData205_163
namespace PartitionCover205_163
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 5 ∈ [0,1] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 6 ∈ [0,4,5] := by
  have b0 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,3,4,5] := remove (a 5) 2 [0,1,2,3,4,5] d5 b0
  have b1 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,4,5] := remove (a 5) 3 [0,1,3,4,5] t0 b1
  have b2 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,5] := remove (a 5) 4 [0,1,4,5] t1 b2
  have b3 : a 5 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,1] := remove (a 5) 5 [0,1,5] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2] := remove (a 9) 1 [0,1,2] d9 b4
  have b5 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 2 [0,2] t4 b5
  have b6 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,2,3,4,5,6,7] := remove (a 17) 1 [0,1,2,3,4,5,6,7] d17 b6
  have b7 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,3,4,5,6,7] := remove (a 17) 2 [0,2,3,4,5,6,7] t6 b7
  have b8 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,4,5,6,7] := remove (a 17) 3 [0,3,4,5,6,7] t7 b8
  have b9 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,5,6,7] := remove (a 17) 4 [0,4,5,6,7] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,6,7] := remove (a 17) 5 [0,5,6,7] t9 b10
  have b11 : a 17 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,7] := remove (a 17) 6 [0,6,7] t10 b11
  have b12 : a 17 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0] := remove (a 17) 7 [0,7] t11 b12
  have b13 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b13
  have b14 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,3,4,5] := remove (a 6) 2 [0,2,3,4,5] t13 b14
  have b15 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,4,5] := remove (a 6) 3 [0,3,4,5] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t12 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,4,5])
    (d2 : a 2 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 6 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0,1,4,5,10,11,13] := by
  have b0 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,5] := remove (a 6) 4 [0,4,5] d6 b0
  have b1 : a 6 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 5 [0,5] t0 b1
  have b2 : a 4 ≠ 2 := exclude [0,1] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,3,4,5] := remove (a 4) 2 [0,1,2,3,4,5] d4 b2
  have b3 : a 4 ≠ 3 := exclude [0,1] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,4,5] := remove (a 4) 3 [0,1,3,4,5] t2 b3
  have b4 : a 4 ≠ 4 := exclude [0,1] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,5] := remove (a 4) 4 [0,1,4,5] t3 b4
  have b5 : a 4 ≠ 5 := exclude [0,1] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,1] := remove (a 4) 5 [0,1,5] t4 b5
  have b6 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 1 [0,1] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t6 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2] := remove (a 12) 1 [0,1,2] d12 b7
  have b8 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 t6 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 2 [0,2] t7 b8
  have b9 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 t6 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d20 b9
  have b10 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 t6 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11,12,13] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13] t9 b10
  have b11 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 t6 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,4,5,7,8,9,10,11,12,13] := remove (a 20) 6 [0,1,4,5,6,7,8,9,10,11,12,13] t10 b11
  have b12 : a 20 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 7 t6 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,4,5,8,9,10,11,12,13] := remove (a 20) 7 [0,1,4,5,7,8,9,10,11,12,13] t11 b12
  have b13 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 t6 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,4,5,9,10,11,12,13] := remove (a 20) 8 [0,1,4,5,8,9,10,11,12,13] t12 b13
  have b14 : a 20 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 9 t6 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,4,5,10,11,12,13] := remove (a 20) 9 [0,1,4,5,9,10,11,12,13] t13 b14
  have b15 : a 20 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 12 t6 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,4,5,10,11,13] := remove (a 20) 12 [0,1,4,5,10,11,12,13] t14 b15
  exact And.intro t1 (And.intro t6 (And.intro t8 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,4,5,10,11,13])
    (d4 : a 4 ∈ [0])
    (d13 : a 13 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 20 ∈ [0,1,4,5,10,11] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0,3,4,5] := by
  have b0 : a 20 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,4,5,10,11] := remove (a 20) 13 [0,1,4,5,10,11,13] d20 b0
  have b1 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b1
  have b2 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t1 b2
  have b3 : a 21 ≠ 1 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d21 b3
  have b4 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 21) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 21) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,5,6,7,8,9,10,11] := remove (a 21) 4 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,6,7,8,9,10,11] := remove (a 21) 5 [0,5,6,7,8,9,10,11] t6 b7
  have b8 : a 21 ≠ 6 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,7,8,9,10,11] := remove (a 21) 6 [0,6,7,8,9,10,11] t7 b8
  have b9 : a 21 ≠ 7 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,8,9,10,11] := remove (a 21) 7 [0,7,8,9,10,11] t8 b9
  have b10 : a 21 ≠ 8 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,9,10,11] := remove (a 21) 8 [0,8,9,10,11] t9 b10
  have b11 : a 21 ≠ 9 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 9 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,10,11] := remove (a 21) 9 [0,9,10,11] t10 b11
  have b12 : a 21 ≠ 10 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 10 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,11] := remove (a 21) 10 [0,10,11] t11 b12
  have b13 : a 21 ≠ 11 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 11 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 11 [0,11] t12 b13
  have b14 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b14
  have b15 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,3,4,5] := remove (a 14) 2 [0,2,3,4,5] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t13 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,3,4,5])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d7 : a 7 ∈ [0])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 14 ∈ [0] ∧ a 22 ∈ [0,1,2,3] ∧ a 23 ∈ [0,1,2,3,4,5,6,7,18,19] := by
  have b0 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,4,5] := remove (a 14) 3 [0,3,4,5] d14 b0
  have b1 : a 14 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,5] := remove (a 14) 4 [0,4,5] t0 b1
  have b2 : a 14 ≠ 5 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0] := remove (a 14) 5 [0,5] t1 b2
  have b3 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,1,2,3,5,6] := remove (a 22) 4 [0,1,2,3,4,5,6] d22 b3
  have b4 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,2,3,6] := remove (a 22) 5 [0,1,2,3,5,6] t3 b4
  have b5 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,2,3] := remove (a 22) 6 [0,1,2,3,6] t4 b5
  have b6 : a 23 ≠ 8 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 8 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d23 b6
  have b7 : a 23 ≠ 9 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 9 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 23 ≠ 10 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19] := remove (a 23) 10 [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 23 ≠ 11 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19] := remove (a 23) 11 [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 23 ≠ 12 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 12 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,3,4,5,6,7,13,14,15,16,17,18,19] := remove (a 23) 12 [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 23 ≠ 13 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 13 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,3,4,5,6,7,14,15,16,17,18,19] := remove (a 23) 13 [0,1,2,3,4,5,6,7,13,14,15,16,17,18,19] t10 b11
  have b12 : a 23 ≠ 14 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 14 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3,4,5,6,7,15,16,17,18,19] := remove (a 23) 14 [0,1,2,3,4,5,6,7,14,15,16,17,18,19] t11 b12
  have b13 : a 23 ≠ 15 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 15 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,3,4,5,6,7,16,17,18,19] := remove (a 23) 15 [0,1,2,3,4,5,6,7,15,16,17,18,19] t12 b13
  have b14 : a 23 ≠ 16 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 16 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,2,3,4,5,6,7,17,18,19] := remove (a 23) 16 [0,1,2,3,4,5,6,7,16,17,18,19] t13 b14
  have b15 : a 23 ≠ 17 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 17 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,2,3,4,5,6,7,18,19] := remove (a 23) 17 [0,1,2,3,4,5,6,7,17,18,19] t14 b15
  exact And.intro t2 (And.intro t5 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_163
