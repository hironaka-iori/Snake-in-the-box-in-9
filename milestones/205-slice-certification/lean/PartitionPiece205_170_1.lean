import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,2])
    (d5 : a 5 ∈ [0,1,4,5])
    (d6 : a 6 ∈ [0,2,3,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 6 ∈ [0,2] ∧ a 12 ∈ [0,5,12,13,14,15,16,17] := by
  have b0 : a 4 ≠ 2 := exclude [0,1,4,5] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t0 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 t0 c16 (by decide +kernel)
  have t1 : a 5 ∈ [0,4,5] := remove (a 5) 1 [0,1,4,5] d5 b1
  have b2 : a 5 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 4 t0 c16 (by decide +kernel)
  have t2 : a 5 ∈ [0,5] := remove (a 5) 4 [0,4,5] t1 b2
  have b3 : a 5 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 5 t0 c16 (by decide +kernel)
  have t3 : a 5 ∈ [0] := remove (a 5) 5 [0,5] t2 b3
  have b4 : a 6 ≠ 3 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 3 t0 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,5] := remove (a 6) 3 [0,2,3,5] d6 b4
  have b5 : a 6 ≠ 5 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 5 t0 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0,2] := remove (a 6) 5 [0,2,5] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t0 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d12 b6
  have b7 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 t0 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 12 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 3 t0 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 4 t0 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 12 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 6 t0 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 6 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 12 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 7 t0 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,5,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 7 [0,5,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 12 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 8 t0 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,5,9,10,11,12,13,14,15,16,17] := remove (a 12) 8 [0,5,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 12 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 9 t0 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,5,10,11,12,13,14,15,16,17] := remove (a 12) 9 [0,5,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 12 ≠ 10 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 10 t0 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,5,11,12,13,14,15,16,17] := remove (a 12) 10 [0,5,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 12 ≠ 11 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 11 t0 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,5,12,13,14,15,16,17] := remove (a 12) 11 [0,5,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t3 (And.intro t5 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,5,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 12 ∈ [0,5] ∧ a 20 ∈ [0,11,12,13,14,15,16,17] := by
  have b0 : a 12 ≠ 12 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 12 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,5,13,14,15,16,17] := remove (a 12) 12 [0,5,12,13,14,15,16,17] d12 b0
  have b1 : a 12 ≠ 13 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 13 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,5,14,15,16,17] := remove (a 12) 13 [0,5,13,14,15,16,17] t0 b1
  have b2 : a 12 ≠ 14 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,5,15,16,17] := remove (a 12) 14 [0,5,14,15,16,17] t1 b2
  have b3 : a 12 ≠ 15 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,5,16,17] := remove (a 12) 15 [0,5,15,16,17] t2 b3
  have b4 : a 12 ≠ 16 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 16 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,5,17] := remove (a 12) 16 [0,5,16,17] t3 b4
  have b5 : a 12 ≠ 17 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 17 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,5] := remove (a 12) 17 [0,5,17] t4 b5
  have b6 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b6
  have b7 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 20 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 20 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 20) 8 [0,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 20 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 20) 9 [0,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,11,12,13,14,15,16,17] := remove (a 20) 10 [0,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t5 (t15)

theorem chunk6 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0])
    (d7 : a 7 ∈ [0,1,2])
    (d5 : a 5 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,2])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    : a 20 ∈ [0,12,14] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0,2,3] ∧ a 21 ∈ [0,2] ∧ a 6 ∈ [0] := by
  have b0 : a 20 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,12,13,14,15,16,17] := remove (a 20) 11 [0,11,12,13,14,15,16,17] d20 b0
  have b1 : a 20 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,12,14,15,16,17] := remove (a 20) 13 [0,12,13,14,15,16,17] t0 b1
  have b2 : a 20 ≠ 15 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,12,14,16,17] := remove (a 20) 15 [0,12,14,15,16,17] t1 b2
  have b3 : a 20 ≠ 16 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 16 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,12,14,17] := remove (a 20) 16 [0,12,14,16,17] t2 b3
  have b4 : a 20 ≠ 17 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 17 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,12,14] := remove (a 20) 17 [0,12,14,17] t3 b4
  have b5 : a 7 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t5 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b5
  have b6 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 d5 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 2 [0,2] t5 b6
  have b7 : a 13 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b7
  have b8 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,2,3,4,5,6,7,8] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8] d21 b8
  have b9 : a 21 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,4,5,6,7,8] := remove (a 21) 3 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 21 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,2,5,6,7,8] := remove (a 21) 4 [0,2,4,5,6,7,8] t9 b10
  have b11 : a 21 ≠ 5 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,6,7,8] := remove (a 21) 5 [0,2,5,6,7,8] t10 b11
  have b12 : a 21 ≠ 6 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,2,7,8] := remove (a 21) 6 [0,2,6,7,8] t11 b12
  have b13 : a 21 ≠ 7 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,2,8] := remove (a 21) 7 [0,2,7,8] t12 b13
  have b14 : a 21 ≠ 8 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,2] := remove (a 21) 8 [0,2,8] t13 b14
  have b15 : a 6 ≠ 2 := exclude [0] (edge r23) (a 6) (a 7) 2 t6 c23 (by decide +kernel)
  have t15 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b15
  exact And.intro t4 (And.intro t6 (And.intro t7 (And.intro t14 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 14 ∈ [0,1,2,3] ∧ a 22 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 14 ≠ 6 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 7 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 8 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 9 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,3,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 10 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,3,11,12,13,14,15,16,17] := remove (a 14) 10 [0,1,2,3,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 11 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,2,3,12,13,14,15,16,17] := remove (a 14) 11 [0,1,2,3,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 12 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 12 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,2,3,13,14,15,16,17] := remove (a 14) 12 [0,1,2,3,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 13 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,2,3,14,15,16,17] := remove (a 14) 13 [0,1,2,3,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 14 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,3,15,16,17] := remove (a 14) 14 [0,1,2,3,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 15 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,3,16,17] := remove (a 14) 15 [0,1,2,3,15,16,17] t10 b11
  have b12 : a 14 ≠ 16 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,3,17] := remove (a 14) 16 [0,1,2,3,16,17] t11 b12
  have b13 : a 14 ≠ 17 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,2,3] := remove (a 14) 17 [0,1,2,3,17] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d22 b14
  have b15 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t13 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_170
