import PartitionData205_184
namespace PartitionCover205_184
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,4,5])
    (d5 : a 5 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 4 ∈ [0,1] ∧ a 12 ∈ [0,1] ∧ a 20 ∈ [0,1,12,13,14,15,16,17] := by
  have b0 : a 4 ≠ 4 := exclude [0,1] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,5] := remove (a 4) 4 [0,1,4,5] d4 b0
  have b1 : a 4 ≠ 5 := exclude [0,1] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t1 : a 4 ∈ [0,1] := remove (a 4) 5 [0,1,5] t0 b1
  have b2 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 t1 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b2
  have b3 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 t1 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t2 b3
  have b4 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 t1 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] t3 b4
  have b5 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 t1 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t4 b5
  have b6 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 2 t1 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b6
  have b7 : a 20 ≠ 3 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 3 t1 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 t1 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 5 t1 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 20 ≠ 6 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 6 t1 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 20 ≠ 7 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 7 t1 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 20 ≠ 8 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 8 t1 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 20) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 20 ≠ 9 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 9 t1 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 20) 9 [0,1,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 20 ≠ 10 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 10 t1 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 20) 10 [0,1,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 11 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 11 t1 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,12,13,14,15,16,17] := remove (a 20) 11 [0,1,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t5 (t15))

theorem chunk5 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 20 ∈ [0,1,12,16] ∧ a 13 ∈ [0,1] ∧ a 21 ∈ [0,1] ∧ a 6 ∈ [0,2] ∧ a 14 ∈ [0,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 20 ≠ 13 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,12,14,15,16,17] := remove (a 20) 13 [0,1,12,13,14,15,16,17] d20 b0
  have b1 : a 20 ≠ 14 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 14 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,12,15,16,17] := remove (a 20) 14 [0,1,12,14,15,16,17] t0 b1
  have b2 : a 20 ≠ 15 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,12,16,17] := remove (a 20) 15 [0,1,12,15,16,17] t1 b2
  have b3 : a 20 ≠ 17 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 17 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,12,16] := remove (a 20) 17 [0,1,12,16,17] t2 b3
  have b4 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t4 b5
  have b6 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] t5 b6
  have b7 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t6 b7
  have b8 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b8
  have b9 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t8 b9
  have b10 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t9 b10
  have b11 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t10 b11
  have b12 : a 6 ≠ 1 := exclude [0] (edge r23) (a 6) (a 7) 1 d7 c23 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b12
  have b13 : a 6 ≠ 3 := exclude [0] (edge r23) (a 6) (a 7) 3 d7 c23 (by decide +kernel)
  have t13 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t12 b13
  have b14 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 t13 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b14
  have b15 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t13 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t11 (And.intro t13 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2])
    (d7 : a 7 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2])
    (d11 : a 11 ∈ [0,1])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 14 ∈ [0,2] ∧ a 15 ∈ [0,1] ∧ a 23 ∈ [0,2] ∧ a 24 ∈ [0,3] ∧ a 9 ∈ [0,1] := by
  have b0 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,6,7,8,9,10,11] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,7,8,9,10,11] := remove (a 14) 6 [0,2,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,8,9,10,11] := remove (a 14) 7 [0,2,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 8 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,9,10,11] := remove (a 14) 8 [0,2,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 9 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,10,11] := remove (a 14) 9 [0,2,9,10,11] t4 b5
  have b6 : a 14 ≠ 10 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,2,11] := remove (a 14) 10 [0,2,10,11] t5 b6
  have b7 : a 14 ≠ 11 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2] := remove (a 14) 11 [0,2,11] t6 b7
  have b8 : a 15 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,1] := remove (a 15) 2 [0,1,2] d15 b8
  have b9 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,2,3,4,5] := remove (a 23) 1 [0,1,2,3,4,5] d23 b9
  have b10 : a 23 ≠ 3 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,2,4,5] := remove (a 23) 3 [0,2,3,4,5] t9 b10
  have b11 : a 23 ≠ 4 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,2,5] := remove (a 23) 4 [0,2,4,5] t10 b11
  have b12 : a 23 ≠ 5 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,2] := remove (a 23) 5 [0,2,5] t11 b12
  have b13 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b13
  have b14 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,3] := remove (a 24) 2 [0,2,3] t13 b14
  have b15 : a 9 ≠ 2 := exclude [0,1] (edge r32) (a 9) (a 11) 2 d11 c32 (by decide +kernel)
  have t15 : a 9 ∈ [0,1] := remove (a 9) 2 [0,1,2] d9 b15
  exact And.intro t7 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] ∧ a 10 ∈ [0,2] ∧ a 26 ∈ [0,1,2,4] ∧ a 27 ∈ [0,1,2,3,10,11] := by
  have b0 : a 25 ≠ 12 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] := remove (a 25) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b0
  have b1 : a 25 ≠ 13 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] := remove (a 25) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] t0 b1
  have b2 : a 25 ≠ 14 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] := remove (a 25) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] t1 b2
  have b3 : a 25 ≠ 15 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := remove (a 25) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] t2 b3
  have b4 : a 25 ≠ 16 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17] := remove (a 25) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17] t3 b4
  have b5 : a 25 ≠ 17 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,1] (edge r35) (a 10) (a 11) 1 d11 c35 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,1] (edge r35) (a 10) (a 11) 3 d11 c35 (by decide +kernel)
  have t7 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t6 b7
  have b8 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 3 t7 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,4,5] := remove (a 26) 3 [0,1,2,3,4,5] d26 b8
  have b9 : a 26 ≠ 5 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 5 t7 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,2,4] := remove (a 26) 5 [0,1,2,4,5] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b10
  have b11 : a 27 ≠ 5 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 27) 5 [0,1,2,3,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 6 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 27) 6 [0,1,2,3,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 7 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,2,3,8,9,10,11] := remove (a 27) 7 [0,1,2,3,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,2,3,9,10,11] := remove (a 27) 8 [0,1,2,3,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 9 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,2,3,10,11] := remove (a 27) 9 [0,1,2,3,9,10,11] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_184
