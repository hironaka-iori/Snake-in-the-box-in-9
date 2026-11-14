import PartitionData205_214
namespace PartitionCover205_214
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,3,4,5])
    (d4 : a 4 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,1,4,5])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0,1,4,5] := by
  have b0 : a 12 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,4,5] := remove (a 12) 3 [0,3,4,5] d12 b0
  have b1 : a 12 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0] := remove (a 12) 5 [0,5] t1 b2
  have b3 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,2,3,4,5,6,7,8] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8] d20 b3
  have b4 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,3,4,5,6,7,8] := remove (a 20) 2 [0,2,3,4,5,6,7,8] t3 b4
  have b5 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,4,5,6,7,8] := remove (a 20) 3 [0,3,4,5,6,7,8] t4 b5
  have b6 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,5,6,7,8] := remove (a 20) 4 [0,4,5,6,7,8] t5 b6
  have b7 : a 20 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,6,7,8] := remove (a 20) 5 [0,5,6,7,8] t6 b7
  have b8 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,7,8] := remove (a 20) 6 [0,6,7,8] t7 b8
  have b9 : a 20 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,8] := remove (a 20) 7 [0,7,8] t8 b9
  have b10 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0] := remove (a 20) 8 [0,8] t9 b10
  have b11 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t11 : a 7 ∈ [0,4,5] := remove (a 7) 1 [0,1,4,5] d7 b11
  have b12 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 4 d5 c20 (by decide +kernel)
  have t12 : a 7 ∈ [0,5] := remove (a 7) 4 [0,4,5] t11 b12
  have b13 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 5 d5 c20 (by decide +kernel)
  have t13 : a 7 ∈ [0] := remove (a 7) 5 [0,5] t12 b13
  have b14 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b14
  have b15 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t13 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,4,5])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0])
    (d8 : a 8 ∈ [0,1,4,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 13 ∈ [0,1] ∧ a 21 ∈ [0,1] ∧ a 22 ∈ [0,2] ∧ a 8 ∈ [0,4] ∧ a 9 ∈ [0,2] := by
  have b0 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] d13 b0
  have b1 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t0 b1
  have b2 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b2
  have b3 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t2 b3
  have b4 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t3 b4
  have b5 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t4 b5
  have b6 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b6
  have b7 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,4,5] := remove (a 22) 3 [0,2,3,4,5] t6 b7
  have b8 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,5] := remove (a 22) 4 [0,2,4,5] t7 b8
  have b9 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,2] := remove (a 22) 5 [0,2,5] t8 b9
  have b10 : a 8 ≠ 1 := exclude [0,1,2,3,4,5] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t10 : a 8 ∈ [0,4,5] := remove (a 8) 1 [0,1,4,5] d8 b10
  have b11 : a 8 ≠ 5 := exclude [0,1,2,3,4,5] (edge r28) (a 8) (a 9) 5 d9 c28 (by decide +kernel)
  have t11 : a 8 ∈ [0,4] := remove (a 8) 5 [0,4,5] t10 b11
  have b12 : a 9 ≠ 1 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 1 t11 c28 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b12
  have b13 : a 9 ≠ 3 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 3 t11 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,2,4,5] := remove (a 9) 3 [0,2,3,4,5] t12 b13
  have b14 : a 9 ≠ 4 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 4 t11 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,2,5] := remove (a 9) 4 [0,2,4,5] t13 b14
  have b15 : a 9 ≠ 5 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 5 t11 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,2] := remove (a 9) 5 [0,2,5] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t9 (And.intro t11 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,4])
    (d12 : a 12 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 8 ∈ [0] ∧ a 24 ∈ [0,6,17] := by
  have b0 : a 8 ≠ 4 := exclude [0] (edge r30) (a 8) (a 12) 4 d12 c30 (by decide +kernel)
  have t0 : a 8 ∈ [0] := remove (a 8) 4 [0,4] d8 b0
  have b1 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t0 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b1
  have b2 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 t0 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t0 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 t0 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 t0 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 t0 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t0 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 t0 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,6,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 24 ≠ 10 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 10 t0 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 24) 10 [0,6,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 11 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 11 t0 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,6,12,13,14,15,16,17] := remove (a 24) 11 [0,6,11,12,13,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 12 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 12 t0 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,6,13,14,15,16,17] := remove (a 24) 12 [0,6,12,13,14,15,16,17] t10 b11
  have b12 : a 24 ≠ 13 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 13 t0 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,6,14,15,16,17] := remove (a 24) 13 [0,6,13,14,15,16,17] t11 b12
  have b13 : a 24 ≠ 14 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 14 t0 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,6,15,16,17] := remove (a 24) 14 [0,6,14,15,16,17] t12 b13
  have b14 : a 24 ≠ 15 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 15 t0 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,6,16,17] := remove (a 24) 15 [0,6,15,16,17] t13 b14
  have b15 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 t0 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,6,17] := remove (a 24) 16 [0,6,16,17] t14 b15
  exact And.intro t0 (t15)

theorem chunk7 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,17])
    (d8 : a 8 ∈ [0])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0,2])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 24 ∈ [0,6] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0,4] ∧ a 14 ∈ [0,2,5] := by
  have b0 : a 24 ≠ 17 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,6] := remove (a 24) 17 [0,6,17] d24 b0
  have b1 : a 9 ≠ 2 := exclude [0,1] (edge r33) (a 9) (a 13) 2 d13 c33 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b1
  have b2 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t1 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b2
  have b3 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 t1 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b3
  have b4 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 t1 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 t1 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 5 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 5 t1 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,4,6,7,8,9,10,11] := remove (a 25) 5 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 25 ≠ 6 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 6 t1 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,4,7,8,9,10,11] := remove (a 25) 6 [0,4,6,7,8,9,10,11] t6 b7
  have b8 : a 25 ≠ 7 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 7 t1 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,4,8,9,10,11] := remove (a 25) 7 [0,4,7,8,9,10,11] t7 b8
  have b9 : a 25 ≠ 8 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 8 t1 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,4,9,10,11] := remove (a 25) 8 [0,4,8,9,10,11] t8 b9
  have b10 : a 25 ≠ 9 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 9 t1 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,4,10,11] := remove (a 25) 9 [0,4,9,10,11] t9 b10
  have b11 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 t1 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,4,11] := remove (a 25) 10 [0,4,10,11] t10 b11
  have b12 : a 25 ≠ 11 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 11 t1 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,4] := remove (a 25) 11 [0,4,11] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b13
  have b14 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,4,5] := remove (a 14) 3 [0,2,3,4,5] t13 b14
  have b15 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,5] := remove (a 14) 4 [0,2,4,5] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t12 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_214
