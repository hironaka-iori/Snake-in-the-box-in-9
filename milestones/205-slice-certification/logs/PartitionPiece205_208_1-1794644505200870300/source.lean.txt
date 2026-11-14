import PartitionData205_208
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d22 : a 22 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,2])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 13 ∈ [0,1,2] ∧ a 21 ∈ [0,2,6,8] ∧ a 22 ∈ [0,2] := by
  have b0 : a 13 ≠ 4 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 13) 4 [0,1,2,4,5,6,7,8,9,10,11] d13 b0
  have b1 : a 13 ≠ 5 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 13) 5 [0,1,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 13 ≠ 6 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,2,7,8,9,10,11] := remove (a 13) 6 [0,1,2,6,7,8,9,10,11] t1 b2
  have b3 : a 13 ≠ 7 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,2,8,9,10,11] := remove (a 13) 7 [0,1,2,7,8,9,10,11] t2 b3
  have b4 : a 13 ≠ 8 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,2,9,10,11] := remove (a 13) 8 [0,1,2,8,9,10,11] t3 b4
  have b5 : a 13 ≠ 9 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,2,10,11] := remove (a 13) 9 [0,1,2,9,10,11] t4 b5
  have b6 : a 13 ≠ 10 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,2,11] := remove (a 13) 10 [0,1,2,10,11] t5 b6
  have b7 : a 13 ≠ 11 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 11 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,2] := remove (a 13) 11 [0,1,2,11] t6 b7
  have b8 : a 21 ≠ 1 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9] d21 b8
  have b9 : a 21 ≠ 3 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,4,5,6,7,8,9] := remove (a 21) 3 [0,2,3,4,5,6,7,8,9] t8 b9
  have b10 : a 21 ≠ 4 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,2,5,6,7,8,9] := remove (a 21) 4 [0,2,4,5,6,7,8,9] t9 b10
  have b11 : a 21 ≠ 5 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,6,7,8,9] := remove (a 21) 5 [0,2,5,6,7,8,9] t10 b11
  have b12 : a 21 ≠ 7 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,2,6,8,9] := remove (a 21) 7 [0,2,6,7,8,9] t11 b12
  have b13 : a 21 ≠ 9 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 9 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,2,6,8] := remove (a 21) 9 [0,2,6,8,9] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b14
  have b15 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t14 b15
  exact And.intro t7 (And.intro t13 (t15))

theorem chunk5 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d7 : a 7 ∈ [0,1,4,5])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d9 : a 9 ∈ [0,4,8,12])
    (d8 : a 8 ∈ [0,6])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 15 ∈ [0,1,2,3,8,9,10,11] ∧ a 23 ∈ [0,1,2,3,6,7] ∧ a 9 ∈ [0,8] ∧ a 24 ∈ [0,2,6,7,8,9,10,11] := by
  have b0 : a 15 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13] := remove (a 15) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d15 b0
  have b1 : a 15 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,3,6,7,8,9,10,11,12,13] := remove (a 15) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13] t0 b1
  have b2 : a 15 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,3,7,8,9,10,11,12,13] := remove (a 15) 6 [0,1,2,3,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 15 ≠ 7 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,3,8,9,10,11,12,13] := remove (a 15) 7 [0,1,2,3,7,8,9,10,11,12,13] t2 b3
  have b4 : a 15 ≠ 12 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 12 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,3,8,9,10,11,13] := remove (a 15) 12 [0,1,2,3,8,9,10,11,12,13] t3 b4
  have b5 : a 15 ≠ 13 := exclude [0,1,4,5] (fun u v => edge r26 v u) (a 15) (a 7) 13 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,2,3,8,9,10,11] := remove (a 15) 13 [0,1,2,3,8,9,10,11,13] t4 b5
  have b6 : a 23 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,3,5,6,7,8,9] := remove (a 23) 4 [0,1,2,3,4,5,6,7,8,9] d23 b6
  have b7 : a 23 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,3,6,7,8,9] := remove (a 23) 5 [0,1,2,3,5,6,7,8,9] t6 b7
  have b8 : a 23 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,3,6,7,9] := remove (a 23) 8 [0,1,2,3,6,7,8,9] t7 b8
  have b9 : a 23 ≠ 9 := exclude [0,1,4,5] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,3,6,7] := remove (a 23) 9 [0,1,2,3,6,7,9] t8 b9
  have b10 : a 9 ≠ 4 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0,8,12] := remove (a 9) 4 [0,4,8,12] d9 b10
  have b11 : a 9 ≠ 12 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 12 d8 c28 (by decide +kernel)
  have t11 : a 9 ∈ [0,8] := remove (a 9) 12 [0,8,12] t10 b11
  have b12 : a 24 ≠ 1 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b12
  have b13 : a 24 ≠ 3 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 4 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 24) 4 [0,2,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 5 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2,6,7,8,9,10,11] := remove (a 24) 5 [0,2,5,6,7,8,9,10,11] t14 b15
  exact And.intro t5 (And.intro t9 (And.intro t11 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,6])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d9 : a 9 ∈ [0,8])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 24 ∈ [0,2] ∧ a 11 ∈ [0,8,12,13] := by
  have b0 : a 24 ≠ 6 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,7,8,9,10,11] := remove (a 24) 6 [0,2,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 7 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,8,9,10,11] := remove (a 24) 7 [0,2,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 8 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,9,10,11] := remove (a 24) 8 [0,2,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 9 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,2,10,11] := remove (a 24) 9 [0,2,9,10,11] t2 b3
  have b4 : a 24 ≠ 10 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,11] := remove (a 24) 10 [0,2,10,11] t3 b4
  have b5 : a 24 ≠ 11 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2] := remove (a 24) 11 [0,2,11] t4 b5
  have b6 : a 11 ≠ 1 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d11 b6
  have b7 : a 11 ≠ 2 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t6 b7
  have b8 : a 11 ≠ 3 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t7 b8
  have b9 : a 11 ≠ 4 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 4 d9 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 11) 4 [0,4,5,6,7,8,9,10,11,12,13] t8 b9
  have b10 : a 11 ≠ 5 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 5 d9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 11) 5 [0,5,6,7,8,9,10,11,12,13] t9 b10
  have b11 : a 11 ≠ 6 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 6 d9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,7,8,9,10,11,12,13] := remove (a 11) 6 [0,6,7,8,9,10,11,12,13] t10 b11
  have b12 : a 11 ≠ 7 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t12 : a 11 ∈ [0,8,9,10,11,12,13] := remove (a 11) 7 [0,7,8,9,10,11,12,13] t11 b12
  have b13 : a 11 ≠ 9 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 9 d9 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,8,10,11,12,13] := remove (a 11) 9 [0,8,9,10,11,12,13] t12 b13
  have b14 : a 11 ≠ 10 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 10 d9 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,8,11,12,13] := remove (a 11) 10 [0,8,10,11,12,13] t13 b14
  have b15 : a 11 ≠ 11 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 11 d9 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0,8,12,13] := remove (a 11) 11 [0,8,11,12,13] t14 b15
  exact And.intro t5 (t15)

theorem chunk7 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,8,12,13])
    (d9 : a 9 ∈ [0,8])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c32 : edge r32 (a 9) (a 11)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 11 ∈ [0,8] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0,5,6,7,8,9,10,11] := by
  have b0 : a 11 ≠ 12 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 12 d9 c32 (by decide +kernel)
  have t0 : a 11 ∈ [0,8,13] := remove (a 11) 12 [0,8,12,13] d11 b0
  have b1 : a 11 ≠ 13 := exclude [0,8] (fun u v => edge r32 v u) (a 11) (a 9) 13 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [0,8] := remove (a 11) 13 [0,8,13] t0 b1
  have b2 : a 10 ≠ 2 := exclude [0,8] (edge r35) (a 10) (a 11) 2 t1 c35 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t2 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9] d14 b3
  have b4 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 t2 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,3,4,5,6,7,8,9] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9] t3 b4
  have b5 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 t2 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,5,6,7,8,9] := remove (a 14) 3 [0,3,4,5,6,7,8,9] t4 b5
  have b6 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 t2 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,5,6,7,8,9] := remove (a 14) 4 [0,4,5,6,7,8,9] t5 b6
  have b7 : a 14 ≠ 5 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 5 t2 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,6,7,8,9] := remove (a 14) 5 [0,5,6,7,8,9] t6 b7
  have b8 : a 14 ≠ 6 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 6 t2 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,7,8,9] := remove (a 14) 6 [0,6,7,8,9] t7 b8
  have b9 : a 14 ≠ 7 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 7 t2 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,8,9] := remove (a 14) 7 [0,7,8,9] t8 b9
  have b10 : a 14 ≠ 8 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 8 t2 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,9] := remove (a 14) 8 [0,8,9] t9 b10
  have b11 : a 14 ≠ 9 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 9 t2 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 9 [0,9] t10 b11
  have b12 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t2 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b12
  have b13 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t2 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t2 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t2 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,5,6,7,8,9,10,11] := remove (a 26) 4 [0,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t11 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_208
