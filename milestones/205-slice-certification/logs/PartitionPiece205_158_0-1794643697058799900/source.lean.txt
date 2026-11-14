import PartitionData205_158
namespace PartitionCover205_158
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 4 ∈ [0] ∧ a 8 ∈ [0,4,5,6,7,8,9,10] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 4) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t0 b1
  have b2 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 4) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 4) 4 [0,4,5,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 4) 5 [0,5,6,7,8,9,10,11,12,13] t3 b4
  have b5 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,7,8,9,10,11,12,13] := remove (a 4) 6 [0,6,7,8,9,10,11,12,13] t4 b5
  have b6 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,8,9,10,11,12,13] := remove (a 4) 7 [0,7,8,9,10,11,12,13] t5 b6
  have b7 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,9,10,11,12,13] := remove (a 4) 8 [0,8,9,10,11,12,13] t6 b7
  have b8 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,10,11,12,13] := remove (a 4) 9 [0,9,10,11,12,13] t7 b8
  have b9 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,11,12,13] := remove (a 4) 10 [0,10,11,12,13] t8 b9
  have b10 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,12,13] := remove (a 4) 11 [0,11,12,13] t9 b10
  have b11 : a 4 ≠ 12 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 12 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,13] := remove (a 4) 12 [0,12,13] t10 b11
  have b12 : a 4 ≠ 13 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 13 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0] := remove (a 4) 13 [0,13] t11 b12
  have b13 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10] d8 b13
  have b14 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,3,4,5,6,7,8,9,10] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10] t13 b14
  have b15 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,4,5,6,7,8,9,10] := remove (a 8) 3 [0,3,4,5,6,7,8,9,10] t14 b15
  exact And.intro t12 (t15)

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,4,5,6,7,8,9,10])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d1 : a 1 ∈ [0])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 8 ∈ [0,4] ∧ a 5 ∈ [0,8,12,13] := by
  have b0 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,4,6,7,8,9,10] := remove (a 8) 5 [0,4,5,6,7,8,9,10] d8 b0
  have b1 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,4,7,8,9,10] := remove (a 8) 6 [0,4,6,7,8,9,10] t0 b1
  have b2 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,4,8,9,10] := remove (a 8) 7 [0,4,7,8,9,10] t1 b2
  have b3 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,4,9,10] := remove (a 8) 8 [0,4,8,9,10] t2 b3
  have b4 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,4,10] := remove (a 8) 9 [0,4,9,10] t3 b4
  have b5 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,4] := remove (a 8) 10 [0,4,10] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 1 d1 c5 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d5 b6
  have b7 : a 5 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 2 d1 c5 (by decide +kernel)
  have t7 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t6 b7
  have b8 : a 5 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t8 : a 5 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 5) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t7 b8
  have b9 : a 5 ≠ 4 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 4 d1 c5 (by decide +kernel)
  have t9 : a 5 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 5) 4 [0,4,5,6,7,8,9,10,11,12,13] t8 b9
  have b10 : a 5 ≠ 5 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 5 d1 c5 (by decide +kernel)
  have t10 : a 5 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 5) 5 [0,5,6,7,8,9,10,11,12,13] t9 b10
  have b11 : a 5 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 6 d1 c5 (by decide +kernel)
  have t11 : a 5 ∈ [0,7,8,9,10,11,12,13] := remove (a 5) 6 [0,6,7,8,9,10,11,12,13] t10 b11
  have b12 : a 5 ≠ 7 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 7 d1 c5 (by decide +kernel)
  have t12 : a 5 ∈ [0,8,9,10,11,12,13] := remove (a 5) 7 [0,7,8,9,10,11,12,13] t11 b12
  have b13 : a 5 ≠ 9 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 9 d1 c5 (by decide +kernel)
  have t13 : a 5 ∈ [0,8,10,11,12,13] := remove (a 5) 9 [0,8,9,10,11,12,13] t12 b13
  have b14 : a 5 ≠ 10 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 10 d1 c5 (by decide +kernel)
  have t14 : a 5 ∈ [0,8,11,12,13] := remove (a 5) 10 [0,8,10,11,12,13] t13 b14
  have b15 : a 5 ≠ 11 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 11 d1 c5 (by decide +kernel)
  have t15 : a 5 ∈ [0,8,12,13] := remove (a 5) 11 [0,8,11,12,13] t14 b15
  exact And.intro t5 (t15)

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,8,12,13])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    : a 5 ∈ [0,8] ∧ a 9 ∈ [0,1] := by
  have b0 : a 5 ≠ 12 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 12 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0,8,13] := remove (a 5) 12 [0,8,12,13] d5 b0
  have b1 : a 5 ≠ 13 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 13 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,8] := remove (a 5) 13 [0,8,13] t0 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d9 b2
  have b3 : a 9 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t3 : a 9 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15] t2 b3
  have b4 : a 9 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 4 d1 c6 (by decide +kernel)
  have t4 : a 9 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15] := remove (a 9) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15] t3 b4
  have b5 : a 9 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 5 d1 c6 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,6,7,8,9,10,11,12,13,14,15] := remove (a 9) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15] t4 b5
  have b6 : a 9 ≠ 6 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 6 d1 c6 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,7,8,9,10,11,12,13,14,15] := remove (a 9) 6 [0,1,6,7,8,9,10,11,12,13,14,15] t5 b6
  have b7 : a 9 ≠ 7 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 7 d1 c6 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,8,9,10,11,12,13,14,15] := remove (a 9) 7 [0,1,7,8,9,10,11,12,13,14,15] t6 b7
  have b8 : a 9 ≠ 8 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 8 d1 c6 (by decide +kernel)
  have t8 : a 9 ∈ [0,1,9,10,11,12,13,14,15] := remove (a 9) 8 [0,1,8,9,10,11,12,13,14,15] t7 b8
  have b9 : a 9 ≠ 9 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 9 d1 c6 (by decide +kernel)
  have t9 : a 9 ∈ [0,1,10,11,12,13,14,15] := remove (a 9) 9 [0,1,9,10,11,12,13,14,15] t8 b9
  have b10 : a 9 ≠ 10 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 10 d1 c6 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,11,12,13,14,15] := remove (a 9) 10 [0,1,10,11,12,13,14,15] t9 b10
  have b11 : a 9 ≠ 11 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 11 d1 c6 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,12,13,14,15] := remove (a 9) 11 [0,1,11,12,13,14,15] t10 b11
  have b12 : a 9 ≠ 12 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 12 d1 c6 (by decide +kernel)
  have t12 : a 9 ∈ [0,1,13,14,15] := remove (a 9) 12 [0,1,12,13,14,15] t11 b12
  have b13 : a 9 ≠ 13 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 13 d1 c6 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,14,15] := remove (a 9) 13 [0,1,13,14,15] t12 b13
  have b14 : a 9 ≠ 14 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 14 d1 c6 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,15] := remove (a 9) 14 [0,1,14,15] t13 b14
  have b15 : a 9 ≠ 15 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 15 d1 c6 (by decide +kernel)
  have t15 : a 9 ∈ [0,1] := remove (a 9) 15 [0,1,15] t14 b15
  exact And.intro t1 (t15)

theorem chunk3 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0,1,2,3,5,6,7,8,9,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0,1] (edge r7) (a 2) (a 3) 1 d3 c7 (by decide +kernel)
  have t0 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0,1] (edge r7) (a 2) (a 3) 2 d3 c7 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t0 b1
  have b2 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 t1 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d6 b2
  have b3 : a 6 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 2 t1 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 6) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 6 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 3 t1 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 6) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t3 b4
  have b5 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 t1 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 6) 4 [0,4,5,6,7,8,9,10,11,12,13] t4 b5
  have b6 : a 6 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 5 t1 c8 (by decide +kernel)
  have t6 : a 6 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 6) 5 [0,5,6,7,8,9,10,11,12,13] t5 b6
  have b7 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 t1 c8 (by decide +kernel)
  have t7 : a 6 ∈ [0,7,8,9,10,11,12,13] := remove (a 6) 6 [0,6,7,8,9,10,11,12,13] t6 b7
  have b8 : a 6 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 7 t1 c8 (by decide +kernel)
  have t8 : a 6 ∈ [0,8,9,10,11,12,13] := remove (a 6) 7 [0,7,8,9,10,11,12,13] t7 b8
  have b9 : a 6 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 8 t1 c8 (by decide +kernel)
  have t9 : a 6 ∈ [0,9,10,11,12,13] := remove (a 6) 8 [0,8,9,10,11,12,13] t8 b9
  have b10 : a 6 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 9 t1 c8 (by decide +kernel)
  have t10 : a 6 ∈ [0,10,11,12,13] := remove (a 6) 9 [0,9,10,11,12,13] t9 b10
  have b11 : a 6 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 10 t1 c8 (by decide +kernel)
  have t11 : a 6 ∈ [0,11,12,13] := remove (a 6) 10 [0,10,11,12,13] t10 b11
  have b12 : a 6 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 11 t1 c8 (by decide +kernel)
  have t12 : a 6 ∈ [0,12,13] := remove (a 6) 11 [0,11,12,13] t11 b12
  have b13 : a 6 ≠ 12 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 12 t1 c8 (by decide +kernel)
  have t13 : a 6 ∈ [0,13] := remove (a 6) 12 [0,12,13] t12 b13
  have b14 : a 6 ≠ 13 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 13 t1 c8 (by decide +kernel)
  have t14 : a 6 ∈ [0] := remove (a 6) 13 [0,13] t13 b14
  have b15 : a 10 ≠ 4 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 4 t1 c9 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 10) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b15
  exact And.intro t1 (And.intro t14 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_158
