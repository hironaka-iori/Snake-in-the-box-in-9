import PartitionData205_186
namespace PartitionCover205_186
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (d1 : a 1 ∈ [0,1,2])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 2 ∈ [0,11] ∧ a 16 ∈ [0,2] ∧ a 5 ∈ [0,1,3,4,5,6,7] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,5,6,7,8,9,10,11] := remove (a 2) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,6,7,8,9,10,11] := remove (a 2) 5 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 2 ≠ 6 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 6 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,7,8,9,10,11] := remove (a 2) 6 [0,6,7,8,9,10,11] t4 b5
  have b6 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t6 : a 2 ∈ [0,8,9,10,11] := remove (a 2) 7 [0,7,8,9,10,11] t5 b6
  have b7 : a 2 ≠ 8 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 8 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,9,10,11] := remove (a 2) 8 [0,8,9,10,11] t6 b7
  have b8 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,10,11] := remove (a 2) 9 [0,9,10,11] t7 b8
  have b9 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,11] := remove (a 2) 10 [0,10,11] t8 b9
  have b10 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,2,3,4,5,6] := remove (a 16) 1 [0,1,2,3,4,5,6] d16 b10
  have b11 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,2,4,5,6] := remove (a 16) 3 [0,2,3,4,5,6] t10 b11
  have b12 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,2,5,6] := remove (a 16) 4 [0,2,4,5,6] t11 b12
  have b13 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,2,6] := remove (a 16) 5 [0,2,5,6] t12 b13
  have b14 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,2] := remove (a 16) 6 [0,2,6] t13 b14
  have b15 : a 5 ≠ 2 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,3,4,5,6,7] := remove (a 5) 2 [0,1,2,3,4,5,6,7] d5 b15
  exact And.intro t9 (And.intro t14 (t15))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,3,4,5,6,7])
    (d1 : a 1 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d2 : a 2 ∈ [0,11])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    : a 5 ∈ [0,1,4,5] ∧ a 1 ∈ [0,1] ∧ a 9 ∈ [0,3] ∧ a 17 ∈ [0,1,3,5,6] ∧ a 3 ∈ [0,5,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 5 ≠ 3 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,4,5,6,7] := remove (a 5) 3 [0,1,3,4,5,6,7] d5 b0
  have b1 : a 5 ≠ 6 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,4,5,7] := remove (a 5) 6 [0,1,4,5,6,7] t0 b1
  have b2 : a 5 ≠ 7 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,4,5] := remove (a 5) 7 [0,1,4,5,7] t1 b2
  have b3 : a 1 ≠ 2 := exclude [0,1,2,3] (edge r7) (a 1) (a 9) 2 d9 c7 (by decide +kernel)
  have t3 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b3
  have b4 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 t3 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 t3 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,3] := remove (a 9) 2 [0,2,3] t4 b5
  have b6 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 2 t3 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,3,4,5,6,7] := remove (a 17) 2 [0,1,2,3,4,5,6,7] d17 b6
  have b7 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 4 t3 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,3,5,6,7] := remove (a 17) 4 [0,1,3,4,5,6,7] t6 b7
  have b8 : a 17 ≠ 7 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 7 t3 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,3,5,6] := remove (a 17) 7 [0,1,3,5,6,7] t7 b8
  have b9 : a 3 ≠ 1 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t9 : a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d3 b9
  have b10 : a 3 ≠ 2 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t10 : a 3 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 3 ≠ 3 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t11 : a 3 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 3 ≠ 4 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t12 : a 3 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 3 ≠ 6 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 6 d2 c9 (by decide +kernel)
  have t13 : a 3 ∈ [0,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 6 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 3 ≠ 7 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 7 d2 c9 (by decide +kernel)
  have t14 : a 3 ∈ [0,5,8,9,10,11,12,13,14,15,16,17] := remove (a 3) 7 [0,5,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 3 ≠ 8 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 8 d2 c9 (by decide +kernel)
  have t15 : a 3 ∈ [0,5,9,10,11,12,13,14,15,16,17] := remove (a 3) 8 [0,5,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t5 (And.intro t8 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,5,9,10,11,12,13,14,15,16,17])
    (d2 : a 2 ∈ [0,11])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 3 ∈ [0,5,13,15] ∧ a 6 ∈ [0,3,6,9,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 3 ≠ 9 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 9 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0,5,10,11,12,13,14,15,16,17] := remove (a 3) 9 [0,5,9,10,11,12,13,14,15,16,17] d3 b0
  have b1 : a 3 ≠ 10 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 10 d2 c9 (by decide +kernel)
  have t1 : a 3 ∈ [0,5,11,12,13,14,15,16,17] := remove (a 3) 10 [0,5,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 3 ≠ 11 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 11 d2 c9 (by decide +kernel)
  have t2 : a 3 ∈ [0,5,12,13,14,15,16,17] := remove (a 3) 11 [0,5,11,12,13,14,15,16,17] t1 b2
  have b3 : a 3 ≠ 12 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 12 d2 c9 (by decide +kernel)
  have t3 : a 3 ∈ [0,5,13,14,15,16,17] := remove (a 3) 12 [0,5,12,13,14,15,16,17] t2 b3
  have b4 : a 3 ≠ 14 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 14 d2 c9 (by decide +kernel)
  have t4 : a 3 ∈ [0,5,13,15,16,17] := remove (a 3) 14 [0,5,13,14,15,16,17] t3 b4
  have b5 : a 3 ≠ 16 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 16 d2 c9 (by decide +kernel)
  have t5 : a 3 ∈ [0,5,13,15,17] := remove (a 3) 16 [0,5,13,15,16,17] t4 b5
  have b6 : a 3 ≠ 17 := exclude [0,11] (fun u v => edge r9 v u) (a 3) (a 2) 17 d2 c9 (by decide +kernel)
  have t6 : a 3 ∈ [0,5,13,15] := remove (a 3) 17 [0,5,13,15,17] t5 b6
  have b7 : a 6 ≠ 1 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b7
  have b8 : a 6 ≠ 2 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 6 ≠ 4 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 5 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 6 ≠ 7 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 7 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 6 ≠ 8 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 8 [0,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 6 ≠ 10 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 10 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,3,6,9,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 10 [0,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 6 ≠ 11 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 11 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,3,6,9,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 11 [0,3,6,9,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 6 ≠ 12 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 12 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,3,6,9,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 12 [0,3,6,9,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t6 (t15)

theorem chunk3 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,3,6,9,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,11])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 6 ∈ [0,3,6,9,19,20] ∧ a 10 ∈ [0,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 6 ≠ 13 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 13 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,3,6,9,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 13 [0,3,6,9,13,14,15,16,17,18,19,20,21,22,23] d6 b0
  have b1 : a 6 ≠ 14 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 14 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,3,6,9,15,16,17,18,19,20,21,22,23] := remove (a 6) 14 [0,3,6,9,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 6 ≠ 15 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 15 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,3,6,9,16,17,18,19,20,21,22,23] := remove (a 6) 15 [0,3,6,9,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 6 ≠ 16 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 16 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,3,6,9,17,18,19,20,21,22,23] := remove (a 6) 16 [0,3,6,9,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 6 ≠ 17 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 17 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,3,6,9,18,19,20,21,22,23] := remove (a 6) 17 [0,3,6,9,17,18,19,20,21,22,23] t3 b4
  have b5 : a 6 ≠ 18 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 18 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,3,6,9,19,20,21,22,23] := remove (a 6) 18 [0,3,6,9,18,19,20,21,22,23] t4 b5
  have b6 : a 6 ≠ 21 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 21 d2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,3,6,9,19,20,22,23] := remove (a 6) 21 [0,3,6,9,19,20,21,22,23] t5 b6
  have b7 : a 6 ≠ 22 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 22 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,3,6,9,19,20,23] := remove (a 6) 22 [0,3,6,9,19,20,22,23] t6 b7
  have b8 : a 6 ≠ 23 := exclude [0,11] (fun u v => edge r10 v u) (a 6) (a 2) 23 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,3,6,9,19,20] := remove (a 6) 23 [0,3,6,9,19,20,23] t7 b8
  have b9 : a 10 ≠ 1 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b9
  have b10 : a 10 ≠ 2 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 10 ≠ 4 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 10 ≠ 5 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 10 ≠ 7 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 7 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 10 ≠ 8 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 9 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_186
