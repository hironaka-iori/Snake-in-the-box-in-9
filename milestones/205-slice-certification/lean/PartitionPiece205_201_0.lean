import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 2 ∈ [0,8] ∧ a 8 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := by
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
  have b7 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,8,10,11] := remove (a 2) 9 [0,8,9,10,11] t6 b7
  have b8 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,8,11] := remove (a 2) 10 [0,8,10,11] t7 b8
  have b9 : a 2 ≠ 11 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 11 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,8] := remove (a 2) 11 [0,8,11] t8 b9
  have b10 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d8 b10
  have b11 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t9 (t15)

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,7,8,9,10,11,12,13,14,15,16,17])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 8 ∈ [0,8] ∧ a 16 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 7 [0,7,8,9,10,11,12,13,14,15,16,17] d8 b0
  have b1 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,8,10,11,12,13,14,15,16,17] := remove (a 8) 9 [0,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,8,11,12,13,14,15,16,17] := remove (a 8) 10 [0,8,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,8,12,13,14,15,16,17] := remove (a 8) 11 [0,8,11,12,13,14,15,16,17] t2 b3
  have b4 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,8,13,14,15,16,17] := remove (a 8) 12 [0,8,12,13,14,15,16,17] t3 b4
  have b5 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,8,14,15,16,17] := remove (a 8) 13 [0,8,13,14,15,16,17] t4 b5
  have b6 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,8,15,16,17] := remove (a 8) 14 [0,8,14,15,16,17] t5 b6
  have b7 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,8,16,17] := remove (a 8) 15 [0,8,15,16,17] t6 b7
  have b8 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,8,17] := remove (a 8) 16 [0,8,16,17] t7 b8
  have b9 : a 8 ≠ 17 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 17 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,8] := remove (a 8) 17 [0,8,17] t8 b9
  have b10 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b10
  have b11 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t9 (t15)

theorem chunk2 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0,1,2])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 16 ∈ [0,8,12,16] ∧ a 5 ∈ [0,2,4,5] := by
  have b0 : a 16 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 7 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b0
  have b1 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 16 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 13 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,8,12,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 13 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,8,12,15,16,17,18,19,20,21,22,23] := remove (a 16) 14 [0,8,12,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,8,12,16,17,18,19,20,21,22,23] := remove (a 16) 15 [0,8,12,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,8,12,16,18,19,20,21,22,23] := remove (a 16) 17 [0,8,12,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 16 ≠ 18 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 18 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,8,12,16,19,20,21,22,23] := remove (a 16) 18 [0,8,12,16,18,19,20,21,22,23] t7 b8
  have b9 : a 16 ≠ 19 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 19 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,8,12,16,20,21,22,23] := remove (a 16) 19 [0,8,12,16,19,20,21,22,23] t8 b9
  have b10 : a 16 ≠ 20 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 20 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,8,12,16,21,22,23] := remove (a 16) 20 [0,8,12,16,20,21,22,23] t9 b10
  have b11 : a 16 ≠ 21 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 21 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,8,12,16,22,23] := remove (a 16) 21 [0,8,12,16,21,22,23] t10 b11
  have b12 : a 16 ≠ 22 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 22 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,8,12,16,23] := remove (a 16) 22 [0,8,12,16,22,23] t11 b12
  have b13 : a 16 ≠ 23 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 23 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,8,12,16] := remove (a 16) 23 [0,8,12,16,23] t12 b13
  have b14 : a 5 ≠ 1 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b14
  have b15 : a 5 ≠ 3 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,2,4,5] := remove (a 5) 3 [0,2,3,4,5] t14 b15
  exact And.intro t13 (t15)

theorem chunk3 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 17 ∈ [0,4,6,8,10,11] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,5] ∧ a 10 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 17 ≠ 1 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b0
  have b1 : a 17 ≠ 2 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 17) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 17 ≠ 3 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 17) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 17 ≠ 5 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,4,6,7,8,9,10,11] := remove (a 17) 5 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 17 ≠ 7 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,4,6,8,9,10,11] := remove (a 17) 7 [0,4,6,7,8,9,10,11] t3 b4
  have b5 : a 17 ≠ 9 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,4,6,8,10,11] := remove (a 17) 9 [0,4,6,8,9,10,11] t4 b5
  have b6 : a 3 ≠ 1 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t6 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b6
  have b7 : a 6 ≠ 1 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b7
  have b8 : a 6 ≠ 2 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,3,4,5] := remove (a 6) 2 [0,2,3,4,5] t7 b8
  have b9 : a 6 ≠ 3 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,4,5] := remove (a 6) 3 [0,3,4,5] t8 b9
  have b10 : a 6 ≠ 4 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,5] := remove (a 6) 4 [0,4,5] t9 b10
  have b11 : a 10 ≠ 2 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b11
  have b12 : a 10 ≠ 3 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 10 ≠ 6 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 10 ≠ 7 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 8 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t5 (And.intro t6 (And.intro t10 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_201
