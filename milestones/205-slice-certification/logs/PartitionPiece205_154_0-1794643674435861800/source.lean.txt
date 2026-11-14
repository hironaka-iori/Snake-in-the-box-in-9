import PartitionData205_154
namespace PartitionCover205_154
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 4 ∈ [0,2,4,6] ∧ a 8 ∈ [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7] := remove (a 4) 1 [0,1,2,3,4,5,6,7] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,4,5,6,7] := remove (a 4) 3 [0,2,3,4,5,6,7] t0 b1
  have b2 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,4,6,7] := remove (a 4) 5 [0,2,4,5,6,7] t1 b2
  have b3 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,4,6] := remove (a 4) 7 [0,2,4,6,7] t2 b3
  have b4 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t4 b5
  have b6 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t5 b6
  have b7 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t6 b7
  have b8 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t7 b8
  have b9 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t8 b9
  have b10 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 10 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t9 b10
  have b11 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 11 [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t10 b11
  have b12 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 12 [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t11 b12
  have b13 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 13 [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t12 b13
  have b14 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,1,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 14 [0,1,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t13 b14
  have b15 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 15 [0,1,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t14 b15
  exact And.intro t3 (t15)

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 8 ∈ [0,1,8,9,16,17,24,25] ∧ a 5 ∈ [0,5,6,7,8,9,10,11] := by
  have b0 : a 8 ≠ 18 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 18 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,8,9,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 18 [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] d8 b0
  have b1 : a 8 ≠ 19 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 19 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,8,9,16,17,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 19 [0,1,8,9,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31] t0 b1
  have b2 : a 8 ≠ 20 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 20 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 20 [0,1,8,9,16,17,20,21,22,23,24,25,26,27,28,29,30,31] t1 b2
  have b3 : a 8 ≠ 21 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 21 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,8,9,16,17,22,23,24,25,26,27,28,29,30,31] := remove (a 8) 21 [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31] t2 b3
  have b4 : a 8 ≠ 22 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 22 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,8,9,16,17,23,24,25,26,27,28,29,30,31] := remove (a 8) 22 [0,1,8,9,16,17,22,23,24,25,26,27,28,29,30,31] t3 b4
  have b5 : a 8 ≠ 23 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 23 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,8,9,16,17,24,25,26,27,28,29,30,31] := remove (a 8) 23 [0,1,8,9,16,17,23,24,25,26,27,28,29,30,31] t4 b5
  have b6 : a 8 ≠ 26 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 26 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,8,9,16,17,24,25,27,28,29,30,31] := remove (a 8) 26 [0,1,8,9,16,17,24,25,26,27,28,29,30,31] t5 b6
  have b7 : a 8 ≠ 27 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 27 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,8,9,16,17,24,25,28,29,30,31] := remove (a 8) 27 [0,1,8,9,16,17,24,25,27,28,29,30,31] t6 b7
  have b8 : a 8 ≠ 28 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 28 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,8,9,16,17,24,25,29,30,31] := remove (a 8) 28 [0,1,8,9,16,17,24,25,28,29,30,31] t7 b8
  have b9 : a 8 ≠ 29 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 29 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,1,8,9,16,17,24,25,30,31] := remove (a 8) 29 [0,1,8,9,16,17,24,25,29,30,31] t8 b9
  have b10 : a 8 ≠ 30 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 30 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,1,8,9,16,17,24,25,31] := remove (a 8) 30 [0,1,8,9,16,17,24,25,30,31] t9 b10
  have b11 : a 8 ≠ 31 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 31 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,1,8,9,16,17,24,25] := remove (a 8) 31 [0,1,8,9,16,17,24,25,31] t10 b11
  have b12 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 1 d1 c5 (by decide +kernel)
  have t12 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b12
  have b13 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 2 d1 c5 (by decide +kernel)
  have t13 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t14 : a 5 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 5) 3 [0,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 4 d1 c5 (by decide +kernel)
  have t15 : a 5 ∈ [0,5,6,7,8,9,10,11] := remove (a 5) 4 [0,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t11 (t15)

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (d2 : a 2 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    : a 5 ∈ [0,6] ∧ a 10 ∈ [0,3,8,11,14,15] := by
  have b0 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 5 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0,6,7,8,9,10,11] := remove (a 5) 5 [0,5,6,7,8,9,10,11] d5 b0
  have b1 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 7 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,6,8,9,10,11] := remove (a 5) 7 [0,6,7,8,9,10,11] t0 b1
  have b2 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 8 d1 c5 (by decide +kernel)
  have t2 : a 5 ∈ [0,6,9,10,11] := remove (a 5) 8 [0,6,8,9,10,11] t1 b2
  have b3 : a 5 ≠ 9 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 9 d1 c5 (by decide +kernel)
  have t3 : a 5 ∈ [0,6,10,11] := remove (a 5) 9 [0,6,9,10,11] t2 b3
  have b4 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 10 d1 c5 (by decide +kernel)
  have t4 : a 5 ∈ [0,6,11] := remove (a 5) 10 [0,6,10,11] t3 b4
  have b5 : a 5 ≠ 11 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 11 d1 c5 (by decide +kernel)
  have t5 : a 5 ∈ [0,6] := remove (a 5) 11 [0,6,11] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 1 d2 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d10 b6
  have b7 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 2 d2 c9 (by decide +kernel)
  have t7 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] t6 b7
  have b8 : a 10 ≠ 4 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 4 d2 c9 (by decide +kernel)
  have t8 : a 10 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 5 d2 c9 (by decide +kernel)
  have t9 : a 10 ∈ [0,3,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15] t8 b9
  have b10 : a 10 ≠ 6 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 6 d2 c9 (by decide +kernel)
  have t10 : a 10 ∈ [0,3,7,8,9,10,11,12,13,14,15] := remove (a 10) 6 [0,3,6,7,8,9,10,11,12,13,14,15] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 7 d2 c9 (by decide +kernel)
  have t11 : a 10 ∈ [0,3,8,9,10,11,12,13,14,15] := remove (a 10) 7 [0,3,7,8,9,10,11,12,13,14,15] t10 b11
  have b12 : a 10 ≠ 9 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 9 d2 c9 (by decide +kernel)
  have t12 : a 10 ∈ [0,3,8,10,11,12,13,14,15] := remove (a 10) 9 [0,3,8,9,10,11,12,13,14,15] t11 b12
  have b13 : a 10 ≠ 10 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 10 d2 c9 (by decide +kernel)
  have t13 : a 10 ∈ [0,3,8,11,12,13,14,15] := remove (a 10) 10 [0,3,8,10,11,12,13,14,15] t12 b13
  have b14 : a 10 ≠ 12 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 12 d2 c9 (by decide +kernel)
  have t14 : a 10 ∈ [0,3,8,11,13,14,15] := remove (a 10) 12 [0,3,8,11,12,13,14,15] t13 b14
  have b15 : a 10 ≠ 13 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 13 d2 c9 (by decide +kernel)
  have t15 : a 10 ∈ [0,3,8,11,14,15] := remove (a 10) 13 [0,3,8,11,13,14,15] t14 b15
  exact And.intro t5 (t15)

theorem chunk3 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3,8,11,14,15])
    (d2 : a 2 ∈ [0,1])
    (d4 : a 4 ∈ [0,2,4,6])
    (d5 : a 5 ∈ [0,6])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 10 ∈ [0,3,8,11] ∧ a 4 ∈ [0,4] ∧ a 6 ∈ [0,4] ∧ a 12 ∈ [0,4] := by
  have b0 : a 10 ≠ 14 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 14 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,3,8,11,15] := remove (a 10) 14 [0,3,8,11,14,15] d10 b0
  have b1 : a 10 ≠ 15 := exclude [0,1] (fun u v => edge r9 v u) (a 10) (a 2) 15 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,3,8,11] := remove (a 10) 15 [0,3,8,11,15] t0 b1
  have b2 : a 4 ≠ 2 := exclude [0,6] (edge r12) (a 4) (a 5) 2 d5 c12 (by decide +kernel)
  have t2 : a 4 ∈ [0,4,6] := remove (a 4) 2 [0,2,4,6] d4 b2
  have b3 : a 4 ≠ 6 := exclude [0,6] (edge r12) (a 4) (a 5) 6 d5 c12 (by decide +kernel)
  have t3 : a 4 ∈ [0,4] := remove (a 4) 6 [0,4,6] t2 b3
  have b4 : a 6 ≠ 1 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 1 t3 c13 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,3,4,5,6,7] := remove (a 6) 1 [0,1,2,3,4,5,6,7] d6 b4
  have b5 : a 6 ≠ 2 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 2 t3 c13 (by decide +kernel)
  have t5 : a 6 ∈ [0,3,4,5,6,7] := remove (a 6) 2 [0,2,3,4,5,6,7] t4 b5
  have b6 : a 6 ≠ 3 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 3 t3 c13 (by decide +kernel)
  have t6 : a 6 ∈ [0,4,5,6,7] := remove (a 6) 3 [0,3,4,5,6,7] t5 b6
  have b7 : a 6 ≠ 5 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 5 t3 c13 (by decide +kernel)
  have t7 : a 6 ∈ [0,4,6,7] := remove (a 6) 5 [0,4,5,6,7] t6 b7
  have b8 : a 6 ≠ 6 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 6 t3 c13 (by decide +kernel)
  have t8 : a 6 ∈ [0,4,7] := remove (a 6) 6 [0,4,6,7] t7 b8
  have b9 : a 6 ≠ 7 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 7 t3 c13 (by decide +kernel)
  have t9 : a 6 ∈ [0,4] := remove (a 6) 7 [0,4,7] t8 b9
  have b10 : a 12 ≠ 1 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 1 t3 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,3,4,5,6,7] := remove (a 12) 1 [0,1,2,3,4,5,6,7] d12 b10
  have b11 : a 12 ≠ 2 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 2 t3 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,3,4,5,6,7] := remove (a 12) 2 [0,2,3,4,5,6,7] t10 b11
  have b12 : a 12 ≠ 3 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 3 t3 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,4,5,6,7] := remove (a 12) 3 [0,3,4,5,6,7] t11 b12
  have b13 : a 12 ≠ 5 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 5 t3 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,4,6,7] := remove (a 12) 5 [0,4,5,6,7] t12 b13
  have b14 : a 12 ≠ 6 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 6 t3 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,4,7] := remove (a 12) 6 [0,4,6,7] t13 b14
  have b15 : a 12 ≠ 7 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 7 t3 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,4] := remove (a 12) 7 [0,4,7] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t9 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_154
