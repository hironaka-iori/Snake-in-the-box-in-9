import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (c1 : edge r1 (a 0) (a 2)=true)
    : a 2 ∈ [0,8,18,19,20,21,22,23] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 2 ≠ 6 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 6 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t6 : a 2 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 2 ≠ 11 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 11 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 2 ≠ 12 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 12 d0 c1 (by decide +kernel)
  have t10 : a 2 ∈ [0,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 12 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 2 ≠ 13 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 13 d0 c1 (by decide +kernel)
  have t11 : a 2 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 13 [0,8,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 2 ≠ 14 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 14 d0 c1 (by decide +kernel)
  have t12 : a 2 ∈ [0,8,15,16,17,18,19,20,21,22,23] := remove (a 2) 14 [0,8,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 2 ≠ 15 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 15 d0 c1 (by decide +kernel)
  have t13 : a 2 ∈ [0,8,16,17,18,19,20,21,22,23] := remove (a 2) 15 [0,8,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 2 ≠ 16 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 16 d0 c1 (by decide +kernel)
  have t14 : a 2 ∈ [0,8,17,18,19,20,21,22,23] := remove (a 2) 16 [0,8,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 2 ≠ 17 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 17 d0 c1 (by decide +kernel)
  have t15 : a 2 ∈ [0,8,18,19,20,21,22,23] := remove (a 2) 17 [0,8,17,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk1 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,8,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d1 : a 1 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 2 ∈ [0,8] ∧ a 4 ∈ [0,1,9,10] ∧ a 5 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 2 ≠ 18 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 18 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,8,19,20,21,22,23] := remove (a 2) 18 [0,8,18,19,20,21,22,23] d2 b0
  have b1 : a 2 ≠ 19 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 19 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,8,20,21,22,23] := remove (a 2) 19 [0,8,19,20,21,22,23] t0 b1
  have b2 : a 2 ≠ 20 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 20 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,8,21,22,23] := remove (a 2) 20 [0,8,20,21,22,23] t1 b2
  have b3 : a 2 ≠ 21 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 21 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,8,22,23] := remove (a 2) 21 [0,8,21,22,23] t2 b3
  have b4 : a 2 ≠ 22 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 22 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,8,23] := remove (a 2) 22 [0,8,22,23] t3 b4
  have b5 : a 2 ≠ 23 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 23 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,8] := remove (a 2) 23 [0,8,23] t4 b5
  have b6 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 4) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d4 b6
  have b7 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 4) 3 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 4) 4 [0,1,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,1,6,7,8,9,10,11] := remove (a 4) 5 [0,1,5,6,7,8,9,10,11] t8 b9
  have b10 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,1,7,8,9,10,11] := remove (a 4) 6 [0,1,6,7,8,9,10,11] t9 b10
  have b11 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,1,8,9,10,11] := remove (a 4) 7 [0,1,7,8,9,10,11] t10 b11
  have b12 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,1,9,10,11] := remove (a 4) 8 [0,1,8,9,10,11] t11 b12
  have b13 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,9,10] := remove (a 4) 11 [0,1,9,10,11] t12 b13
  have b14 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d5 b14
  have b15 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t5 (And.intro t13 (t15))

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,8])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    : a 5 ∈ [0,4,8,10,11,19,20,22] ∧ a 9 ∈ [0,2] ∧ a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d5 b0
  have b1 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 5 ≠ 9 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 9 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 9 [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 5 ≠ 12 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 12 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,4,8,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 12 [0,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 5 ≠ 13 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 13 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,4,8,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 13 [0,4,8,10,11,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 5 ≠ 14 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 14 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,4,8,10,11,15,16,17,18,19,20,21,22,23] := remove (a 5) 14 [0,4,8,10,11,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 5 ≠ 15 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 15 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,4,8,10,11,16,17,18,19,20,21,22,23] := remove (a 5) 15 [0,4,8,10,11,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 5 ≠ 16 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 16 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,4,8,10,11,17,18,19,20,21,22,23] := remove (a 5) 16 [0,4,8,10,11,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 5 ≠ 17 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 17 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,4,8,10,11,18,19,20,21,22,23] := remove (a 5) 17 [0,4,8,10,11,17,18,19,20,21,22,23] t9 b10
  have b11 : a 5 ≠ 18 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 18 d1 c6 (by decide +kernel)
  have t11 : a 5 ∈ [0,4,8,10,11,19,20,21,22,23] := remove (a 5) 18 [0,4,8,10,11,18,19,20,21,22,23] t10 b11
  have b12 : a 5 ≠ 21 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 21 d1 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,4,8,10,11,19,20,22,23] := remove (a 5) 21 [0,4,8,10,11,19,20,21,22,23] t11 b12
  have b13 : a 5 ≠ 23 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 23 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,4,8,10,11,19,20,22] := remove (a 5) 23 [0,4,8,10,11,19,20,22,23] t12 b13
  have b14 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,2] := remove (a 9) 1 [0,1,2] d9 b14
  have b15 : a 3 ≠ 1 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t15 : a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 3) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d3 b15
  exact And.intro t13 (And.intro t14 (t15))

theorem chunk3 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 3 ∈ [0,5,6,11] ∧ a 6 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 3 ≠ 2 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 3) 2 [0,2,3,4,5,6,7,8,9,10,11] d3 b0
  have b1 : a 3 ≠ 3 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t1 : a 3 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 3) 3 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 3 ≠ 4 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t2 : a 3 ∈ [0,5,6,7,8,9,10,11] := remove (a 3) 4 [0,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 3 ≠ 7 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 7 d2 c9 (by decide +kernel)
  have t3 : a 3 ∈ [0,5,6,8,9,10,11] := remove (a 3) 7 [0,5,6,7,8,9,10,11] t2 b3
  have b4 : a 3 ≠ 8 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 8 d2 c9 (by decide +kernel)
  have t4 : a 3 ∈ [0,5,6,9,10,11] := remove (a 3) 8 [0,5,6,8,9,10,11] t3 b4
  have b5 : a 3 ≠ 9 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 9 d2 c9 (by decide +kernel)
  have t5 : a 3 ∈ [0,5,6,10,11] := remove (a 3) 9 [0,5,6,9,10,11] t4 b5
  have b6 : a 3 ≠ 10 := exclude [0,8] (fun u v => edge r9 v u) (a 3) (a 2) 10 d2 c9 (by decide +kernel)
  have t6 : a 3 ∈ [0,5,6,11] := remove (a 3) 10 [0,5,6,10,11] t5 b6
  have b7 : a 6 ≠ 1 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b7
  have b8 : a 6 ≠ 2 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 6 ≠ 3 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 4 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 6 ≠ 5 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 6 ≠ 6 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 6 ≠ 7 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 6 ≠ 9 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 9 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 6 ≠ 10 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 10 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t6 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_187
