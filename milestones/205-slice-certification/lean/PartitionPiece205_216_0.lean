import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    : a 2 ∈ [0,1,2] ∧ a 4 ∈ [0,1,4,5,13,17,21,22,23] := by
  have b0 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,2] := remove (a 2) 3 [0,1,2,3] d2 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d4 b1
  have b2 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 4 ≠ 12 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 12 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 4) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 4 ≠ 14 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 14 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,1,4,5,13,15,16,17,18,19,20,21,22,23] := remove (a 4) 14 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 4 ≠ 15 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 15 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,1,4,5,13,16,17,18,19,20,21,22,23] := remove (a 4) 15 [0,1,4,5,13,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 4 ≠ 16 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 16 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,1,4,5,13,17,18,19,20,21,22,23] := remove (a 4) 16 [0,1,4,5,13,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 4 ≠ 18 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 18 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,4,5,13,17,19,20,21,22,23] := remove (a 4) 18 [0,1,4,5,13,17,18,19,20,21,22,23] t12 b13
  have b14 : a 4 ≠ 19 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 19 d0 c2 (by decide +kernel)
  have t14 : a 4 ∈ [0,1,4,5,13,17,20,21,22,23] := remove (a 4) 19 [0,1,4,5,13,17,19,20,21,22,23] t13 b14
  have b15 : a 4 ≠ 20 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 20 d0 c2 (by decide +kernel)
  have t15 : a 4 ∈ [0,1,4,5,13,17,21,22,23] := remove (a 4) 20 [0,1,4,5,13,17,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

theorem chunk1 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,4,5,13,17,21,22,23])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 4 ∈ [0,1,4,5,13,17,21,23] ∧ a 8 ∈ [0,1,3,5,7] ∧ a 16 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 4 ≠ 22 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 22 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,4,5,13,17,21,23] := remove (a 4) 22 [0,1,4,5,13,17,21,22,23] d4 b0
  have b1 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d8 b1
  have b2 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 4 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,3,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 6 [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,3,5,7,9,10,11,12,13,14,15,16,17] := remove (a 8) 8 [0,1,3,5,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,3,5,7,10,11,12,13,14,15,16,17] := remove (a 8) 9 [0,1,3,5,7,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,3,5,7,11,12,13,14,15,16,17] := remove (a 8) 10 [0,1,3,5,7,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,3,5,7,12,13,14,15,16,17] := remove (a 8) 11 [0,1,3,5,7,11,12,13,14,15,16,17] t6 b7
  have b8 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,3,5,7,13,14,15,16,17] := remove (a 8) 12 [0,1,3,5,7,12,13,14,15,16,17] t7 b8
  have b9 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,1,3,5,7,14,15,16,17] := remove (a 8) 13 [0,1,3,5,7,13,14,15,16,17] t8 b9
  have b10 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,1,3,5,7,15,16,17] := remove (a 8) 14 [0,1,3,5,7,14,15,16,17] t9 b10
  have b11 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,1,3,5,7,16,17] := remove (a 8) 15 [0,1,3,5,7,15,16,17] t10 b11
  have b12 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,1,3,5,7,17] := remove (a 8) 16 [0,1,3,5,7,16,17] t11 b12
  have b13 : a 8 ≠ 17 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 17 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,3,5,7] := remove (a 8) 17 [0,1,3,5,7,17] t12 b13
  have b14 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b14
  have b15 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t13 (t15))

theorem chunk2 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 16 ∈ [0,8,12,21,22,23] := by
  have b0 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b0
  have b1 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 16 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 7 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 16 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 13 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,8,12,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 13 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,8,12,15,16,17,18,19,20,21,22,23] := remove (a 16) 14 [0,8,12,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,8,12,16,17,18,19,20,21,22,23] := remove (a 16) 15 [0,8,12,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,8,12,17,18,19,20,21,22,23] := remove (a 16) 16 [0,8,12,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,8,12,18,19,20,21,22,23] := remove (a 16) 17 [0,8,12,17,18,19,20,21,22,23] t11 b12
  have b13 : a 16 ≠ 18 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 18 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,8,12,19,20,21,22,23] := remove (a 16) 18 [0,8,12,18,19,20,21,22,23] t12 b13
  have b14 : a 16 ≠ 19 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 19 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,8,12,20,21,22,23] := remove (a 16) 19 [0,8,12,19,20,21,22,23] t13 b14
  have b15 : a 16 ≠ 20 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 20 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,8,12,21,22,23] := remove (a 16) 20 [0,8,12,20,21,22,23] t14 b15
  exact t15

theorem chunk3 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,8,12,21,22,23])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0,1,2])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 16 ∈ [0,8,12,22] ∧ a 5 ∈ [0,6,12,17] := by
  have b0 : a 16 ≠ 21 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 21 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,8,12,22,23] := remove (a 16) 21 [0,8,12,21,22,23] d16 b0
  have b1 : a 16 ≠ 23 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 23 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,8,12,22] := remove (a 16) 23 [0,8,12,22,23] t0 b1
  have b2 : a 5 ≠ 1 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d5 b2
  have b3 : a 5 ≠ 2 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 5 ≠ 3 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 5 ≠ 4 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 5 ≠ 5 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 5 ≠ 7 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 5 ≠ 8 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 5) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 5 ≠ 9 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 9 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 5) 9 [0,6,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 5 ≠ 10 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 5) 10 [0,6,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 5 ≠ 11 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 11 d1 c6 (by decide +kernel)
  have t11 : a 5 ∈ [0,6,12,13,14,15,16,17] := remove (a 5) 11 [0,6,11,12,13,14,15,16,17] t10 b11
  have b12 : a 5 ≠ 13 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 13 d1 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,6,12,14,15,16,17] := remove (a 5) 13 [0,6,12,13,14,15,16,17] t11 b12
  have b13 : a 5 ≠ 14 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 14 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,6,12,15,16,17] := remove (a 5) 14 [0,6,12,14,15,16,17] t12 b13
  have b14 : a 5 ≠ 15 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 15 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,6,12,16,17] := remove (a 5) 15 [0,6,12,15,16,17] t13 b14
  have b15 : a 5 ≠ 16 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 16 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,6,12,17] := remove (a 5) 16 [0,6,12,16,17] t14 b15
  exact And.intro t1 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_216
