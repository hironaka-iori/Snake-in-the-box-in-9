import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (c1 : edge r1 (a 0) (a 2)=true)
    : a 2 ∈ [0,4,8,14,20,21,22,23] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 2 ≠ 6 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 6 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t6 : a 2 ∈ [0,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 9 [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,4,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 10 [0,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 2 ≠ 11 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 11 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,4,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 11 [0,4,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 2 ≠ 12 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 12 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,4,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 12 [0,4,8,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 2 ≠ 13 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 13 d0 c1 (by decide +kernel)
  have t10 : a 2 ∈ [0,4,8,14,15,16,17,18,19,20,21,22,23] := remove (a 2) 13 [0,4,8,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 2 ≠ 15 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 15 d0 c1 (by decide +kernel)
  have t11 : a 2 ∈ [0,4,8,14,16,17,18,19,20,21,22,23] := remove (a 2) 15 [0,4,8,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 2 ≠ 16 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 16 d0 c1 (by decide +kernel)
  have t12 : a 2 ∈ [0,4,8,14,17,18,19,20,21,22,23] := remove (a 2) 16 [0,4,8,14,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 2 ≠ 17 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 17 d0 c1 (by decide +kernel)
  have t13 : a 2 ∈ [0,4,8,14,18,19,20,21,22,23] := remove (a 2) 17 [0,4,8,14,17,18,19,20,21,22,23] t12 b13
  have b14 : a 2 ≠ 18 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 18 d0 c1 (by decide +kernel)
  have t14 : a 2 ∈ [0,4,8,14,19,20,21,22,23] := remove (a 2) 18 [0,4,8,14,18,19,20,21,22,23] t13 b14
  have b15 : a 2 ≠ 19 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 19 d0 c1 (by decide +kernel)
  have t15 : a 2 ∈ [0,4,8,14,20,21,22,23] := remove (a 2) 19 [0,4,8,14,19,20,21,22,23] t14 b15
  exact t15

theorem chunk1 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,4,8,14,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 2 ∈ [0,4,8,14] ∧ a 4 ∈ [0,1,3] ∧ a 8 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 2 ≠ 20 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 20 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,4,8,14,21,22,23] := remove (a 2) 20 [0,4,8,14,20,21,22,23] d2 b0
  have b1 : a 2 ≠ 21 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 21 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,4,8,14,22,23] := remove (a 2) 21 [0,4,8,14,21,22,23] t0 b1
  have b2 : a 2 ≠ 22 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 22 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,8,14,23] := remove (a 2) 22 [0,4,8,14,22,23] t1 b2
  have b3 : a 2 ≠ 23 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 23 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,4,8,14] := remove (a 2) 23 [0,4,8,14,23] t2 b3
  have b4 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d8 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t4 (t15))

theorem chunk2 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 8 ∈ [0,1,18,19] ∧ a 16 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 8) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] d8 b0
  have b1 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 8) 14 [0,1,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 8) 15 [0,1,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 8) 16 [0,1,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 8 ≠ 17 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 17 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,18,19,20,21,22,23] := remove (a 8) 17 [0,1,17,18,19,20,21,22,23] t3 b4
  have b5 : a 8 ≠ 20 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 20 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,18,19,21,22,23] := remove (a 8) 20 [0,1,18,19,20,21,22,23] t4 b5
  have b6 : a 8 ≠ 21 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 21 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,18,19,22,23] := remove (a 8) 21 [0,1,18,19,21,22,23] t5 b6
  have b7 : a 8 ≠ 22 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 22 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1,18,19,23] := remove (a 8) 22 [0,1,18,19,22,23] t6 b7
  have b8 : a 8 ≠ 23 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 23 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,1,18,19] := remove (a 8) 23 [0,1,18,19,23] t7 b8
  have b9 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b9
  have b10 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 10 [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (t15)

theorem chunk3 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8])
    (d1 : a 1 ∈ [0,1])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 16 ∈ [0,1,6,7] ∧ a 9 ∈ [0,4,5,6,7,8] := by
  have b0 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 11 [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b0
  have b1 : a 16 ≠ 12 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 12 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 12 [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 16 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 13 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,6,7,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 13 [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,6,7,15,16,17,18,19,20,21,22,23] := remove (a 16) 14 [0,1,6,7,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,6,7,16,17,18,19,20,21,22,23] := remove (a 16) 15 [0,1,6,7,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,6,7,17,18,19,20,21,22,23] := remove (a 16) 16 [0,1,6,7,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,6,7,18,19,20,21,22,23] := remove (a 16) 17 [0,1,6,7,17,18,19,20,21,22,23] t5 b6
  have b7 : a 16 ≠ 18 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 18 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,6,7,19,20,21,22,23] := remove (a 16) 18 [0,1,6,7,18,19,20,21,22,23] t6 b7
  have b8 : a 16 ≠ 19 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 19 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,6,7,20,21,22,23] := remove (a 16) 19 [0,1,6,7,19,20,21,22,23] t7 b8
  have b9 : a 16 ≠ 20 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 20 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,6,7,21,22,23] := remove (a 16) 20 [0,1,6,7,20,21,22,23] t8 b9
  have b10 : a 16 ≠ 21 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 21 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,6,7,22,23] := remove (a 16) 21 [0,1,6,7,21,22,23] t9 b10
  have b11 : a 16 ≠ 22 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 22 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,6,7,23] := remove (a 16) 22 [0,1,6,7,22,23] t10 b11
  have b12 : a 16 ≠ 23 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 23 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,6,7] := remove (a 16) 23 [0,1,6,7,23] t11 b12
  have b13 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,2,3,4,5,6,7,8] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8] d9 b13
  have b14 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,3,4,5,6,7,8] := remove (a 9) 2 [0,2,3,4,5,6,7,8] t13 b14
  have b15 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,4,5,6,7,8] := remove (a 9) 3 [0,3,4,5,6,7,8] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_212
