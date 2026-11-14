import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    : a 2 ∈ [0,2] ∧ a 4 ∈ [0,6,14,15,16,17] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2,4,5] := remove (a 2) 3 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,2,5] := remove (a 2) 4 [0,2,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,2] := remove (a 2) 5 [0,2,5] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d4 b4
  have b5 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 4) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 4) 9 [0,6,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 4) 10 [0,6,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,6,12,13,14,15,16,17] := remove (a 4) 11 [0,6,11,12,13,14,15,16,17] t12 b13
  have b14 : a 4 ≠ 12 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 12 d0 c2 (by decide +kernel)
  have t14 : a 4 ∈ [0,6,13,14,15,16,17] := remove (a 4) 12 [0,6,12,13,14,15,16,17] t13 b14
  have b15 : a 4 ≠ 13 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 13 d0 c2 (by decide +kernel)
  have t15 : a 4 ∈ [0,6,14,15,16,17] := remove (a 4) 13 [0,6,13,14,15,16,17] t14 b15
  exact And.intro t3 (t15)

theorem chunk1 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,6,14,15,16,17])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 4 ∈ [0,6] ∧ a 8 ∈ [0,4,5,6,10,11] := by
  have b0 : a 4 ≠ 14 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 14 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,6,15,16,17] := remove (a 4) 14 [0,6,14,15,16,17] d4 b0
  have b1 : a 4 ≠ 15 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 15 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,6,16,17] := remove (a 4) 15 [0,6,15,16,17] t0 b1
  have b2 : a 4 ≠ 16 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 16 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,6,17] := remove (a 4) 16 [0,6,16,17] t1 b2
  have b3 : a 4 ≠ 17 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 17 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,6] := remove (a 4) 17 [0,6,17] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,4,5,6,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 7 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,4,5,6,9,10,11,12,13,14,15,16,17] := remove (a 8) 8 [0,4,5,6,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,4,5,6,10,11,12,13,14,15,16,17] := remove (a 8) 9 [0,4,5,6,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,4,5,6,10,11,13,14,15,16,17] := remove (a 8) 12 [0,4,5,6,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,4,5,6,10,11,14,15,16,17] := remove (a 8) 13 [0,4,5,6,10,11,13,14,15,16,17] t10 b11
  have b12 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,4,5,6,10,11,15,16,17] := remove (a 8) 14 [0,4,5,6,10,11,14,15,16,17] t11 b12
  have b13 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,4,5,6,10,11,16,17] := remove (a 8) 15 [0,4,5,6,10,11,15,16,17] t12 b13
  have b14 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,4,5,6,10,11,17] := remove (a 8) 16 [0,4,5,6,10,11,16,17] t13 b14
  have b15 : a 8 ≠ 17 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 17 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,4,5,6,10,11] := remove (a 8) 17 [0,4,5,6,10,11,17] t14 b15
  exact And.intro t3 (t15)

theorem chunk2 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d0 : a 0 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (d1 : a 1 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 16 ∈ [0,1,6,7,8,9,12,13,15,17] ∧ a 17 ∈ [0,3,4,6,7,8] ∧ a 3 ∈ [0,1] ∧ a 6 ∈ [0,1,4,7,8] := by
  have b0 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b0
  have b1 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,6,7,8,9,11,12,13,14,15,16,17] := remove (a 16) 10 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,6,7,8,9,12,13,14,15,16,17] := remove (a 16) 11 [0,1,6,7,8,9,11,12,13,14,15,16,17] t4 b5
  have b6 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,6,7,8,9,12,13,15,16,17] := remove (a 16) 14 [0,1,6,7,8,9,12,13,14,15,16,17] t5 b6
  have b7 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,6,7,8,9,12,13,15,17] := remove (a 16) 16 [0,1,6,7,8,9,12,13,15,16,17] t6 b7
  have b8 : a 17 ≠ 1 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,2,3,4,5,6,7,8] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8] d17 b8
  have b9 : a 17 ≠ 2 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,4,5,6,7,8] := remove (a 17) 2 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,3,4,6,7,8] := remove (a 17) 5 [0,3,4,5,6,7,8] t9 b10
  have b11 : a 3 ≠ 2 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t11 : a 3 ∈ [0,1] := remove (a 3) 2 [0,1,2] d3 b11
  have b12 : a 6 ≠ 2 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,3,4,5,6,7,8] := remove (a 6) 2 [0,1,2,3,4,5,6,7,8] d6 b12
  have b13 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,4,5,6,7,8] := remove (a 6) 3 [0,1,3,4,5,6,7,8] t12 b13
  have b14 : a 6 ≠ 5 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,4,6,7,8] := remove (a 6) 5 [0,1,4,5,6,7,8] t13 b14
  have b15 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,4,7,8] := remove (a 6) 6 [0,1,4,6,7,8] t14 b15
  exact And.intro t7 (And.intro t10 (And.intro t11 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,4,7,8])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 6 ∈ [0,1,4] ∧ a 10 ∈ [0,1,4,5] ∧ a 18 ∈ [0,1,4,5,10,11] := by
  have b0 : a 6 ≠ 7 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,4,8] := remove (a 6) 7 [0,1,4,7,8] d6 b0
  have b1 : a 6 ≠ 8 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,4] := remove (a 6) 8 [0,1,4,8] t0 b1
  have b2 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b2
  have b3 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 10) 6 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,4,5,8,9,10,11] := remove (a 10) 7 [0,1,4,5,7,8,9,10,11] t4 b5
  have b6 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,4,5,9,10,11] := remove (a 10) 8 [0,1,4,5,8,9,10,11] t5 b6
  have b7 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5,10,11] := remove (a 10) 9 [0,1,4,5,9,10,11] t6 b7
  have b8 : a 10 ≠ 10 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5,11] := remove (a 10) 10 [0,1,4,5,10,11] t7 b8
  have b9 : a 10 ≠ 11 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,4,5] := remove (a 10) 11 [0,1,4,5,11] t8 b9
  have b10 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 18) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b10
  have b11 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,1,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 18) 6 [0,1,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,4,5,8,9,10,11] := remove (a 18) 7 [0,1,4,5,7,8,9,10,11] t12 b13
  have b14 : a 18 ≠ 8 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,4,5,9,10,11] := remove (a 18) 8 [0,1,4,5,8,9,10,11] t13 b14
  have b15 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,4,5,10,11] := remove (a 18) 9 [0,1,4,5,9,10,11] t14 b15
  exact And.intro t1 (And.intro t9 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_206
