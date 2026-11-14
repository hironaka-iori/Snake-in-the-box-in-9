import PartitionData205_183
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    : a 2 ∈ [0,1] ∧ a 4 ∈ [0,2,3,5] ∧ a 15 ∈ [0,3,6,7,8] := by
  have b0 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,3,4,5] := remove (a 2) 2 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1,4,5] := remove (a 2) 3 [0,1,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,1,5] := remove (a 2) 4 [0,1,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,1] := remove (a 2) 5 [0,1,5] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d4 b4
  have b5 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 4) 4 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 4) 6 [0,2,3,5,6,7,8,9,10,11] t5 b6
  have b7 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,2,3,5,8,9,10,11] := remove (a 4) 7 [0,2,3,5,7,8,9,10,11] t6 b7
  have b8 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,2,3,5,9,10,11] := remove (a 4) 8 [0,2,3,5,8,9,10,11] t7 b8
  have b9 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,2,3,5,10,11] := remove (a 4) 9 [0,2,3,5,9,10,11] t8 b9
  have b10 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,2,3,5,11] := remove (a 4) 10 [0,2,3,5,10,11] t9 b10
  have b11 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,2,3,5] := remove (a 4) 11 [0,2,3,5,11] t10 b11
  have b12 : a 15 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 1 d0 c4 (by decide +kernel)
  have t12 : a 15 ∈ [0,2,3,4,5,6,7,8] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8] d15 b12
  have b13 : a 15 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 2 d0 c4 (by decide +kernel)
  have t13 : a 15 ∈ [0,3,4,5,6,7,8] := remove (a 15) 2 [0,2,3,4,5,6,7,8] t12 b13
  have b14 : a 15 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 4 d0 c4 (by decide +kernel)
  have t14 : a 15 ∈ [0,3,5,6,7,8] := remove (a 15) 4 [0,3,4,5,6,7,8] t13 b14
  have b15 : a 15 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 5 d0 c4 (by decide +kernel)
  have t15 : a 15 ∈ [0,3,6,7,8] := remove (a 15) 5 [0,3,5,6,7,8] t14 b15
  exact And.intro t3 (And.intro t11 (t15))

theorem chunk1 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,3,6,7,8])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c4 : edge r4 (a 0) (a 15)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 16)=true)
    : a 15 ∈ [0,3] ∧ a 5 ∈ [0,3,6,7] ∧ a 16 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 15 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 6 d0 c4 (by decide +kernel)
  have t0 : a 15 ∈ [0,3,7,8] := remove (a 15) 6 [0,3,6,7,8] d15 b0
  have b1 : a 15 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 7 d0 c4 (by decide +kernel)
  have t1 : a 15 ∈ [0,3,8] := remove (a 15) 7 [0,3,7,8] t0 b1
  have b2 : a 15 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 8 d0 c4 (by decide +kernel)
  have t2 : a 15 ∈ [0,3] := remove (a 15) 8 [0,3,8] t1 b2
  have b3 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b3
  have b4 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 5) 4 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 5 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,3,6,7,8,9,10,11] := remove (a 5) 5 [0,3,5,6,7,8,9,10,11] t5 b6
  have b7 : a 5 ≠ 8 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,3,6,7,9,10,11] := remove (a 5) 8 [0,3,6,7,8,9,10,11] t6 b7
  have b8 : a 5 ≠ 9 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 9 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,3,6,7,10,11] := remove (a 5) 9 [0,3,6,7,9,10,11] t7 b8
  have b9 : a 5 ≠ 10 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,3,6,7,11] := remove (a 5) 10 [0,3,6,7,10,11] t8 b9
  have b10 : a 5 ≠ 11 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 11 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,3,6,7] := remove (a 5) 11 [0,3,6,7,11] t9 b10
  have b11 : a 16 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 1 d1 c8 (by decide +kernel)
  have t11 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b11
  have b12 : a 16 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 3 d1 c8 (by decide +kernel)
  have t12 : a 16 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 16 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 4 d1 c8 (by decide +kernel)
  have t13 : a 16 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 16 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 5 d1 c8 (by decide +kernel)
  have t14 : a 16 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 16 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 7 d1 c8 (by decide +kernel)
  have t15 : a 16 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t10 (t15))

theorem chunk2 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0])
    (d3 : a 3 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c8 : edge r8 (a 1) (a 16)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 16 ∈ [0,2,6,8,12,14] ∧ a 3 ∈ [0,1] ∧ a 6 ∈ [0,1,2,3,9,10,11] := by
  have b0 : a 16 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 9 d1 c8 (by decide +kernel)
  have t0 : a 16 ∈ [0,2,6,8,10,11,12,13,14,15,16,17] := remove (a 16) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17] d16 b0
  have b1 : a 16 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 10 d1 c8 (by decide +kernel)
  have t1 : a 16 ∈ [0,2,6,8,11,12,13,14,15,16,17] := remove (a 16) 10 [0,2,6,8,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 16 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 11 d1 c8 (by decide +kernel)
  have t2 : a 16 ∈ [0,2,6,8,12,13,14,15,16,17] := remove (a 16) 11 [0,2,6,8,11,12,13,14,15,16,17] t1 b2
  have b3 : a 16 ≠ 13 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 13 d1 c8 (by decide +kernel)
  have t3 : a 16 ∈ [0,2,6,8,12,14,15,16,17] := remove (a 16) 13 [0,2,6,8,12,13,14,15,16,17] t2 b3
  have b4 : a 16 ≠ 15 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 15 d1 c8 (by decide +kernel)
  have t4 : a 16 ∈ [0,2,6,8,12,14,16,17] := remove (a 16) 15 [0,2,6,8,12,14,15,16,17] t3 b4
  have b5 : a 16 ≠ 16 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 16 d1 c8 (by decide +kernel)
  have t5 : a 16 ∈ [0,2,6,8,12,14,17] := remove (a 16) 16 [0,2,6,8,12,14,16,17] t4 b5
  have b6 : a 16 ≠ 17 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 17 d1 c8 (by decide +kernel)
  have t6 : a 16 ∈ [0,2,6,8,12,14] := remove (a 16) 17 [0,2,6,8,12,14,17] t5 b6
  have b7 : a 3 ≠ 2 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t7 : a 3 ∈ [0,1,3,4,5] := remove (a 3) 2 [0,1,2,3,4,5] d3 b7
  have b8 : a 3 ≠ 3 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t8 : a 3 ∈ [0,1,4,5] := remove (a 3) 3 [0,1,3,4,5] t7 b8
  have b9 : a 3 ≠ 4 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t9 : a 3 ∈ [0,1,5] := remove (a 3) 4 [0,1,4,5] t8 b9
  have b10 : a 3 ≠ 5 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 5 d2 c9 (by decide +kernel)
  have t10 : a 3 ∈ [0,1] := remove (a 3) 5 [0,1,5] t9 b10
  have b11 : a 6 ≠ 4 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 6) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b11
  have b12 : a 6 ≠ 5 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 6) 5 [0,1,2,3,5,6,7,8,9,10,11] t11 b12
  have b13 : a 6 ≠ 6 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 6) 6 [0,1,2,3,6,7,8,9,10,11] t12 b13
  have b14 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,2,3,8,9,10,11] := remove (a 6) 7 [0,1,2,3,7,8,9,10,11] t13 b14
  have b15 : a 6 ≠ 8 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,2,3,9,10,11] := remove (a 6) 8 [0,1,2,3,8,9,10,11] t14 b15
  exact And.intro t6 (And.intro t10 (t15))

theorem chunk3 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,2,3,9,10,11])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 17)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 6 ∈ [0,1,2,3] ∧ a 10 ∈ [0,1] ∧ a 17 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0,1,4,5] := by
  have b0 : a 6 ≠ 9 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 9 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,2,3,10,11] := remove (a 6) 9 [0,1,2,3,9,10,11] d6 b0
  have b1 : a 6 ≠ 10 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 10 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,2,3,11] := remove (a 6) 10 [0,1,2,3,10,11] t0 b1
  have b2 : a 6 ≠ 11 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 11 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,2,3] := remove (a 6) 11 [0,1,2,3,11] t1 b2
  have b3 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1] := remove (a 10) 2 [0,1,2] d10 b3
  have b4 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 1 d2 c12 (by decide +kernel)
  have t4 : a 17 ∈ [0,2,3,4,5,6,7,8] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8] d17 b4
  have b5 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 2 d2 c12 (by decide +kernel)
  have t5 : a 17 ∈ [0,3,4,5,6,7,8] := remove (a 17) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 3 d2 c12 (by decide +kernel)
  have t6 : a 17 ∈ [0,4,5,6,7,8] := remove (a 17) 3 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 4 d2 c12 (by decide +kernel)
  have t7 : a 17 ∈ [0,5,6,7,8] := remove (a 17) 4 [0,4,5,6,7,8] t6 b7
  have b8 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 5 d2 c12 (by decide +kernel)
  have t8 : a 17 ∈ [0,6,7,8] := remove (a 17) 5 [0,5,6,7,8] t7 b8
  have b9 : a 17 ≠ 6 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 6 d2 c12 (by decide +kernel)
  have t9 : a 17 ∈ [0,7,8] := remove (a 17) 6 [0,6,7,8] t8 b9
  have b10 : a 17 ≠ 7 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 7 d2 c12 (by decide +kernel)
  have t10 : a 17 ∈ [0,8] := remove (a 17) 7 [0,7,8] t9 b10
  have b11 : a 17 ≠ 8 := exclude [0,1] (fun u v => edge r12 v u) (a 17) (a 2) 8 d2 c12 (by decide +kernel)
  have t11 : a 17 ∈ [0] := remove (a 17) 8 [0,8] t10 b11
  have b12 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t12 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b12
  have b13 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t13 : a 7 ∈ [0] := remove (a 7) 2 [0,2] t12 b13
  have b14 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,1,3,4,5] := remove (a 11) 2 [0,1,2,3,4,5] d11 b14
  have b15 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,4,5] := remove (a 11) 3 [0,1,3,4,5] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t11 (And.intro t13 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_183
