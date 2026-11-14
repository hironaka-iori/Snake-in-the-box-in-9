import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 4 ∈ [0,2] ∧ a 8 ∈ [0] ∧ a 16 ∈ [0,1,5,6,7,8,9] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,4,5] := remove (a 4) 3 [0,2,3,4,5] t0 b1
  have b2 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,5] := remove (a 4) 4 [0,2,4,5] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2] := remove (a 4) 5 [0,2,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3,4,5,6,7,8,9] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9] t4 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,4,5,6,7,8,9] := remove (a 8) 3 [0,3,4,5,6,7,8,9] t5 b6
  have b7 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,5,6,7,8,9] := remove (a 8) 4 [0,4,5,6,7,8,9] t6 b7
  have b8 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,6,7,8,9] := remove (a 8) 5 [0,5,6,7,8,9] t7 b8
  have b9 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,7,8,9] := remove (a 8) 6 [0,6,7,8,9] t8 b9
  have b10 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,8,9] := remove (a 8) 7 [0,7,8,9] t9 b10
  have b11 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,9] := remove (a 8) 8 [0,8,9] t10 b11
  have b12 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 9 [0,9] t11 b12
  have b13 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9] d16 b13
  have b14 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,4,5,6,7,8,9] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9] t13 b14
  have b15 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,5,6,7,8,9] := remove (a 16) 4 [0,1,4,5,6,7,8,9] t14 b15
  exact And.intro t3 (And.intro t12 (t15))

theorem chunk1 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,5,6,7,8,9])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 16 ∈ [0,1,6,7] ∧ a 5 ∈ [0,1,4,5] ∧ a 9 ∈ [0,1,4,5,6,7,10,11,12,13] ∧ a 17 ∈ [0,1,3,4,5,6,7,8,9] := by
  have b0 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,6,7,8,9] := remove (a 16) 5 [0,1,5,6,7,8,9] d16 b0
  have b1 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,1,6,7,9] := remove (a 16) 8 [0,1,6,7,8,9] t0 b1
  have b2 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,6,7] := remove (a 16) 9 [0,1,6,7,9] t1 b2
  have b3 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,3,4,5] := remove (a 5) 2 [0,1,2,3,4,5] d5 b3
  have b4 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,1,4,5] := remove (a 5) 3 [0,1,3,4,5] t3 b4
  have b5 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d9 b5
  have b6 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 9 ≠ 8 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] := remove (a 9) 8 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 9 ≠ 9 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,14,15,16,17,18,19] := remove (a 9) 9 [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 9 ≠ 14 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 14 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,15,16,17,18,19] := remove (a 9) 14 [0,1,4,5,6,7,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 9 ≠ 15 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 15 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,16,17,18,19] := remove (a 9) 15 [0,1,4,5,6,7,10,11,12,13,15,16,17,18,19] t9 b10
  have b11 : a 9 ≠ 16 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 16 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,17,18,19] := remove (a 9) 16 [0,1,4,5,6,7,10,11,12,13,16,17,18,19] t10 b11
  have b12 : a 9 ≠ 17 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 17 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,18,19] := remove (a 9) 17 [0,1,4,5,6,7,10,11,12,13,17,18,19] t11 b12
  have b13 : a 9 ≠ 18 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 18 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13,19] := remove (a 9) 18 [0,1,4,5,6,7,10,11,12,13,18,19] t12 b13
  have b14 : a 9 ≠ 19 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 19 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13] := remove (a 9) 19 [0,1,4,5,6,7,10,11,12,13,19] t13 b14
  have b15 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 17) 2 [0,1,2,3,4,5,6,7,8,9] d17 b15
  exact And.intro t2 (And.intro t4 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,3,4,5,6,7,8,9])
    (d1 : a 1 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (d2 : a 2 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 17 ∈ [0,1] ∧ a 6 ∈ [0,2,3,5] ∧ a 18 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18] := by
  have b0 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,4,5,6,7,8,9] := remove (a 17) 3 [0,1,3,4,5,6,7,8,9] d17 b0
  have b1 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,5,6,7,8,9] := remove (a 17) 4 [0,1,4,5,6,7,8,9] t0 b1
  have b2 : a 17 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,6,7,8,9] := remove (a 17) 5 [0,1,5,6,7,8,9] t1 b2
  have b3 : a 17 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,7,8,9] := remove (a 17) 6 [0,1,6,7,8,9] t2 b3
  have b4 : a 17 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,8,9] := remove (a 17) 7 [0,1,7,8,9] t3 b4
  have b5 : a 17 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,9] := remove (a 17) 8 [0,1,8,9] t4 b5
  have b6 : a 17 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1] := remove (a 17) 9 [0,1,9] t5 b6
  have b7 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,3,4,5,6,7,8] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8] d6 b7
  have b8 : a 6 ≠ 4 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,3,5,6,7,8] := remove (a 6) 4 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 6 ≠ 6 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,3,5,7,8] := remove (a 6) 6 [0,2,3,5,6,7,8] t8 b9
  have b10 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,3,5,8] := remove (a 6) 7 [0,2,3,5,7,8] t9 b10
  have b11 : a 6 ≠ 8 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,3,5] := remove (a 6) 8 [0,2,3,5,8] t10 b11
  have b12 : a 18 ≠ 5 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 5 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d18 b12
  have b13 : a 18 ≠ 7 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 7 [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 18 ≠ 17 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18,19] := remove (a 18) 17 [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 18 ≠ 19 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 19 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18] := remove (a 18) 19 [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18,19] t14 b15
  exact And.intro t6 (And.intro t11 (t15))

theorem chunk3 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d3 : a 3 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 11 ∈ [0,8,10,11] ∧ a 19 ∈ [0,1] := by
  have b0 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b0
  have b1 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,5,6,7,8,9,10,11] := remove (a 11) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 11 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,6,7,8,9,10,11] := remove (a 11) 5 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,7,8,9,10,11] := remove (a 11) 6 [0,6,7,8,9,10,11] t4 b5
  have b6 : a 11 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,8,9,10,11] := remove (a 11) 7 [0,7,8,9,10,11] t5 b6
  have b7 : a 11 ≠ 9 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,8,10,11] := remove (a 11) 9 [0,8,9,10,11] t6 b7
  have b8 : a 19 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9] d19 b8
  have b9 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,4,5,6,7,8,9] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9] t8 b9
  have b10 : a 19 ≠ 4 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,5,6,7,8,9] := remove (a 19) 4 [0,1,4,5,6,7,8,9] t9 b10
  have b11 : a 19 ≠ 5 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,6,7,8,9] := remove (a 19) 5 [0,1,5,6,7,8,9] t10 b11
  have b12 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,7,8,9] := remove (a 19) 6 [0,1,6,7,8,9] t11 b12
  have b13 : a 19 ≠ 7 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,8,9] := remove (a 19) 7 [0,1,7,8,9] t12 b13
  have b14 : a 19 ≠ 8 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,9] := remove (a 19) 8 [0,1,8,9] t13 b14
  have b15 : a 19 ≠ 9 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1] := remove (a 19) 9 [0,1,9] t14 b15
  exact And.intro t7 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_170
