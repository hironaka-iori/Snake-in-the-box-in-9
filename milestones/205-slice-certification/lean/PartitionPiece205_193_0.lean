import PartitionData205_193
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 2 ∈ [0,2] ∧ a 4 ∈ [0,4] ∧ a 8 ∈ [0,3] ∧ a 16 ∈ [0,3,6,7,8] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,3,4,5,6,7] := remove (a 4) 1 [0,1,2,3,4,5,6,7] d4 b2
  have b3 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,3,4,5,6,7] := remove (a 4) 2 [0,2,3,4,5,6,7] t2 b3
  have b4 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,4,5,6,7] := remove (a 4) 3 [0,3,4,5,6,7] t3 b4
  have b5 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,4,6,7] := remove (a 4) 5 [0,4,5,6,7] t4 b5
  have b6 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,7] := remove (a 4) 6 [0,4,6,7] t5 b6
  have b7 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,4] := remove (a 4) 7 [0,4,7] t6 b7
  have b8 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,2,3,4,5] := remove (a 8) 1 [0,1,2,3,4,5] d8 b8
  have b9 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,3,4,5] := remove (a 8) 2 [0,2,3,4,5] t8 b9
  have b10 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,3,5] := remove (a 8) 4 [0,3,4,5] t9 b10
  have b11 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,3] := remove (a 8) 5 [0,3,5] t10 b11
  have b12 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,2,3,4,5,6,7,8] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8] d16 b12
  have b13 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,3,4,5,6,7,8] := remove (a 16) 2 [0,2,3,4,5,6,7,8] t12 b13
  have b14 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,3,5,6,7,8] := remove (a 16) 4 [0,3,4,5,6,7,8] t13 b14
  have b15 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,3,6,7,8] := remove (a 16) 5 [0,3,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t7 (And.intro t11 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,3,6,7,8])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d2 : a 2 ∈ [0,2])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 16 ∈ [0,3] ∧ a 9 ∈ [0,2,3,5] ∧ a 17 ∈ [0,1,3,4,6,7] ∧ a 18 ∈ [0,2,6,8,12,13,14,15,16,17] := by
  have b0 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,3,7,8] := remove (a 16) 6 [0,3,6,7,8] d16 b0
  have b1 : a 16 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 7 d0 c4 (by decide +kernel)
  have t1 : a 16 ∈ [0,3,8] := remove (a 16) 7 [0,3,7,8] t0 b1
  have b2 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,3] := remove (a 16) 8 [0,3,8] t1 b2
  have b3 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b3
  have b4 : a 9 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3,5] := remove (a 9) 4 [0,2,3,4,5] t3 b4
  have b5 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,3,4,5,6,7,8] := remove (a 17) 2 [0,1,2,3,4,5,6,7,8] d17 b5
  have b6 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,3,4,6,7,8] := remove (a 17) 5 [0,1,3,4,5,6,7,8] t5 b6
  have b7 : a 17 ≠ 8 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,3,4,6,7] := remove (a 17) 8 [0,1,3,4,6,7,8] t6 b7
  have b8 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d18 b8
  have b9 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,6,8,10,11,12,13,14,15,16,17] := remove (a 18) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 18 ≠ 10 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,2,6,8,11,12,13,14,15,16,17] := remove (a 18) 10 [0,2,6,8,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 18 ≠ 11 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,6,8,12,13,14,15,16,17] := remove (a 18) 11 [0,2,6,8,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t7 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,6,8,12,13,14,15,16,17])
    (d2 : a 2 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 18 ∈ [0,2,6,8,12,14] ∧ a 11 ∈ [0,2] ∧ a 19 ∈ [0,1,6,7,8,9,10,11] := by
  have b0 : a 18 ≠ 13 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,6,8,12,14,15,16,17] := remove (a 18) 13 [0,2,6,8,12,13,14,15,16,17] d18 b0
  have b1 : a 18 ≠ 15 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,2,6,8,12,14,16,17] := remove (a 18) 15 [0,2,6,8,12,14,15,16,17] t0 b1
  have b2 : a 18 ≠ 16 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,2,6,8,12,14,17] := remove (a 18) 16 [0,2,6,8,12,14,16,17] t1 b2
  have b3 : a 18 ≠ 17 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,2,6,8,12,14] := remove (a 18) 17 [0,2,6,8,12,14,17] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9] d11 b4
  have b5 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,4,5,6,7,8,9] := remove (a 11) 3 [0,2,3,4,5,6,7,8,9] t4 b5
  have b6 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,2,5,6,7,8,9] := remove (a 11) 4 [0,2,4,5,6,7,8,9] t5 b6
  have b7 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,2,6,7,8,9] := remove (a 11) 5 [0,2,5,6,7,8,9] t6 b7
  have b8 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,7,8,9] := remove (a 11) 6 [0,2,6,7,8,9] t7 b8
  have b9 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,2,8,9] := remove (a 11) 7 [0,2,7,8,9] t8 b9
  have b10 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,2,9] := remove (a 11) 8 [0,2,8,9] t9 b10
  have b11 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,2] := remove (a 11) 9 [0,2,9] t10 b11
  have b12 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b12
  have b13 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 19) 4 [0,1,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,6,7,8,9,10,11] := remove (a 19) 5 [0,1,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t11 (t15))

theorem chunk3 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,6,7,8,9,10,11])
    (d3 : a 3 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d4 : a 4 ∈ [0,4])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 19 ∈ [0,1] ∧ a 12 ∈ [0,5,6] ∧ a 20 ∈ [0,2,4,5,6,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 19 ≠ 6 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 6 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,7,8,9,10,11] := remove (a 19) 6 [0,1,6,7,8,9,10,11] d19 b0
  have b1 : a 19 ≠ 7 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,8,9,10,11] := remove (a 19) 7 [0,1,7,8,9,10,11] t0 b1
  have b2 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,9,10,11] := remove (a 19) 8 [0,1,8,9,10,11] t1 b2
  have b3 : a 19 ≠ 9 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,10,11] := remove (a 19) 9 [0,1,9,10,11] t2 b3
  have b4 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,11] := remove (a 19) 10 [0,1,10,11] t3 b4
  have b5 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 11 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,1] := remove (a 19) 11 [0,1,11] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9] d12 b6
  have b7 : a 12 ≠ 2 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,3,4,5,6,7,8,9] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9] t6 b7
  have b8 : a 12 ≠ 3 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,4,5,6,7,8,9] := remove (a 12) 3 [0,3,4,5,6,7,8,9] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,5,6,7,8,9] := remove (a 12) 4 [0,4,5,6,7,8,9] t8 b9
  have b10 : a 12 ≠ 7 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,5,6,8,9] := remove (a 12) 7 [0,5,6,7,8,9] t9 b10
  have b11 : a 12 ≠ 8 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,5,6,9] := remove (a 12) 8 [0,5,6,8,9] t10 b11
  have b12 : a 12 ≠ 9 := exclude [0,4] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,5,6] := remove (a 12) 9 [0,5,6,9] t11 b12
  have b13 : a 20 ≠ 1 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b13
  have b14 : a 20 ≠ 3 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 7 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,2,4,5,6,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 7 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t5 (And.intro t12 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_193
