import PartitionData205_188
namespace PartitionCover205_188
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 2 ∈ [0,1] ∧ a 8 ∈ [0,2] ∧ a 9 ∈ [0,2,6,8] ∧ a 17 ∈ [0,1] := by
  have b0 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,3] := remove (a 2) 2 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1] := remove (a 2) 3 [0,1,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3,4,5,6,7,8] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,2,4,5,6,7,8] := remove (a 8) 3 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,5,6,7,8] := remove (a 8) 4 [0,2,4,5,6,7,8] t3 b4
  have b5 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,2,6,7,8] := remove (a 8) 5 [0,2,5,6,7,8] t4 b5
  have b6 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,2,7,8] := remove (a 8) 6 [0,2,6,7,8] t5 b6
  have b7 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,2,8] := remove (a 8) 7 [0,2,7,8] t6 b7
  have b8 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,2] := remove (a 8) 8 [0,2,8] t7 b8
  have b9 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,2,3,4,5,6,7,8] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8] d9 b9
  have b10 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,2,4,5,6,7,8] := remove (a 9) 3 [0,2,3,4,5,6,7,8] t9 b10
  have b11 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,2,5,6,7,8] := remove (a 9) 4 [0,2,4,5,6,7,8] t10 b11
  have b12 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,6,7,8] := remove (a 9) 5 [0,2,5,6,7,8] t11 b12
  have b13 : a 9 ≠ 7 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,2,6,8] := remove (a 9) 7 [0,2,6,7,8] t12 b13
  have b14 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t14 : a 17 ∈ [0,1,3] := remove (a 17) 2 [0,1,2,3] d17 b14
  have b15 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,1] := remove (a 17) 3 [0,1,3] t14 b15
  exact And.intro t1 (And.intro t8 (And.intro t13 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 3 ∈ [0,1] ∧ a 6 ∈ [0,1,2,3,4,5] ∧ a 10 ∈ [0,1,2,4,6,7,8,10] ∧ a 18 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 3 ≠ 2 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0,1,3] := remove (a 3) 2 [0,1,2,3] d3 b0
  have b1 : a 3 ≠ 3 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t1 : a 3 ∈ [0,1] := remove (a 3) 3 [0,1,3] t0 b1
  have b2 : a 6 ≠ 6 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,2,3,4,5,7,8] := remove (a 6) 6 [0,1,2,3,4,5,6,7,8] d6 b2
  have b3 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,2,3,4,5,8] := remove (a 6) 7 [0,1,2,3,4,5,7,8] t2 b3
  have b4 : a 6 ≠ 8 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,2,3,4,5] := remove (a 6) 8 [0,1,2,3,4,5,8] t3 b4
  have b5 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 10) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d10 b5
  have b6 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,2,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 10) 5 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 10 ≠ 9 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,2,4,6,7,8,10,11,12,13,14,15,16,17] := remove (a 10) 9 [0,1,2,4,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 10 ≠ 11 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,2,4,6,7,8,10,12,13,14,15,16,17] := remove (a 10) 11 [0,1,2,4,6,7,8,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 10 ≠ 12 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 12 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,2,4,6,7,8,10,13,14,15,16,17] := remove (a 10) 12 [0,1,2,4,6,7,8,10,12,13,14,15,16,17] t8 b9
  have b10 : a 10 ≠ 13 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,2,4,6,7,8,10,14,15,16,17] := remove (a 10) 13 [0,1,2,4,6,7,8,10,13,14,15,16,17] t9 b10
  have b11 : a 10 ≠ 14 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 14 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,2,4,6,7,8,10,15,16,17] := remove (a 10) 14 [0,1,2,4,6,7,8,10,14,15,16,17] t10 b11
  have b12 : a 10 ≠ 15 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 15 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,2,4,6,7,8,10,16,17] := remove (a 10) 15 [0,1,2,4,6,7,8,10,15,16,17] t11 b12
  have b13 : a 10 ≠ 16 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,2,4,6,7,8,10,17] := remove (a 10) 16 [0,1,2,4,6,7,8,10,16,17] t12 b13
  have b14 : a 10 ≠ 17 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 17 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,2,4,6,7,8,10] := remove (a 10) 17 [0,1,2,4,6,7,8,10,17] t13 b14
  have b15 : a 18 ≠ 4 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d18 b15
  exact And.intro t1 (And.intro t4 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d2 : a 2 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,1,2,3,6,7,8,9] ∧ a 11 ∈ [0,6,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 18 ≠ 5 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] d18 b0
  have b1 : a 18 ≠ 10 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] := remove (a 18) 10 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 18 ≠ 11 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,2,3,6,7,8,9,12,13,14,15,16,17] := remove (a 18) 11 [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] t1 b2
  have b3 : a 18 ≠ 12 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 12 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,2,3,6,7,8,9,13,14,15,16,17] := remove (a 18) 12 [0,1,2,3,6,7,8,9,12,13,14,15,16,17] t2 b3
  have b4 : a 18 ≠ 13 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,2,3,6,7,8,9,14,15,16,17] := remove (a 18) 13 [0,1,2,3,6,7,8,9,13,14,15,16,17] t3 b4
  have b5 : a 18 ≠ 14 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 14 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,2,3,6,7,8,9,15,16,17] := remove (a 18) 14 [0,1,2,3,6,7,8,9,14,15,16,17] t4 b5
  have b6 : a 18 ≠ 15 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,2,3,6,7,8,9,16,17] := remove (a 18) 15 [0,1,2,3,6,7,8,9,15,16,17] t5 b6
  have b7 : a 18 ≠ 16 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,2,3,6,7,8,9,17] := remove (a 18) 16 [0,1,2,3,6,7,8,9,16,17] t6 b7
  have b8 : a 18 ≠ 17 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,2,3,6,7,8,9] := remove (a 18) 17 [0,1,2,3,6,7,8,9,17] t7 b8
  have b9 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d11 b9
  have b10 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 11) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t8 (t15)

theorem chunk3 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,6,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 11 ∈ [0,6] ∧ a 19 ∈ [0,5,9,10,11] := by
  have b0 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 11) 9 [0,6,9,10,11,12,13,14,15,16,17] d11 b0
  have b1 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 11) 10 [0,6,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,6,12,13,14,15,16,17] := remove (a 11) 11 [0,6,11,12,13,14,15,16,17] t1 b2
  have b3 : a 11 ≠ 12 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 12 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,6,13,14,15,16,17] := remove (a 11) 12 [0,6,12,13,14,15,16,17] t2 b3
  have b4 : a 11 ≠ 13 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 13 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,6,14,15,16,17] := remove (a 11) 13 [0,6,13,14,15,16,17] t3 b4
  have b5 : a 11 ≠ 14 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 14 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,6,15,16,17] := remove (a 11) 14 [0,6,14,15,16,17] t4 b5
  have b6 : a 11 ≠ 15 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 15 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,6,16,17] := remove (a 11) 15 [0,6,15,16,17] t5 b6
  have b7 : a 11 ≠ 16 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 16 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,6,17] := remove (a 11) 16 [0,6,16,17] t6 b7
  have b8 : a 11 ≠ 17 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 17 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,6] := remove (a 11) 17 [0,6,17] t7 b8
  have b9 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t9 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b9
  have b10 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,5,6,7,8,9,10,11] := remove (a 19) 4 [0,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 6 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 6 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,5,7,8,9,10,11] := remove (a 19) 6 [0,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 7 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,5,8,9,10,11] := remove (a 19) 7 [0,5,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,5,9,10,11] := remove (a 19) 8 [0,5,8,9,10,11] t14 b15
  exact And.intro t8 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_188
