import PartitionData205_205
namespace PartitionCover205_205
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0,3] ∧ a 16 ∈ [0,2] ∧ a 9 ∈ [0,4] ∧ a 17 ∈ [0,2] ∧ a 6 ∈ [0,1,4,5,6,7] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3,4,5] := remove (a 8) 1 [0,1,2,3,4,5] d8 b2
  have b3 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,3,4,5] := remove (a 8) 2 [0,2,3,4,5] t2 b3
  have b4 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,3,5] := remove (a 8) 4 [0,3,4,5] t3 b4
  have b5 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3] := remove (a 8) 5 [0,3,5] t4 b5
  have b6 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b6
  have b7 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t6 b7
  have b8 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b8
  have b9 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,3,4,5] := remove (a 9) 2 [0,2,3,4,5] t8 b9
  have b10 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,4,5] := remove (a 9) 3 [0,3,4,5] t9 b10
  have b11 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,4] := remove (a 9) 5 [0,4,5] t10 b11
  have b12 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b12
  have b13 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t13 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t12 b13
  have b14 : a 6 ≠ 2 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 2 t1 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,3,4,5,6,7] := remove (a 6) 2 [0,1,2,3,4,5,6,7] d6 b14
  have b15 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 t1 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,4,5,6,7] := remove (a 6) 3 [0,1,3,4,5,6,7] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t7 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,4,5,6,7])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 6 ∈ [0,1,4,5] ∧ a 10 ∈ [0,2] ∧ a 18 ∈ [0,7,8] := by
  have b0 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,4,5,7] := remove (a 6) 6 [0,1,4,5,6,7] d6 b0
  have b1 : a 6 ≠ 7 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,4,5] := remove (a 6) 7 [0,1,4,5,7] t0 b1
  have b2 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9] d10 b2
  have b3 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2,4,5,6,7,8,9] := remove (a 10) 3 [0,2,3,4,5,6,7,8,9] t2 b3
  have b4 : a 10 ≠ 4 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,2,5,6,7,8,9] := remove (a 10) 4 [0,2,4,5,6,7,8,9] t3 b4
  have b5 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,2,6,7,8,9] := remove (a 10) 5 [0,2,5,6,7,8,9] t4 b5
  have b6 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,7,8,9] := remove (a 10) 6 [0,2,6,7,8,9] t5 b6
  have b7 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,8,9] := remove (a 10) 7 [0,2,7,8,9] t6 b7
  have b8 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,9] := remove (a 10) 8 [0,2,8,9] t7 b8
  have b9 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,2] := remove (a 10) 9 [0,2,9] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3,4,5,6,7,8] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8] d18 b10
  have b11 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,3,4,5,6,7,8] := remove (a 18) 2 [0,2,3,4,5,6,7,8] t10 b11
  have b12 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,4,5,6,7,8] := remove (a 18) 3 [0,3,4,5,6,7,8] t11 b12
  have b13 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,5,6,7,8] := remove (a 18) 4 [0,4,5,6,7,8] t12 b13
  have b14 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,6,7,8] := remove (a 18) 5 [0,5,6,7,8] t13 b14
  have b15 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,7,8] := remove (a 18) 6 [0,6,7,8] t14 b15
  exact And.intro t1 (And.intro t9 (t15))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,7,8])
    (d2 : a 2 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,4,5])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 18 ∈ [0] ∧ a 11 ∈ [0,3,5,6] ∧ a 19 ∈ [0,2,3,4] ∧ a 7 ∈ [0,2] ∧ a 13 ∈ [0,1,4,5] ∧ a 14 ∈ [0,1,3,4] := by
  have b0 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,8] := remove (a 18) 7 [0,7,8] d18 b0
  have b1 : a 18 ≠ 8 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0] := remove (a 18) 8 [0,8] t0 b1
  have b2 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,3,4,5,6,7,8] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8] d11 b2
  have b3 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,3,4,5,6,7,8] := remove (a 11) 2 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,3,5,6,7,8] := remove (a 11) 4 [0,3,4,5,6,7,8] t3 b4
  have b5 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,3,5,6,8] := remove (a 11) 7 [0,3,5,6,7,8] t4 b5
  have b6 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,5,6] := remove (a 11) 8 [0,3,5,6,8] t5 b6
  have b7 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b7
  have b8 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,2,3,4] := remove (a 19) 5 [0,2,3,4,5] t7 b8
  have b9 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t9 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b9
  have b10 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,3,4,5,6,7] := remove (a 13) 2 [0,1,2,3,4,5,6,7] d13 b10
  have b11 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,4,5,6,7] := remove (a 13) 3 [0,1,3,4,5,6,7] t10 b11
  have b12 : a 13 ≠ 6 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,4,5,7] := remove (a 13) 6 [0,1,4,5,6,7] t11 b12
  have b13 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,4,5] := remove (a 13) 7 [0,1,4,5,7] t12 b13
  have b14 : a 14 ≠ 2 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,3,4,5] := remove (a 14) 2 [0,1,2,3,4,5] d14 b14
  have b15 : a 14 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,3,4] := remove (a 14) 5 [0,1,3,4,5] t14 b15
  exact And.intro t1 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,4,5])
    (d22 : a 22 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 6 ∈ [0,4] ∧ a 15 ∈ [0,1,4,5] ∧ a 23 ∈ [0,1,4,5] ∧ a 12 ∈ [0,2] ∧ a 24 ∈ [0,2] := by
  have b0 : a 6 ≠ 1 := exclude [0] (edge r25) (a 6) (a 22) 1 d22 c25 (by decide +kernel)
  have t0 : a 6 ∈ [0,4,5] := remove (a 6) 1 [0,1,4,5] d6 b0
  have b1 : a 6 ≠ 5 := exclude [0] (edge r25) (a 6) (a 22) 5 d22 c25 (by decide +kernel)
  have t1 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t0 b1
  have b2 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b2
  have b3 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] t2 b3
  have b4 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b4
  have b5 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b6
  have b7 : a 12 ≠ 3 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 3 d8 c30 (by decide +kernel)
  have t7 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t6 b7
  have b8 : a 24 ≠ 1 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9] d24 b8
  have b9 : a 24 ≠ 3 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,4,5,6,7,8,9] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9] t8 b9
  have b10 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,2,5,6,7,8,9] := remove (a 24) 4 [0,2,4,5,6,7,8,9] t9 b10
  have b11 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,6,7,8,9] := remove (a 24) 5 [0,2,5,6,7,8,9] t10 b11
  have b12 : a 24 ≠ 6 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,7,8,9] := remove (a 24) 6 [0,2,6,7,8,9] t11 b12
  have b13 : a 24 ≠ 7 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,8,9] := remove (a 24) 7 [0,2,7,8,9] t12 b13
  have b14 : a 24 ≠ 8 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,9] := remove (a 24) 8 [0,2,8,9] t13 b14
  have b15 : a 24 ≠ 9 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2] := remove (a 24) 9 [0,2,9] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_205
