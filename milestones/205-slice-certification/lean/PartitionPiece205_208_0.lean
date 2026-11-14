import PartitionData205_208
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0,6] ∧ a 16 ∈ [0,3] ∧ a 5 ∈ [0,2,3,5] ∧ a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3,4,5,6,7,8] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8] d8 b2
  have b3 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,3,4,5,6,7,8] := remove (a 8) 2 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,4,5,6,7,8] := remove (a 8) 3 [0,3,4,5,6,7,8] t3 b4
  have b5 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,5,6,7,8] := remove (a 8) 4 [0,4,5,6,7,8] t4 b5
  have b6 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,6,7,8] := remove (a 8) 5 [0,5,6,7,8] t5 b6
  have b7 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,6,8] := remove (a 8) 7 [0,6,7,8] t6 b7
  have b8 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,6] := remove (a 8) 8 [0,6,8] t7 b8
  have b9 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,2,3,4,5] := remove (a 16) 1 [0,1,2,3,4,5] d16 b9
  have b10 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,3,4,5] := remove (a 16) 2 [0,2,3,4,5] t9 b10
  have b11 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,3,5] := remove (a 16) 4 [0,3,4,5] t10 b11
  have b12 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,3] := remove (a 16) 5 [0,3,5] t11 b12
  have b13 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b13
  have b14 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,2,3,5] := remove (a 5) 4 [0,2,3,4,5] t13 b14
  have b15 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d9 b15
  exact And.intro t1 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13])
    (d1 : a 1 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 9 ∈ [0,4,8,12] ∧ a 17 ∈ [0,2,3,5] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,2] ∧ a 10 ∈ [0,2,3,4,5,6,7,8,9] := by
  have b0 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 9) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] d9 b0
  have b1 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 9) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t0 b1
  have b2 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,4,6,7,8,9,10,11,12,13] := remove (a 9) 5 [0,4,5,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 9 ≠ 6 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 6 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,4,7,8,9,10,11,12,13] := remove (a 9) 6 [0,4,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 9 ≠ 7 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,4,8,9,10,11,12,13] := remove (a 9) 7 [0,4,7,8,9,10,11,12,13] t3 b4
  have b5 : a 9 ≠ 9 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,4,8,10,11,12,13] := remove (a 9) 9 [0,4,8,9,10,11,12,13] t4 b5
  have b6 : a 9 ≠ 10 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 10 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,4,8,11,12,13] := remove (a 9) 10 [0,4,8,10,11,12,13] t5 b6
  have b7 : a 9 ≠ 11 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 11 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,4,8,12,13] := remove (a 9) 11 [0,4,8,11,12,13] t6 b7
  have b8 : a 9 ≠ 13 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 13 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,4,8,12] := remove (a 9) 13 [0,4,8,12,13] t7 b8
  have b9 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,2,3,4,5] := remove (a 17) 1 [0,1,2,3,4,5] d17 b9
  have b10 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,2,3,5] := remove (a 17) 4 [0,2,3,4,5] t9 b10
  have b11 : a 3 ≠ 1 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t11 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b11
  have b12 : a 3 ≠ 3 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t12 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t11 b12
  have b13 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b13
  have b14 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t13 b14
  have b15 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9] d10 b15
  exact And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,2,3,4,5,6,7,8,9])
    (d2 : a 2 ∈ [0,2])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6])
    (d3 : a 3 ∈ [0,2])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    : a 10 ∈ [0,2] ∧ a 18 ∈ [0,2] ∧ a 7 ∈ [0,1,3,4,5,6] := by
  have b0 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,4,5,6,7,8,9] := remove (a 10) 3 [0,2,3,4,5,6,7,8,9] d10 b0
  have b1 : a 10 ≠ 4 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,2,5,6,7,8,9] := remove (a 10) 4 [0,2,4,5,6,7,8,9] t0 b1
  have b2 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,6,7,8,9] := remove (a 10) 5 [0,2,5,6,7,8,9] t1 b2
  have b3 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2,7,8,9] := remove (a 10) 6 [0,2,6,7,8,9] t2 b3
  have b4 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,2,8,9] := remove (a 10) 7 [0,2,7,8,9] t3 b4
  have b5 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,2,9] := remove (a 10) 8 [0,2,8,9] t4 b5
  have b6 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2] := remove (a 10) 9 [0,2,9] t5 b6
  have b7 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9] d18 b7
  have b8 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,4,5,6,7,8,9] := remove (a 18) 3 [0,2,3,4,5,6,7,8,9] t7 b8
  have b9 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,5,6,7,8,9] := remove (a 18) 4 [0,2,4,5,6,7,8,9] t8 b9
  have b10 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,6,7,8,9] := remove (a 18) 5 [0,2,5,6,7,8,9] t9 b10
  have b11 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,7,8,9] := remove (a 18) 6 [0,2,6,7,8,9] t10 b11
  have b12 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,8,9] := remove (a 18) 7 [0,2,7,8,9] t11 b12
  have b13 : a 18 ≠ 8 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,9] := remove (a 18) 8 [0,2,8,9] t12 b13
  have b14 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,2] := remove (a 18) 9 [0,2,9] t13 b14
  have b15 : a 7 ≠ 2 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t15 : a 7 ∈ [0,1,3,4,5,6] := remove (a 7) 2 [0,1,2,3,4,5,6] d7 b15
  exact And.intro t6 (And.intro t14 (t15))

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,3,4,5,6])
    (d3 : a 3 ∈ [0,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8])
    (d4 : a 4 ∈ [0,1])
    (d5 : a 5 ∈ [0,2,3,5])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 7 ∈ [0,1,4,5] ∧ a 19 ∈ [0,3] ∧ a 12 ∈ [0,6] ∧ a 5 ∈ [0,3] ∧ a 13 ∈ [0,1,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 d3 c13 (by decide +kernel)
  have t0 : a 7 ∈ [0,1,4,5,6] := remove (a 7) 3 [0,1,3,4,5,6] d7 b0
  have b1 : a 7 ≠ 6 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 6 d3 c13 (by decide +kernel)
  have t1 : a 7 ∈ [0,1,4,5] := remove (a 7) 6 [0,1,4,5,6] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b2
  have b3 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,3,4,5] := remove (a 19) 2 [0,2,3,4,5] t2 b3
  have b4 : a 19 ≠ 4 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,3,5] := remove (a 19) 4 [0,3,4,5] t3 b4
  have b5 : a 19 ≠ 5 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,3] := remove (a 19) 5 [0,3,5] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3,4,5,6,7,8] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8] d12 b6
  have b7 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,3,4,5,6,7,8] := remove (a 12) 2 [0,2,3,4,5,6,7,8] t6 b7
  have b8 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,4,5,6,7,8] := remove (a 12) 3 [0,3,4,5,6,7,8] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,5,6,7,8] := remove (a 12) 4 [0,4,5,6,7,8] t8 b9
  have b10 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,6,7,8] := remove (a 12) 5 [0,5,6,7,8] t9 b10
  have b11 : a 12 ≠ 7 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,6,8] := remove (a 12) 7 [0,6,7,8] t10 b11
  have b12 : a 12 ≠ 8 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,6] := remove (a 12) 8 [0,6,8] t11 b12
  have b13 : a 5 ≠ 2 := exclude [0,1,4,5] (edge r20) (a 5) (a 7) 2 t1 c20 (by decide +kernel)
  have t13 : a 5 ∈ [0,3,5] := remove (a 5) 2 [0,2,3,5] d5 b13
  have b14 : a 5 ≠ 5 := exclude [0,1,4,5] (edge r20) (a 5) (a 7) 5 t1 c20 (by decide +kernel)
  have t14 : a 5 ∈ [0,3] := remove (a 5) 5 [0,3,5] t13 b14
  have b15 : a 13 ≠ 3 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 3 t14 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b15
  exact And.intro t1 (And.intro t5 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_208
