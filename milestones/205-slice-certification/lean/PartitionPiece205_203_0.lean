import PartitionData205_203
namespace PartitionCover205_203
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,2])
    (d1 : a 1 ∈ [0])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0,3] ∧ a 16 ∈ [0,2] ∧ a 9 ∈ [0,1] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2,4,5] := remove (a 2) 3 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,2,5] := remove (a 2) 4 [0,2,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,2] := remove (a 2) 5 [0,2,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3,4,5,6,7,8] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3,4,5,6,7,8] := remove (a 8) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,3,5,6,7,8] := remove (a 8) 4 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,3,6,7,8] := remove (a 8) 5 [0,3,5,6,7,8] t6 b7
  have b8 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,3,7,8] := remove (a 8) 6 [0,3,6,7,8] t7 b8
  have b9 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,3,8] := remove (a 8) 7 [0,3,7,8] t8 b9
  have b10 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,3] := remove (a 8) 8 [0,3,8] t9 b10
  have b11 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,2,3,4,5] := remove (a 16) 1 [0,1,2,3,4,5] d16 b11
  have b12 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,2,4,5] := remove (a 16) 3 [0,2,3,4,5] t11 b12
  have b13 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,2,5] := remove (a 16) 4 [0,2,4,5] t12 b13
  have b14 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,2] := remove (a 16) 5 [0,2,5] t13 b14
  have b15 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,1] := remove (a 9) 2 [0,1,2] d9 b15
  exact And.intro t3 (And.intro t10 (And.intro t14 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 3 ∈ [0,1] ∧ a 6 ∈ [0,1,4,5] ∧ a 10 ∈ [0,4] := by
  have b0 : a 3 ≠ 2 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0,1] := remove (a 3) 2 [0,1,2] d3 b0
  have b1 : a 6 ≠ 2 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,3,4,5,6,7,8] := remove (a 6) 2 [0,1,2,3,4,5,6,7,8] d6 b1
  have b2 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,4,5,6,7,8] := remove (a 6) 3 [0,1,3,4,5,6,7,8] t1 b2
  have b3 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,4,5,7,8] := remove (a 6) 6 [0,1,4,5,6,7,8] t2 b3
  have b4 : a 6 ≠ 7 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,4,5,8] := remove (a 6) 7 [0,1,4,5,7,8] t3 b4
  have b5 : a 6 ≠ 8 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,1,4,5] := remove (a 6) 8 [0,1,4,5,8] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b6
  have b7 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,4,6,7,8,9,10,11] := remove (a 10) 5 [0,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,4,7,8,9,10,11] := remove (a 10) 6 [0,4,6,7,8,9,10,11] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,4,8,9,10,11] := remove (a 10) 7 [0,4,7,8,9,10,11] t10 b11
  have b12 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,4,9,10,11] := remove (a 10) 8 [0,4,8,9,10,11] t11 b12
  have b13 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,4,10,11] := remove (a 10) 9 [0,4,9,10,11] t12 b13
  have b14 : a 10 ≠ 10 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,4,11] := remove (a 10) 10 [0,4,10,11] t13 b14
  have b15 : a 10 ≠ 11 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,4] := remove (a 10) 11 [0,4,11] t14 b15
  exact And.intro t0 (And.intro t5 (t15))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,2])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,3] ∧ a 7 ∈ [0,1,2,3] ∧ a 11 ∈ [0,4,5,6,8] := by
  have b0 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b0
  have b1 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 18) 4 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,3,6,7,8,9,10,11] := remove (a 18) 5 [0,3,5,6,7,8,9,10,11] t2 b3
  have b4 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,3,7,8,9,10,11] := remove (a 18) 6 [0,3,6,7,8,9,10,11] t3 b4
  have b5 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,3,8,9,10,11] := remove (a 18) 7 [0,3,7,8,9,10,11] t4 b5
  have b6 : a 18 ≠ 8 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,3,9,10,11] := remove (a 18) 8 [0,3,8,9,10,11] t5 b6
  have b7 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,3,10,11] := remove (a 18) 9 [0,3,9,10,11] t6 b7
  have b8 : a 18 ≠ 10 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,3,11] := remove (a 18) 10 [0,3,10,11] t7 b8
  have b9 : a 18 ≠ 11 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,3] := remove (a 18) 11 [0,3,11] t8 b9
  have b10 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 4 d3 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0,1,2,3,5] := remove (a 7) 4 [0,1,2,3,4,5] d7 b10
  have b11 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 5 d3 c13 (by decide +kernel)
  have t11 : a 7 ∈ [0,1,2,3] := remove (a 7) 5 [0,1,2,3,5] t10 b11
  have b12 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,3,4,5,6,7,8] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8] d11 b12
  have b13 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,3,4,5,6,7,8] := remove (a 11) 2 [0,2,3,4,5,6,7,8] t12 b13
  have b14 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,4,5,6,7,8] := remove (a 11) 3 [0,3,4,5,6,7,8] t13 b14
  have b15 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,4,5,6,8] := remove (a 11) 7 [0,4,5,6,7,8] t14 b15
  exact And.intro t9 (And.intro t11 (t15))

theorem chunk3 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,4,5,6,8])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,1,4,5])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 11 ∈ [0,4,5,6] ∧ a 19 ∈ [0,4,6,8] ∧ a 6 ∈ [0,4] ∧ a 12 ∈ [0,2,6,8,9,10,11] := by
  have b0 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,4,5,6] := remove (a 11) 8 [0,4,5,6,8] d11 b0
  have b1 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b1
  have b2 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,4,6,7,8,9,10,11] := remove (a 19) 5 [0,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 19 ≠ 7 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,4,6,8,9,10,11] := remove (a 19) 7 [0,4,6,7,8,9,10,11] t4 b5
  have b6 : a 19 ≠ 9 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0,4,6,8,10,11] := remove (a 19) 9 [0,4,6,8,9,10,11] t5 b6
  have b7 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,4,6,8,11] := remove (a 19) 10 [0,4,6,8,10,11] t6 b7
  have b8 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 11 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,4,6,8] := remove (a 19) 11 [0,4,6,8,11] t7 b8
  have b9 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 d4 c17 (by decide +kernel)
  have t9 : a 6 ∈ [0,4,5] := remove (a 6) 1 [0,1,4,5] d6 b9
  have b10 : a 6 ≠ 5 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 5 d4 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t9 b10
  have b11 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b11
  have b12 : a 12 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 12) 3 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 12 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 12) 4 [0,2,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 12 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,6,7,8,9,10,11] := remove (a 12) 5 [0,2,5,6,7,8,9,10,11] t13 b14
  have b15 : a 12 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,2,6,8,9,10,11] := remove (a 12) 7 [0,2,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t8 (And.intro t10 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_203
