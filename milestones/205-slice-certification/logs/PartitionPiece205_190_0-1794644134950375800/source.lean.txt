import PartitionData205_190
namespace PartitionCover205_190
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,1,2,3])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 8 ∈ [0,1,2,4] ∧ a 16 ∈ [0,2] ∧ a 9 ∈ [0,1] ∧ a 17 ∈ [0,2] ∧ a 10 ∈ [0,6,8,9,10,11] := by
  have b0 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,2,4,5] := remove (a 8) 3 [0,1,2,3,4,5] d8 b0
  have b1 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,2,4] := remove (a 8) 5 [0,1,2,4,5] t0 b1
  have b2 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b2
  have b3 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t2 b3
  have b4 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,1,3,4,5] := remove (a 9) 2 [0,1,2,3,4,5] d9 b4
  have b5 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,4,5] := remove (a 9) 3 [0,1,3,4,5] t4 b5
  have b6 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,5] := remove (a 9) 4 [0,1,4,5] t5 b6
  have b7 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,1] := remove (a 9) 5 [0,1,5] t6 b7
  have b8 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b8
  have b9 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t8 b9
  have b10 : a 10 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b10
  have b11 : a 10 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 10 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 10 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,5,6,7,8,9,10,11] := remove (a 10) 4 [0,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 10 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,6,7,8,9,10,11] := remove (a 10) 5 [0,5,6,7,8,9,10,11] t13 b14
  have b15 : a 10 ≠ 7 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,6,8,9,10,11] := remove (a 10) 7 [0,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (And.intro t9 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,6,8,9,10,11])
    (d2 : a 2 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 10 ∈ [0,6] ∧ a 7 ∈ [0,1,3,5] ∧ a 11 ∈ [0,2,6,8] ∧ a 19 ∈ [0,1,4,5] := by
  have b0 : a 10 ≠ 8 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,6,9,10,11] := remove (a 10) 8 [0,6,8,9,10,11] d10 b0
  have b1 : a 10 ≠ 9 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,6,10,11] := remove (a 10) 9 [0,6,9,10,11] t0 b1
  have b2 : a 10 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,6,11] := remove (a 10) 10 [0,6,10,11] t1 b2
  have b3 : a 10 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,6] := remove (a 10) 11 [0,6,11] t2 b3
  have b4 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b4
  have b5 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 4 d3 c13 (by decide +kernel)
  have t5 : a 7 ∈ [0,1,3,5] := remove (a 7) 4 [0,1,3,4,5] t4 b5
  have b6 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b6
  have b7 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 11) 4 [0,2,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,2,6,7,8,9,10,11] := remove (a 11) 5 [0,2,5,6,7,8,9,10,11] t8 b9
  have b10 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,2,6,8,9,10,11] := remove (a 11) 7 [0,2,6,7,8,9,10,11] t9 b10
  have b11 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,2,6,8,10,11] := remove (a 11) 9 [0,2,6,8,9,10,11] t10 b11
  have b12 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,6,8,11] := remove (a 11) 10 [0,2,6,8,10,11] t11 b12
  have b13 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,6,8] := remove (a 11) 11 [0,2,6,8,11] t12 b13
  have b14 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,3,4,5] := remove (a 19) 2 [0,1,2,3,4,5] d19 b14
  have b15 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,4,5] := remove (a 19) 3 [0,1,3,4,5] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t13 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,4,5])
    (d3 : a 3 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,3,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 19 ∈ [0,1] ∧ a 6 ∈ [0,2] ∧ a 14 ∈ [0,1,2,6,7,8] ∧ a 15 ∈ [0,5,6,11] ∧ a 23 ∈ [0,1,3,4,5] := by
  have b0 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,5] := remove (a 19) 4 [0,1,4,5] d19 b0
  have b1 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1] := remove (a 19) 5 [0,1,5] t0 b1
  have b2 : a 6 ≠ 1 := exclude [0,1,3,5] (edge r23) (a 6) (a 7) 1 d7 c23 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b2
  have b3 : a 6 ≠ 3 := exclude [0,1,3,5] (edge r23) (a 6) (a 7) 3 d7 c23 (by decide +kernel)
  have t3 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t2 b3
  have b4 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t3 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,2,4,5,6,7,8] := remove (a 14) 3 [0,1,2,3,4,5,6,7,8] d14 b4
  have b5 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 t3 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,5,6,7,8] := remove (a 14) 4 [0,1,2,4,5,6,7,8] t4 b5
  have b6 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 t3 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,6,7,8] := remove (a 14) 5 [0,1,2,5,6,7,8] t5 b6
  have b7 : a 15 ≠ 1 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b7
  have b8 : a 15 ≠ 2 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 15 ≠ 3 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 15) 3 [0,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 15 ≠ 4 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,5,6,7,8,9,10,11] := remove (a 15) 4 [0,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 15 ≠ 7 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,5,6,8,9,10,11] := remove (a 15) 7 [0,5,6,7,8,9,10,11] t10 b11
  have b12 : a 15 ≠ 8 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,5,6,9,10,11] := remove (a 15) 8 [0,5,6,8,9,10,11] t11 b12
  have b13 : a 15 ≠ 9 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,5,6,10,11] := remove (a 15) 9 [0,5,6,9,10,11] t12 b13
  have b14 : a 15 ≠ 10 := exclude [0,1,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,5,6,11] := remove (a 15) 10 [0,5,6,10,11] t13 b14
  have b15 : a 23 ≠ 2 := exclude [0,1,3,5] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b15
  exact And.intro t1 (And.intro t3 (And.intro t6 (And.intro t14 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,3,4,5])
    (d7 : a 7 ∈ [0,1,3,5])
    (d8 : a 8 ∈ [0,1,2,4])
    (d9 : a 9 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 23 ∈ [0,1,3,5] ∧ a 8 ∈ [0,1] ∧ a 12 ∈ [0,1] ∧ a 24 ∈ [0,2,4,6] ∧ a 25 ∈ [0,1,2,3,8,9,10,11,13] := by
  have b0 : a 23 ≠ 4 := exclude [0,1,3,5] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,3,5] := remove (a 23) 4 [0,1,3,4,5] d23 b0
  have b1 : a 8 ≠ 2 := exclude [0,1] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,4] := remove (a 8) 2 [0,1,2,4] d8 b1
  have b2 : a 8 ≠ 4 := exclude [0,1] (edge r28) (a 8) (a 9) 4 d9 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0,1] := remove (a 8) 4 [0,1,4] t1 b2
  have b3 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 2 t2 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b3
  have b4 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 3 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t3 b4
  have b5 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 4 t2 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] t4 b5
  have b6 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 5 t2 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t5 b6
  have b7 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 t2 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,2,3,4,5,6,7] := remove (a 24) 1 [0,1,2,3,4,5,6,7] d24 b7
  have b8 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 t2 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,4,5,6,7] := remove (a 24) 3 [0,2,3,4,5,6,7] t7 b8
  have b9 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 t2 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,4,6,7] := remove (a 24) 5 [0,2,4,5,6,7] t8 b9
  have b10 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 t2 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,2,4,6] := remove (a 24) 7 [0,2,4,6,7] t9 b10
  have b11 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13] := remove (a 25) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d25 b11
  have b12 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,2,3,6,7,8,9,10,11,12,13] := remove (a 25) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13] t11 b12
  have b13 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,2,3,7,8,9,10,11,12,13] := remove (a 25) 6 [0,1,2,3,6,7,8,9,10,11,12,13] t12 b13
  have b14 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,8,9,10,11,12,13] := remove (a 25) 7 [0,1,2,3,7,8,9,10,11,12,13] t13 b14
  have b15 : a 25 ≠ 12 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,2,3,8,9,10,11,13] := remove (a 25) 12 [0,1,2,3,8,9,10,11,12,13] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t6 (And.intro t10 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_190
