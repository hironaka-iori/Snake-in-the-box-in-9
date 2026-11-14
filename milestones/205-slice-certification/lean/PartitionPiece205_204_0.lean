import PartitionData205_204
namespace PartitionCover205_204
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0,2] ∧ a 16 ∈ [0,1] ∧ a 9 ∈ [0,1,2,4] ∧ a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
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
  have b9 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,3,4,5] := remove (a 16) 2 [0,1,2,3,4,5] d16 b9
  have b10 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,4,5] := remove (a 16) 3 [0,1,3,4,5] t9 b10
  have b11 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,5] := remove (a 16) 4 [0,1,4,5] t10 b11
  have b12 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1] := remove (a 16) 5 [0,1,5] t11 b12
  have b13 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,2,4,5] := remove (a 9) 3 [0,1,2,3,4,5] d9 b13
  have b14 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,2,4] := remove (a 9) 5 [0,1,2,4,5] t13 b14
  have b15 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 17) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b15
  exact And.intro t1 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 17 ∈ [0,1,2,3] ∧ a 6 ∈ [0,4] ∧ a 10 ∈ [0,5,7,8,9,10,11] := by
  have b0 : a 17 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 17) 5 [0,1,2,3,5,6,7,8,9,10,11] d17 b0
  have b1 : a 17 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 17) 6 [0,1,2,3,6,7,8,9,10,11] t0 b1
  have b2 : a 17 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,2,3,8,9,10,11] := remove (a 17) 7 [0,1,2,3,7,8,9,10,11] t1 b2
  have b3 : a 17 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,2,3,9,10,11] := remove (a 17) 8 [0,1,2,3,8,9,10,11] t2 b3
  have b4 : a 17 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,2,3,10,11] := remove (a 17) 9 [0,1,2,3,9,10,11] t3 b4
  have b5 : a 17 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 10 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,2,3,11] := remove (a 17) 10 [0,1,2,3,10,11] t4 b5
  have b6 : a 17 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 11 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,2,3] := remove (a 17) 11 [0,1,2,3,11] t5 b6
  have b7 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b7
  have b8 : a 6 ≠ 2 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,3,4,5] := remove (a 6) 2 [0,2,3,4,5] t7 b8
  have b9 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,4,5] := remove (a 6) 3 [0,3,4,5] t8 b9
  have b10 : a 6 ≠ 5 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t9 b10
  have b11 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b11
  have b12 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 10 ≠ 4 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,5,6,7,8,9,10,11] := remove (a 10) 4 [0,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,5,7,8,9,10,11] := remove (a 10) 6 [0,5,6,7,8,9,10,11] t14 b15
  exact And.intro t6 (And.intro t10 (t15))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,5,7,8,9,10,11])
    (d2 : a 2 ∈ [0,2])
    (d18 : a 18 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 10 ∈ [0,5] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0,2] ∧ a 11 ∈ [0,6] ∧ a 12 ∈ [0,1,3,4,5] := by
  have b0 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,5,8,9,10,11] := remove (a 10) 7 [0,5,7,8,9,10,11] d10 b0
  have b1 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,5,9,10,11] := remove (a 10) 8 [0,5,8,9,10,11] t0 b1
  have b2 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,5,10,11] := remove (a 10) 9 [0,5,9,10,11] t1 b2
  have b3 : a 10 ≠ 10 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,5,11] := remove (a 10) 10 [0,5,10,11] t2 b3
  have b4 : a 10 ≠ 11 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,5] := remove (a 10) 11 [0,5,11] t3 b4
  have b5 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b5
  have b6 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0] := remove (a 18) 2 [0,2] t5 b6
  have b7 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t7 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b7
  have b8 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,3,4,5,6,7,8] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8] d11 b8
  have b9 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,3,4,5,6,7,8] := remove (a 11) 2 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,4,5,6,7,8] := remove (a 11) 3 [0,3,4,5,6,7,8] t9 b10
  have b11 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,5,6,7,8] := remove (a 11) 4 [0,4,5,6,7,8] t10 b11
  have b12 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,6,7,8] := remove (a 11) 5 [0,5,6,7,8] t11 b12
  have b13 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,6,8] := remove (a 11) 7 [0,6,7,8] t12 b13
  have b14 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,6] := remove (a 11) 8 [0,6,8] t13 b14
  have b15 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b15
  exact And.intro t4 (And.intro t6 (And.intro t7 (And.intro t14 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,3,4,5])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,4])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 12 ∈ [0,1] ∧ a 20 ∈ [0,1] ∧ a 14 ∈ [0,1,4,8,10,11,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] d12 b0
  have b1 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t1 b2
  have b3 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,3,4,5] := remove (a 20) 2 [0,1,2,3,4,5] d20 b3
  have b4 : a 20 ≠ 3 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,4,5] := remove (a 20) 3 [0,1,3,4,5] t3 b4
  have b5 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,5] := remove (a 20) 4 [0,1,4,5] t4 b5
  have b6 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t5 b6
  have b7 : a 14 ≠ 2 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b7
  have b8 : a 14 ≠ 3 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 5 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 6 [0,1,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 7 [0,1,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 14 ≠ 9 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 9 [0,1,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 14 ≠ 12 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 12 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,4,8,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 12 [0,1,4,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 14 ≠ 13 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,4,8,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 13 [0,1,4,8,10,11,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 14 ≠ 14 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,4,8,10,11,15,16,17,18,19,20,21,22,23] := remove (a 14) 14 [0,1,4,8,10,11,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t6 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_204
