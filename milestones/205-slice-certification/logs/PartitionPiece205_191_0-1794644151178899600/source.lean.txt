import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 2 ∈ [0,1,2,3,8,9,10,11] ∧ a 16 ∈ [0,2,5,6,7,10] ∧ a 1 ∈ [0,2] ∧ a 5 ∈ [0,4] ∧ a 9 ∈ [0,1,3,4,5] := by
  have b0 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 2) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d2 b0
  have b1 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 2) 5 [0,1,2,3,5,6,7,8,9,10,11] t0 b1
  have b2 : a 2 ≠ 6 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 6 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 2) 6 [0,1,2,3,6,7,8,9,10,11] t1 b2
  have b3 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,1,2,3,8,9,10,11] := remove (a 2) 7 [0,1,2,3,7,8,9,10,11] t2 b3
  have b4 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d16 b4
  have b5 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 16) 3 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 16) 4 [0,2,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,2,5,6,7,9,10,11] := remove (a 16) 8 [0,2,5,6,7,8,9,10,11] t6 b7
  have b8 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,2,5,6,7,10,11] := remove (a 16) 9 [0,2,5,6,7,9,10,11] t7 b8
  have b9 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,2,5,6,7,10] := remove (a 16) 11 [0,2,5,6,7,10,11] t8 b9
  have b10 : a 1 ≠ 1 := exclude [0,1,2,3,4,5] (edge r6) (a 1) (a 5) 1 d5 c6 (by decide +kernel)
  have t10 : a 1 ∈ [0,2] := remove (a 1) 1 [0,1,2] d1 b10
  have b11 : a 5 ≠ 1 := exclude [0,2] (fun u v => edge r6 v u) (a 5) (a 1) 1 t10 c6 (by decide +kernel)
  have t11 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b11
  have b12 : a 5 ≠ 2 := exclude [0,2] (fun u v => edge r6 v u) (a 5) (a 1) 2 t10 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,3,4,5] := remove (a 5) 2 [0,2,3,4,5] t11 b12
  have b13 : a 5 ≠ 3 := exclude [0,2] (fun u v => edge r6 v u) (a 5) (a 1) 3 t10 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,4,5] := remove (a 5) 3 [0,3,4,5] t12 b13
  have b14 : a 5 ≠ 5 := exclude [0,2] (fun u v => edge r6 v u) (a 5) (a 1) 5 t10 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,4] := remove (a 5) 5 [0,4,5] t13 b14
  have b15 : a 9 ≠ 2 := exclude [0,2] (fun u v => edge r7 v u) (a 9) (a 1) 2 t10 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,3,4,5] := remove (a 9) 2 [0,1,2,3,4,5] d9 b15
  exact And.intro t3 (And.intro t9 (And.intro t10 (And.intro t14 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,3,4,5])
    (d1 : a 1 ∈ [0,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,1,2,3,8,9,10,11])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 9 ∈ [0,1,4,5] ∧ a 17 ∈ [0,1,2,3,5,6,7,8,14,15,16,17] ∧ a 3 ∈ [0,1,2,3,8,9,10,11] ∧ a 6 ∈ [0,1,2,3,8,9,10,11] ∧ a 10 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 9 ≠ 3 := exclude [0,2] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,4,5] := remove (a 9) 3 [0,1,3,4,5] d9 b0
  have b1 : a 17 ≠ 4 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 17) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d17 b1
  have b2 : a 17 ≠ 9 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,2,3,5,6,7,8,10,11,12,13,14,15,16,17] := remove (a 17) 9 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 17 ≠ 10 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 10 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,2,3,5,6,7,8,11,12,13,14,15,16,17] := remove (a 17) 10 [0,1,2,3,5,6,7,8,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 17 ≠ 11 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 11 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,2,3,5,6,7,8,12,13,14,15,16,17] := remove (a 17) 11 [0,1,2,3,5,6,7,8,11,12,13,14,15,16,17] t3 b4
  have b5 : a 17 ≠ 12 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 12 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,2,3,5,6,7,8,13,14,15,16,17] := remove (a 17) 12 [0,1,2,3,5,6,7,8,12,13,14,15,16,17] t4 b5
  have b6 : a 17 ≠ 13 := exclude [0,2] (fun u v => edge r8 v u) (a 17) (a 1) 13 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,2,3,5,6,7,8,14,15,16,17] := remove (a 17) 13 [0,1,2,3,5,6,7,8,13,14,15,16,17] t5 b6
  have b7 : a 3 ≠ 4 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t7 : a 3 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 3) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d3 b7
  have b8 : a 3 ≠ 5 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r9 v u) (a 3) (a 2) 5 d2 c9 (by decide +kernel)
  have t8 : a 3 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 3) 5 [0,1,2,3,5,6,7,8,9,10,11] t7 b8
  have b9 : a 3 ≠ 6 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r9 v u) (a 3) (a 2) 6 d2 c9 (by decide +kernel)
  have t9 : a 3 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 3) 6 [0,1,2,3,6,7,8,9,10,11] t8 b9
  have b10 : a 3 ≠ 7 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r9 v u) (a 3) (a 2) 7 d2 c9 (by decide +kernel)
  have t10 : a 3 ∈ [0,1,2,3,8,9,10,11] := remove (a 3) 7 [0,1,2,3,7,8,9,10,11] t9 b10
  have b11 : a 6 ≠ 4 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 6) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b11
  have b12 : a 6 ≠ 5 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 6) 5 [0,1,2,3,5,6,7,8,9,10,11] t11 b12
  have b13 : a 6 ≠ 6 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 6) 6 [0,1,2,3,6,7,8,9,10,11] t12 b13
  have b14 : a 6 ≠ 7 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,2,3,8,9,10,11] := remove (a 6) 7 [0,1,2,3,7,8,9,10,11] t13 b14
  have b15 : a 10 ≠ 8 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b15
  exact And.intro t0 (And.intro t6 (And.intro t10 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,1,2,3,8,9,10,11])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,1,2,3,8,9,10,11])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,17,20,21,22,23] ∧ a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22] ∧ a 11 ∈ [0,1,2,3,4,6,7,8] := by
  have b0 : a 10 ≠ 9 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 12 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 12 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 12 [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 13 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,1,2,3,4,5,6,7,10,11,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 14 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 14 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,16,17,18,19,20,21,22,23] := remove (a 10) 14 [0,1,2,3,4,5,6,7,10,11,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 16 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,17,18,19,20,21,22,23] := remove (a 10) 16 [0,1,2,3,4,5,6,7,10,11,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 18 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 18 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,17,19,20,21,22,23] := remove (a 10) 18 [0,1,2,3,4,5,6,7,10,11,15,17,18,19,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 19 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r11 v u) (a 10) (a 2) 19 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,2,3,4,5,6,7,10,11,15,17,20,21,22,23] := remove (a 10) 19 [0,1,2,3,4,5,6,7,10,11,15,17,19,20,21,22,23] t5 b6
  have b7 : a 18 ≠ 4 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d18 b7
  have b8 : a 18 ≠ 5 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 18 ≠ 7 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,2,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 7 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 18 ≠ 8 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,2,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 8 [0,1,2,3,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 18 ≠ 9 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 9 [0,1,2,3,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 18 ≠ 16 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,17,18,19,20,21,22,23] := remove (a 18) 16 [0,1,2,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 18 ≠ 17 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 18) 17 [0,1,2,3,6,10,11,12,13,14,15,17,18,19,20,21,22,23] t12 b13
  have b14 : a 18 ≠ 23 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r12 v u) (a 18) (a 2) 23 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22] := remove (a 18) 23 [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22,23] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,2,3,4,6,7,8] := remove (a 11) 5 [0,1,2,3,4,5,6,7,8] d11 b15
  exact And.intro t6 (And.intro t14 (t15))

theorem chunk3 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,3,4,6,7,8])
    (d3 : a 3 ∈ [0,1,2,3,8,9,10,11])
    (d6 : a 6 ∈ [0,1,2,3,8,9,10,11])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 11 ∈ [0,1,2,3,4,7,8] ∧ a 6 ∈ [0,9] ∧ a 12 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 11 ≠ 6 := exclude [0,1,2,3,8,9,10,11] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,2,3,4,7,8] := remove (a 11) 6 [0,1,2,3,4,6,7,8] d11 b0
  have b1 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 1 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,3,8,9,10,11] := remove (a 6) 1 [0,1,2,3,8,9,10,11] d6 b1
  have b2 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t2 : a 6 ∈ [0,3,8,9,10,11] := remove (a 6) 2 [0,2,3,8,9,10,11] t1 b2
  have b3 : a 6 ≠ 3 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 3 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,8,9,10,11] := remove (a 6) 3 [0,3,8,9,10,11] t2 b3
  have b4 : a 6 ≠ 8 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 8 d4 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,9,10,11] := remove (a 6) 8 [0,8,9,10,11] t3 b4
  have b5 : a 6 ≠ 10 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 10 d4 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0,9,11] := remove (a 6) 10 [0,9,10,11] t4 b5
  have b6 : a 6 ≠ 11 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 11 d4 c17 (by decide +kernel)
  have t6 : a 6 ∈ [0,9] := remove (a 6) 11 [0,9,11] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b7
  have b8 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 6 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 7 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 12 ≠ 8 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 12 ≠ 9 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t6 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_191
