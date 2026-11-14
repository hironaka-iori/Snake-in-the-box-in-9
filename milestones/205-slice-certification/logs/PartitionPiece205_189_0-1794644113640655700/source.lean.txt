import PartitionData205_189
namespace PartitionCover205_189
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 8 ∈ [0,2,4,5] ∧ a 16 ∈ [0,1,6,7] := by
  have b0 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,2,3,4,5] := remove (a 8) 1 [0,1,2,3,4,5] d8 b0
  have b1 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,2,4,5] := remove (a 8) 3 [0,2,3,4,5] t0 b1
  have b2 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b2
  have b3 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 16) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 16) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 16) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 16) 11 [0,1,6,7,11,12,13,14,15,16,17] t8 b9
  have b10 : a 16 ≠ 12 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 12 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 16) 12 [0,1,6,7,12,13,14,15,16,17] t9 b10
  have b11 : a 16 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 13 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,6,7,14,15,16,17] := remove (a 16) 13 [0,1,6,7,13,14,15,16,17] t10 b11
  have b12 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,6,7,15,16,17] := remove (a 16) 14 [0,1,6,7,14,15,16,17] t11 b12
  have b13 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,6,7,16,17] := remove (a 16) 15 [0,1,6,7,15,16,17] t12 b13
  have b14 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,6,7,17] := remove (a 16) 16 [0,1,6,7,16,17] t13 b14
  have b15 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,6,7] := remove (a 16) 17 [0,1,6,7,17] t14 b15
  exact And.intro t1 (t15)

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 9 ∈ [0,2] ∧ a 17 ∈ [0,3] ∧ a 10 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b0
  have b1 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,2,4,5] := remove (a 9) 3 [0,2,3,4,5] t0 b1
  have b2 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,5] := remove (a 9) 4 [0,2,4,5] t1 b2
  have b3 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,2] := remove (a 9) 5 [0,2,5] t2 b3
  have b4 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,2,3,4,5,6,7,8] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8] d17 b4
  have b5 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,3,4,5,6,7,8] := remove (a 17) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,3,5,6,7,8] := remove (a 17) 4 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 17 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,3,6,7,8] := remove (a 17) 5 [0,3,5,6,7,8] t6 b7
  have b8 : a 17 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,3,7,8] := remove (a 17) 6 [0,3,6,7,8] t7 b8
  have b9 : a 17 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,8] := remove (a 17) 7 [0,3,7,8] t8 b9
  have b10 : a 17 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,3] := remove (a 17) 8 [0,3,8] t9 b10
  have b11 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b11
  have b12 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 10 ≠ 4 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t10 (t15))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 10 ∈ [0,6,11,18] ∧ a 18 ∈ [0,2] := by
  have b0 : a 10 ≠ 7 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 8 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 9 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 10 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 10 [0,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 12 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 12 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,6,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 12 [0,6,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 13 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,6,11,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,6,11,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 14 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 14 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,6,11,15,16,17,18,19,20,21,22,23] := remove (a 10) 14 [0,6,11,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 10 ≠ 15 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 15 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,6,11,16,17,18,19,20,21,22,23] := remove (a 10) 15 [0,6,11,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 10 ≠ 16 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,6,11,17,18,19,20,21,22,23] := remove (a 10) 16 [0,6,11,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 10 ≠ 17 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 17 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,6,11,18,19,20,21,22,23] := remove (a 10) 17 [0,6,11,17,18,19,20,21,22,23] t8 b9
  have b10 : a 10 ≠ 19 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 19 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,6,11,18,20,21,22,23] := remove (a 10) 19 [0,6,11,18,19,20,21,22,23] t9 b10
  have b11 : a 10 ≠ 20 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 20 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,6,11,18,21,22,23] := remove (a 10) 20 [0,6,11,18,20,21,22,23] t10 b11
  have b12 : a 10 ≠ 21 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 21 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,6,11,18,22,23] := remove (a 10) 21 [0,6,11,18,21,22,23] t11 b12
  have b13 : a 10 ≠ 22 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 22 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,6,11,18,23] := remove (a 10) 22 [0,6,11,18,22,23] t12 b13
  have b14 : a 10 ≠ 23 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 23 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,6,11,18] := remove (a 10) 23 [0,6,11,18,23] t13 b14
  have b15 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b15
  exact And.intro t14 (t15)

theorem chunk3 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2])
    (d2 : a 2 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0] ∧ a 11 ∈ [0,4,15,18,19,20,21,22,23] := by
  have b0 : a 18 ≠ 2 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b0
  have b1 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d11 b1
  have b2 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 8 [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,4,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 9 [0,4,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,4,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 10 [0,4,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,4,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 11 [0,4,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 11 ≠ 12 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 12 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,4,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 12 [0,4,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 11 ≠ 13 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 13 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,4,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 13 [0,4,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 11 ≠ 14 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 14 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,4,15,16,17,18,19,20,21,22,23] := remove (a 11) 14 [0,4,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 11 ≠ 16 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 16 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,4,15,17,18,19,20,21,22,23] := remove (a 11) 16 [0,4,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 11 ≠ 17 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 17 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,4,15,18,19,20,21,22,23] := remove (a 11) 17 [0,4,15,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_189
