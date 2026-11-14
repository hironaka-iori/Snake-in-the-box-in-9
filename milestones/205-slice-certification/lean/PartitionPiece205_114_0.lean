import PartitionData205_114
namespace PartitionCover205_114
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    : a 2 ∈ [0,6] ∧ a 9 ∈ [0,3] ∧ a 3 ∈ [0,3,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7] := remove (a 2) 1 [0,1,2,3,4,5,6,7] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2,4,5,6,7] := remove (a 2) 3 [0,2,3,4,5,6,7] t0 b1
  have b2 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,2,4,6,7] := remove (a 2) 5 [0,2,4,5,6,7] t1 b2
  have b3 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,2,4,6] := remove (a 2) 7 [0,2,4,6,7] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 1 d1 c6 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t5 : a 9 ∈ [0,3] := remove (a 9) 2 [0,2,3] t4 b5
  have b6 : a 2 ≠ 2 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r7) (a 2) (a 3) 2 d3 c7 (by decide +kernel)
  have t6 : a 2 ∈ [0,4,6] := remove (a 2) 2 [0,2,4,6] t3 b6
  have b7 : a 2 ≠ 4 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r7) (a 2) (a 3) 4 d3 c7 (by decide +kernel)
  have t7 : a 2 ∈ [0,6] := remove (a 2) 4 [0,4,6] t6 b7
  have b8 : a 3 ≠ 1 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 1 t7 c7 (by decide +kernel)
  have t8 : a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 3) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d3 b8
  have b9 : a 3 ≠ 2 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 2 t7 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 3) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 3 ≠ 4 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 4 t7 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 3) 4 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 3 ≠ 5 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 5 t7 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0,3,6,7,8,9,10,11] := remove (a 3) 5 [0,3,5,6,7,8,9,10,11] t10 b11
  have b12 : a 3 ≠ 6 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 6 t7 c7 (by decide +kernel)
  have t12 : a 3 ∈ [0,3,7,8,9,10,11] := remove (a 3) 6 [0,3,6,7,8,9,10,11] t11 b12
  have b13 : a 3 ≠ 7 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 7 t7 c7 (by decide +kernel)
  have t13 : a 3 ∈ [0,3,8,9,10,11] := remove (a 3) 7 [0,3,7,8,9,10,11] t12 b13
  have b14 : a 3 ≠ 8 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 8 t7 c7 (by decide +kernel)
  have t14 : a 3 ∈ [0,3,9,10,11] := remove (a 3) 8 [0,3,8,9,10,11] t13 b14
  have b15 : a 3 ≠ 9 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 9 t7 c7 (by decide +kernel)
  have t15 : a 3 ∈ [0,3,10,11] := remove (a 3) 9 [0,3,9,10,11] t14 b15
  exact And.intro t7 (And.intro t5 (t15))

theorem chunk1 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,3,10,11])
    (d2 : a 2 ∈ [0,6])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    : a 3 ∈ [0,3] ∧ a 6 ∈ [0,6] ∧ a 10 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 3 ≠ 10 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 10 d2 c7 (by decide +kernel)
  have t0 : a 3 ∈ [0,3,11] := remove (a 3) 10 [0,3,10,11] d3 b0
  have b1 : a 3 ≠ 11 := exclude [0,6] (fun u v => edge r7 v u) (a 3) (a 2) 11 d2 c7 (by decide +kernel)
  have t1 : a 3 ∈ [0,3] := remove (a 3) 11 [0,3,11] t0 b1
  have b2 : a 6 ≠ 1 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 1 d2 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,3,4,5,6,7] := remove (a 6) 1 [0,1,2,3,4,5,6,7] d6 b2
  have b3 : a 6 ≠ 2 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 2 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,3,4,5,6,7] := remove (a 6) 2 [0,2,3,4,5,6,7] t2 b3
  have b4 : a 6 ≠ 3 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 3 d2 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,4,5,6,7] := remove (a 6) 3 [0,3,4,5,6,7] t3 b4
  have b5 : a 6 ≠ 4 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 4 d2 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0,5,6,7] := remove (a 6) 4 [0,4,5,6,7] t4 b5
  have b6 : a 6 ≠ 5 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 5 d2 c8 (by decide +kernel)
  have t6 : a 6 ∈ [0,6,7] := remove (a 6) 5 [0,5,6,7] t5 b6
  have b7 : a 6 ≠ 7 := exclude [0,6] (fun u v => edge r8 v u) (a 6) (a 2) 7 d2 c8 (by decide +kernel)
  have t7 : a 6 ∈ [0,6] := remove (a 6) 7 [0,6,7] t6 b7
  have b8 : a 10 ≠ 4 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 4 d2 c9 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b8
  have b9 : a 10 ≠ 5 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 5 d2 c9 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 10 ≠ 6 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 6 d2 c9 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 7 d2 c9 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 10 ≠ 8 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 8 d2 c9 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 10 ≠ 9 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 9 d2 c9 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 10 ≠ 10 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 10 d2 c9 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 11 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 11 d2 c9 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t7 (t15))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,6])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,3])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    : a 10 ∈ [0,1,2,3,18,19,20,21] ∧ a 11 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 10 ≠ 12 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 12 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 12 [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 13 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 13 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,2,3,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 14 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 14 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,2,3,15,16,17,18,19,20,21,22,23] := remove (a 10) 14 [0,1,2,3,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 15 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 15 d2 c9 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,2,3,16,17,18,19,20,21,22,23] := remove (a 10) 15 [0,1,2,3,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 16 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 16 d2 c9 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,2,3,17,18,19,20,21,22,23] := remove (a 10) 16 [0,1,2,3,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 17 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 17 d2 c9 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,3,18,19,20,21,22,23] := remove (a 10) 17 [0,1,2,3,17,18,19,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 22 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 22 d2 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,2,3,18,19,20,21,23] := remove (a 10) 22 [0,1,2,3,18,19,20,21,22,23] t5 b6
  have b7 : a 10 ≠ 23 := exclude [0,6] (fun u v => edge r9 v u) (a 10) (a 2) 23 d2 c9 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,2,3,18,19,20,21] := remove (a 10) 23 [0,1,2,3,18,19,20,21,23] t6 b7
  have b8 : a 11 ≠ 1 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d11 b8
  have b9 : a 11 ≠ 2 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t9 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 11 ≠ 3 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t10 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 11 ≠ 4 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 4 d3 c11 (by decide +kernel)
  have t11 : a 11 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 11 ≠ 7 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 7 d3 c11 (by decide +kernel)
  have t12 : a 11 ∈ [0,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 7 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 11 ≠ 8 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 8 d3 c11 (by decide +kernel)
  have t13 : a 11 ∈ [0,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 8 [0,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 11 ≠ 9 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 9 d3 c11 (by decide +kernel)
  have t14 : a 11 ∈ [0,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 9 [0,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 11 ≠ 10 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 10 d3 c11 (by decide +kernel)
  have t15 : a 11 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 10 [0,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (t15)

theorem chunk3 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,3])
    (d4 : a 4 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 11 ∈ [0,5,6,12,18,23] ∧ a 4 ∈ [0,3] ∧ a 5 ∈ [0,3] ∧ a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := by
  have b0 : a 11 ≠ 11 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 11 d3 c11 (by decide +kernel)
  have t0 : a 11 ∈ [0,5,6,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 11 [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] d11 b0
  have b1 : a 11 ≠ 13 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 13 d3 c11 (by decide +kernel)
  have t1 : a 11 ∈ [0,5,6,12,14,15,16,17,18,19,20,21,22,23] := remove (a 11) 13 [0,5,6,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 11 ≠ 14 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 14 d3 c11 (by decide +kernel)
  have t2 : a 11 ∈ [0,5,6,12,15,16,17,18,19,20,21,22,23] := remove (a 11) 14 [0,5,6,12,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 11 ≠ 15 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 15 d3 c11 (by decide +kernel)
  have t3 : a 11 ∈ [0,5,6,12,16,17,18,19,20,21,22,23] := remove (a 11) 15 [0,5,6,12,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 11 ≠ 16 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 16 d3 c11 (by decide +kernel)
  have t4 : a 11 ∈ [0,5,6,12,17,18,19,20,21,22,23] := remove (a 11) 16 [0,5,6,12,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 11 ≠ 17 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 17 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0,5,6,12,18,19,20,21,22,23] := remove (a 11) 17 [0,5,6,12,17,18,19,20,21,22,23] t4 b5
  have b6 : a 11 ≠ 19 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 19 d3 c11 (by decide +kernel)
  have t6 : a 11 ∈ [0,5,6,12,18,20,21,22,23] := remove (a 11) 19 [0,5,6,12,18,19,20,21,22,23] t5 b6
  have b7 : a 11 ≠ 20 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 20 d3 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0,5,6,12,18,21,22,23] := remove (a 11) 20 [0,5,6,12,18,20,21,22,23] t6 b7
  have b8 : a 11 ≠ 21 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 21 d3 c11 (by decide +kernel)
  have t8 : a 11 ∈ [0,5,6,12,18,22,23] := remove (a 11) 21 [0,5,6,12,18,21,22,23] t7 b8
  have b9 : a 11 ≠ 22 := exclude [0,3] (fun u v => edge r11 v u) (a 11) (a 3) 22 d3 c11 (by decide +kernel)
  have t9 : a 11 ∈ [0,5,6,12,18,23] := remove (a 11) 22 [0,5,6,12,18,22,23] t8 b9
  have b10 : a 4 ≠ 1 := exclude [0,1,2,3] (edge r12) (a 4) (a 5) 1 d5 c12 (by decide +kernel)
  have t10 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b10
  have b11 : a 4 ≠ 2 := exclude [0,1,2,3] (edge r12) (a 4) (a 5) 2 d5 c12 (by decide +kernel)
  have t11 : a 4 ∈ [0,3] := remove (a 4) 2 [0,2,3] t10 b11
  have b12 : a 5 ≠ 1 := exclude [0,3] (fun u v => edge r12 v u) (a 5) (a 4) 1 t11 c12 (by decide +kernel)
  have t12 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b12
  have b13 : a 5 ≠ 2 := exclude [0,3] (fun u v => edge r12 v u) (a 5) (a 4) 2 t11 c12 (by decide +kernel)
  have t13 : a 5 ∈ [0,3] := remove (a 5) 2 [0,2,3] t12 b13
  have b14 : a 12 ≠ 1 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 1 t11 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] d12 b14
  have b15 : a 12 ≠ 2 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 2 t11 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t14 b15
  exact And.intro t9 (And.intro t11 (And.intro t13 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_114
