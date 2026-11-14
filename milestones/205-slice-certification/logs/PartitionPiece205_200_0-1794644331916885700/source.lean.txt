import PartitionData205_200
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 2 ∈ [0,4] ∧ a 4 ∈ [0,1,2,4,5,6,7,8,9,10] ∧ a 8 ∈ [0,3,8,11,14,15,16,17] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5] := remove (a 2) 2 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5] := remove (a 2) 3 [0,3,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,4] := remove (a 2) 5 [0,4,5] t2 b3
  have b4 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 4) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d4 b4
  have b5 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,2,4,5,6,7,8,9,10] := remove (a 4) 11 [0,1,2,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d8 b6
  have b7 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,3,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 7 [0,3,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,3,8,10,11,12,13,14,15,16,17] := remove (a 8) 9 [0,3,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,3,8,11,12,13,14,15,16,17] := remove (a 8) 10 [0,3,8,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,3,8,11,13,14,15,16,17] := remove (a 8) 12 [0,3,8,11,12,13,14,15,16,17] t13 b14
  have b15 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,3,8,11,14,15,16,17] := remove (a 8) 13 [0,3,8,11,13,14,15,16,17] t14 b15
  exact And.intro t3 (And.intro t5 (t15))

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,3,8,11,14,15,16,17])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,4])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 8 ∈ [0,3,8,11,15,17] ∧ a 16 ∈ [0,1,2,3] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,4] ∧ a 10 ∈ [0,1,2,3,4] := by
  have b0 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,3,8,11,15,16,17] := remove (a 8) 14 [0,3,8,11,14,15,16,17] d8 b0
  have b1 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,3,8,11,15,17] := remove (a 8) 16 [0,3,8,11,15,16,17] t0 b1
  have b2 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,2,3,5] := remove (a 16) 4 [0,1,2,3,4,5] d16 b2
  have b3 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,2,3] := remove (a 16) 5 [0,1,2,3,5] t2 b3
  have b4 : a 3 ≠ 1 := exclude [0,4] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t4 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b4
  have b5 : a 6 ≠ 1 := exclude [0,4] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b5
  have b6 : a 6 ≠ 2 := exclude [0,4] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,3,4,5] := remove (a 6) 2 [0,2,3,4,5] t5 b6
  have b7 : a 6 ≠ 3 := exclude [0,4] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,4,5] := remove (a 6) 3 [0,3,4,5] t6 b7
  have b8 : a 6 ≠ 5 := exclude [0,4] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,2,3,4,6,7,8,9,10,11] := remove (a 10) 5 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b9
  have b10 : a 10 ≠ 6 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,2,3,4,7,8,9,10,11] := remove (a 10) 6 [0,1,2,3,4,6,7,8,9,10,11] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,2,3,4,8,9,10,11] := remove (a 10) 7 [0,1,2,3,4,7,8,9,10,11] t10 b11
  have b12 : a 10 ≠ 8 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,2,3,4,9,10,11] := remove (a 10) 8 [0,1,2,3,4,8,9,10,11] t11 b12
  have b13 : a 10 ≠ 9 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,2,3,4,10,11] := remove (a 10) 9 [0,1,2,3,4,9,10,11] t12 b13
  have b14 : a 10 ≠ 10 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,2,3,4,11] := remove (a 10) 10 [0,1,2,3,4,10,11] t13 b14
  have b15 : a 10 ≠ 11 := exclude [0,4] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,2,3,4] := remove (a 10) 11 [0,1,2,3,4,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t8 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0,4])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,2])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,4] ∧ a 11 ∈ [0,4,6,10,12,16] := by
  have b0 : a 18 ≠ 1 := exclude [0,4] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,3,4,5] := remove (a 18) 1 [0,1,2,3,4,5] d18 b0
  have b1 : a 18 ≠ 2 := exclude [0,4] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,3,4,5] := remove (a 18) 2 [0,2,3,4,5] t0 b1
  have b2 : a 18 ≠ 3 := exclude [0,4] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,4,5] := remove (a 18) 3 [0,3,4,5] t1 b2
  have b3 : a 18 ≠ 5 := exclude [0,4] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,4] := remove (a 18) 5 [0,4,5] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d11 b4
  have b5 : a 11 ≠ 2 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,4,6,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 7 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 11 ≠ 8 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,4,6,9,10,11,12,13,14,15,16,17] := remove (a 11) 8 [0,4,6,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 11 ≠ 9 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,4,6,10,11,12,13,14,15,16,17] := remove (a 11) 9 [0,4,6,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 11 ≠ 11 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,4,6,10,12,13,14,15,16,17] := remove (a 11) 11 [0,4,6,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 11 ≠ 13 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 13 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,4,6,10,12,14,15,16,17] := remove (a 11) 13 [0,4,6,10,12,13,14,15,16,17] t11 b12
  have b13 : a 11 ≠ 14 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 14 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,4,6,10,12,15,16,17] := remove (a 11) 14 [0,4,6,10,12,14,15,16,17] t12 b13
  have b14 : a 11 ≠ 15 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 15 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,4,6,10,12,16,17] := remove (a 11) 15 [0,4,6,10,12,15,16,17] t13 b14
  have b15 : a 11 ≠ 17 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 17 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,4,6,10,12,16] := remove (a 11) 17 [0,4,6,10,12,16,17] t14 b15
  exact And.intro t3 (t15)

theorem chunk3 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,4,5,6,7,8,9,10])
    (d6 : a 6 ∈ [0,4])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 4 ∈ [0,1,4,5,6,7,8,9] ∧ a 12 ∈ [0,1,2,3,4,7,16,19,22,23] := by
  have b0 : a 4 ≠ 2 := exclude [0,4] (edge r17) (a 4) (a 6) 2 d6 c17 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,4,5,6,7,8,9,10] := remove (a 4) 2 [0,1,2,4,5,6,7,8,9,10] d4 b0
  have b1 : a 4 ≠ 10 := exclude [0,4] (edge r17) (a 4) (a 6) 10 d6 c17 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,4,5,6,7,8,9] := remove (a 4) 10 [0,1,4,5,6,7,8,9,10] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 5 t1 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b2
  have b3 : a 12 ≠ 6 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 6 t1 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 12 ≠ 8 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 8 t1 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,2,3,4,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,1,2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 12 ≠ 9 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 9 t1 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,2,3,4,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,1,2,3,4,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 12 ≠ 10 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 10 t1 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,2,3,4,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 10 [0,1,2,3,4,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 12 ≠ 11 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 11 t1 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,2,3,4,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 11 [0,1,2,3,4,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 12 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 12 t1 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,2,3,4,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 12 [0,1,2,3,4,7,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 13 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 13 t1 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,2,3,4,7,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 13 [0,1,2,3,4,7,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 14 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 14 t1 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,2,3,4,7,15,16,17,18,19,20,21,22,23] := remove (a 12) 14 [0,1,2,3,4,7,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 15 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 15 t1 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,2,3,4,7,16,17,18,19,20,21,22,23] := remove (a 12) 15 [0,1,2,3,4,7,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 17 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 17 t1 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,2,3,4,7,16,18,19,20,21,22,23] := remove (a 12) 17 [0,1,2,3,4,7,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 18 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 18 t1 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,2,3,4,7,16,19,20,21,22,23] := remove (a 12) 18 [0,1,2,3,4,7,16,18,19,20,21,22,23] t12 b13
  have b14 : a 12 ≠ 20 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 20 t1 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,2,3,4,7,16,19,21,22,23] := remove (a 12) 20 [0,1,2,3,4,7,16,19,20,21,22,23] t13 b14
  have b15 : a 12 ≠ 21 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r18 v u) (a 12) (a 4) 21 t1 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,2,3,4,7,16,19,22,23] := remove (a 12) 21 [0,1,2,3,4,7,16,19,21,22,23] t14 b15
  exact And.intro t1 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_200
