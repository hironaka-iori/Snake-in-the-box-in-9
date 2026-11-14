import PartitionData205_202
namespace PartitionCover205_202
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    : a 2 ∈ [0,2,6,8] ∧ a 4 ∈ [0,2,12,14,15,16,17,18,19] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2,4,5,6,7,8] := remove (a 2) 3 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,2,5,6,7,8] := remove (a 2) 4 [0,2,4,5,6,7,8] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,2,6,7,8] := remove (a 2) 5 [0,2,5,6,7,8] t2 b3
  have b4 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,2,6,8] := remove (a 2) 7 [0,2,6,7,8] t3 b4
  have b5 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d4 b5
  have b6 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,2,10,11,12,13,14,15,16,17,18,19] := remove (a 4) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,2,11,12,13,14,15,16,17,18,19] := remove (a 4) 10 [0,2,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t14 : a 4 ∈ [0,2,12,13,14,15,16,17,18,19] := remove (a 4) 11 [0,2,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 4 ≠ 13 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 13 d0 c2 (by decide +kernel)
  have t15 : a 4 ∈ [0,2,12,14,15,16,17,18,19] := remove (a 4) 13 [0,2,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t4 (t15)

theorem chunk1 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,2,12,14,15,16,17,18,19])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,2,6,8])
    (d6 : a 6 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 4 ∈ [0,2,12,14] ∧ a 5 ∈ [0,2,6,7] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,2] ∧ a 2 ∈ [0,6,8] := by
  have b0 : a 4 ≠ 15 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 15 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,12,14,16,17,18,19] := remove (a 4) 15 [0,2,12,14,15,16,17,18,19] d4 b0
  have b1 : a 4 ≠ 16 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 16 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,12,14,17,18,19] := remove (a 4) 16 [0,2,12,14,16,17,18,19] t0 b1
  have b2 : a 4 ≠ 17 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 17 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,12,14,18,19] := remove (a 4) 17 [0,2,12,14,17,18,19] t1 b2
  have b3 : a 4 ≠ 18 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 18 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,12,14,19] := remove (a 4) 18 [0,2,12,14,18,19] t2 b3
  have b4 : a 4 ≠ 19 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 19 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,12,14] := remove (a 4) 19 [0,2,12,14,19] t3 b4
  have b5 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9] d5 b5
  have b6 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,4,5,6,7,8,9] := remove (a 5) 3 [0,2,3,4,5,6,7,8,9] t5 b6
  have b7 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,2,5,6,7,8,9] := remove (a 5) 4 [0,2,4,5,6,7,8,9] t6 b7
  have b8 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,6,7,8,9] := remove (a 5) 5 [0,2,5,6,7,8,9] t7 b8
  have b9 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,2,6,7,9] := remove (a 5) 8 [0,2,6,7,8,9] t8 b9
  have b10 : a 5 ≠ 9 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 9 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,2,6,7] := remove (a 5) 9 [0,2,6,7,9] t9 b10
  have b11 : a 3 ≠ 1 := exclude [0,2,6,8] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t11 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b11
  have b12 : a 3 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t12 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t11 b12
  have b13 : a 6 ≠ 1 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b13
  have b14 : a 6 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t13 b14
  have b15 : a 2 ≠ 2 := exclude [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (edge r11) (a 2) (a 10) 2 d10 c11 (by decide +kernel)
  have t15 : a 2 ∈ [0,6,8] := remove (a 2) 2 [0,2,6,8] d2 b15
  exact And.intro t4 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,6,8])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 2 ∈ [0,6] ∧ a 10 ∈ [0,2,8,10] ∧ a 18 ∈ [0,4,5,6,7] := by
  have b0 : a 2 ≠ 8 := exclude [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (edge r11) (a 2) (a 10) 8 d10 c11 (by decide +kernel)
  have t0 : a 2 ∈ [0,6] := remove (a 2) 8 [0,6,8] d2 b0
  have b1 : a 10 ≠ 1 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 1 t0 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d10 b1
  have b2 : a 10 ≠ 3 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 3 t0 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] t1 b2
  have b3 : a 10 ≠ 4 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 4 t0 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15] t2 b3
  have b4 : a 10 ≠ 5 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 5 t0 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,2,6,7,8,9,10,11,12,13,14,15] := remove (a 10) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15] t3 b4
  have b5 : a 10 ≠ 6 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 6 t0 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,2,7,8,9,10,11,12,13,14,15] := remove (a 10) 6 [0,2,6,7,8,9,10,11,12,13,14,15] t4 b5
  have b6 : a 10 ≠ 7 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 7 t0 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,8,9,10,11,12,13,14,15] := remove (a 10) 7 [0,2,7,8,9,10,11,12,13,14,15] t5 b6
  have b7 : a 10 ≠ 9 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 9 t0 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,8,10,11,12,13,14,15] := remove (a 10) 9 [0,2,8,9,10,11,12,13,14,15] t6 b7
  have b8 : a 10 ≠ 11 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 11 t0 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,8,10,12,13,14,15] := remove (a 10) 11 [0,2,8,10,11,12,13,14,15] t7 b8
  have b9 : a 10 ≠ 12 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 12 t0 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,2,8,10,13,14,15] := remove (a 10) 12 [0,2,8,10,12,13,14,15] t8 b9
  have b10 : a 10 ≠ 13 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 13 t0 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,2,8,10,14,15] := remove (a 10) 13 [0,2,8,10,13,14,15] t9 b10
  have b11 : a 10 ≠ 14 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 14 t0 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,2,8,10,15] := remove (a 10) 14 [0,2,8,10,14,15] t10 b11
  have b12 : a 10 ≠ 15 := exclude [0,6] (fun u v => edge r11 v u) (a 10) (a 2) 15 t0 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,2,8,10] := remove (a 10) 15 [0,2,8,10,15] t11 b12
  have b13 : a 18 ≠ 1 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 1 t0 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,3,4,5,6,7] := remove (a 18) 1 [0,1,2,3,4,5,6,7] d18 b13
  have b14 : a 18 ≠ 2 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 2 t0 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,3,4,5,6,7] := remove (a 18) 2 [0,2,3,4,5,6,7] t13 b14
  have b15 : a 18 ≠ 3 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 3 t0 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,4,5,6,7] := remove (a 18) 3 [0,3,4,5,6,7] t14 b15
  exact And.intro t0 (And.intro t12 (t15))

theorem chunk3 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,4,5,6,7])
    (d2 : a 2 ∈ [0,6])
    (d7 : a 7 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (d19 : a 19 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,2,12,14])
    (d5 : a 5 ∈ [0,2,6,7])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    : a 18 ∈ [0,4] ∧ a 7 ∈ [0,2] ∧ a 11 ∈ [0,4] ∧ a 19 ∈ [0,2] ∧ a 4 ∈ [0,12] ∧ a 5 ∈ [0,6,7] := by
  have b0 : a 18 ≠ 5 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,4,6,7] := remove (a 18) 5 [0,4,5,6,7] d18 b0
  have b1 : a 18 ≠ 6 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,4,7] := remove (a 18) 6 [0,4,6,7] t0 b1
  have b2 : a 18 ≠ 7 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,4] := remove (a 18) 7 [0,4,7] t1 b2
  have b3 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b3
  have b4 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 d3 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3,4,5,6,7] := remove (a 11) 1 [0,1,2,3,4,5,6,7] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,5,6,7] := remove (a 11) 2 [0,2,3,4,5,6,7] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,5,6,7] := remove (a 11) 3 [0,3,4,5,6,7] t6 b7
  have b8 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,4,6,7] := remove (a 11) 5 [0,4,5,6,7] t7 b8
  have b9 : a 11 ≠ 6 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,4,7] := remove (a 11) 6 [0,4,6,7] t8 b9
  have b10 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,4] := remove (a 11) 7 [0,4,7] t9 b10
  have b11 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b11
  have b12 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,2] := remove (a 19) 3 [0,2,3] t11 b12
  have b13 : a 4 ≠ 2 := exclude [0,2,6,7] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t13 : a 4 ∈ [0,12,14] := remove (a 4) 2 [0,2,12,14] d4 b13
  have b14 : a 4 ≠ 14 := exclude [0,2,6,7] (edge r16) (a 4) (a 5) 14 d5 c16 (by decide +kernel)
  have t14 : a 4 ∈ [0,12] := remove (a 4) 14 [0,12,14] t13 b14
  have b15 : a 5 ≠ 2 := exclude [0,12] (fun u v => edge r16 v u) (a 5) (a 4) 2 t14 c16 (by decide +kernel)
  have t15 : a 5 ∈ [0,6,7] := remove (a 5) 2 [0,2,6,7] d5 b15
  exact And.intro t2 (And.intro t4 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_202
