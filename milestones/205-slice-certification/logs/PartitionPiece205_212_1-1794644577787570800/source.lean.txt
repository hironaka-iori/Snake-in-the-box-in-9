import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,4,5,6,7,8])
    (d1 : a 1 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,4,8,14])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 9 ∈ [0,6] ∧ a 17 ∈ [0,6] ∧ a 6 ∈ [0,1,2,4,5,7,8,9,10,11] := by
  have b0 : a 9 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,5,6,7,8] := remove (a 9) 4 [0,4,5,6,7,8] d9 b0
  have b1 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,6,7,8] := remove (a 9) 5 [0,5,6,7,8] t0 b1
  have b2 : a 9 ≠ 7 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,6,8] := remove (a 9) 7 [0,6,7,8] t1 b2
  have b3 : a 9 ≠ 8 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,6] := remove (a 9) 8 [0,6,8] t2 b3
  have b4 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b4
  have b5 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 17) 2 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 17) 3 [0,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,5,6,7,8,9,10,11] := remove (a 17) 4 [0,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,6,7,8,9,10,11] := remove (a 17) 5 [0,5,6,7,8,9,10,11] t7 b8
  have b9 : a 17 ≠ 7 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,6,8,9,10,11] := remove (a 17) 7 [0,6,7,8,9,10,11] t8 b9
  have b10 : a 17 ≠ 8 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,6,9,10,11] := remove (a 17) 8 [0,6,8,9,10,11] t9 b10
  have b11 : a 17 ≠ 9 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,6,10,11] := remove (a 17) 9 [0,6,9,10,11] t10 b11
  have b12 : a 17 ≠ 10 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 10 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0,6,11] := remove (a 17) 10 [0,6,10,11] t11 b12
  have b13 : a 17 ≠ 11 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 11 d1 c8 (by decide +kernel)
  have t13 : a 17 ∈ [0,6] := remove (a 17) 11 [0,6,11] t12 b13
  have b14 : a 6 ≠ 3 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 6) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b14
  have b15 : a 6 ≠ 6 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,2,4,5,7,8,9,10,11] := remove (a 6) 6 [0,1,2,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t13 (t15))

theorem chunk5 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,2,4,5,7,8,9,10,11])
    (d2 : a 2 ∈ [0,4,8,14])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 6 ∈ [0,1,2,4,5,10] ∧ a 10 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := by
  have b0 : a 6 ≠ 7 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,2,4,5,8,9,10,11] := remove (a 6) 7 [0,1,2,4,5,7,8,9,10,11] d6 b0
  have b1 : a 6 ≠ 8 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,2,4,5,9,10,11] := remove (a 6) 8 [0,1,2,4,5,8,9,10,11] t0 b1
  have b2 : a 6 ≠ 9 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 9 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,2,4,5,10,11] := remove (a 6) 9 [0,1,2,4,5,9,10,11] t1 b2
  have b3 : a 6 ≠ 11 := exclude [0,4,8,14] (fun u v => edge r10 v u) (a 6) (a 2) 11 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,2,4,5,10] := remove (a 6) 11 [0,1,2,4,5,10,11] t2 b3
  have b4 : a 10 ≠ 2 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b4
  have b5 : a 10 ≠ 3 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 6 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 10 ≠ 7 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 10 ≠ 8 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 10 ≠ 9 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 10 ≠ 10 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 10 ≠ 11 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 10 ≠ 12 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 12 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 10 ≠ 13 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 10 ≠ 14 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 14 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 10) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 10 ≠ 15 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 15 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 10) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,4,5,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,4,8,14])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 10 ∈ [0,1,4,5] ∧ a 18 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 10 ≠ 16 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 10) 16 [0,1,4,5,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 17 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 17 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 10) 17 [0,1,4,5,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 18 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 18 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 10) 18 [0,1,4,5,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 19 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 19 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,4,5,20,21,22,23] := remove (a 10) 19 [0,1,4,5,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 20 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 20 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,4,5,21,22,23] := remove (a 10) 20 [0,1,4,5,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 21 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 21 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,4,5,22,23] := remove (a 10) 21 [0,1,4,5,21,22,23] t4 b5
  have b6 : a 10 ≠ 22 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 22 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,4,5,23] := remove (a 10) 22 [0,1,4,5,22,23] t5 b6
  have b7 : a 10 ≠ 23 := exclude [0,4,8,14] (fun u v => edge r11 v u) (a 10) (a 2) 23 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5] := remove (a 10) 23 [0,1,4,5,23] t6 b7
  have b8 : a 18 ≠ 2 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d18 b8
  have b9 : a 18 ≠ 3 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 18 ≠ 4 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 18 ≠ 5 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 18 ≠ 8 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 18 ≠ 9 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 18 ≠ 10 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 10 [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 18 ≠ 11 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 11 [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (t15)

theorem chunk7 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,4,8,14])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,1,6,7] ∧ a 11 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 18 ≠ 12 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 12 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 12 [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] d18 b0
  have b1 : a 18 ≠ 13 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,6,7,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 13 [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 18 ≠ 14 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 14 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,6,7,15,16,17,18,19,20,21,22,23] := remove (a 18) 14 [0,1,6,7,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 18 ≠ 15 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,6,7,16,17,18,19,20,21,22,23] := remove (a 18) 15 [0,1,6,7,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 18 ≠ 16 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,6,7,17,18,19,20,21,22,23] := remove (a 18) 16 [0,1,6,7,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 18 ≠ 17 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,6,7,18,19,20,21,22,23] := remove (a 18) 17 [0,1,6,7,17,18,19,20,21,22,23] t4 b5
  have b6 : a 18 ≠ 18 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 18 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,6,7,19,20,21,22,23] := remove (a 18) 18 [0,1,6,7,18,19,20,21,22,23] t5 b6
  have b7 : a 18 ≠ 19 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 19 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,6,7,20,21,22,23] := remove (a 18) 19 [0,1,6,7,19,20,21,22,23] t6 b7
  have b8 : a 18 ≠ 20 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 20 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,6,7,21,22,23] := remove (a 18) 20 [0,1,6,7,20,21,22,23] t7 b8
  have b9 : a 18 ≠ 21 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 21 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,6,7,22,23] := remove (a 18) 21 [0,1,6,7,21,22,23] t8 b9
  have b10 : a 18 ≠ 22 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 22 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,6,7,23] := remove (a 18) 22 [0,1,6,7,22,23] t9 b10
  have b11 : a 18 ≠ 23 := exclude [0,4,8,14] (fun u v => edge r12 v u) (a 18) (a 2) 23 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,6,7] := remove (a 18) 23 [0,1,6,7,23] t10 b11
  have b12 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d11 b12
  have b13 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t11 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_212
