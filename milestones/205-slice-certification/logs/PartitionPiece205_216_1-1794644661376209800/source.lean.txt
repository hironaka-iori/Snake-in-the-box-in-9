import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 9 ∈ [0,6,12] ∧ a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 9 ≠ 1 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d9 b0
  have b1 : a 9 ≠ 2 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 9 ≠ 3 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 9 ≠ 4 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 9 ≠ 5 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 9 ≠ 7 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 9 ≠ 8 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 9) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 9 ≠ 9 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 9) 9 [0,6,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 9 ≠ 10 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 10 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 9) 10 [0,6,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 9 ≠ 11 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 11 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,6,12,13,14,15,16,17] := remove (a 9) 11 [0,6,11,12,13,14,15,16,17] t8 b9
  have b10 : a 9 ≠ 13 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 13 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,6,12,14,15,16,17] := remove (a 9) 13 [0,6,12,13,14,15,16,17] t9 b10
  have b11 : a 9 ≠ 14 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 14 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,6,12,15,16,17] := remove (a 9) 14 [0,6,12,14,15,16,17] t10 b11
  have b12 : a 9 ≠ 15 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 15 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,6,12,16,17] := remove (a 9) 15 [0,6,12,15,16,17] t11 b12
  have b13 : a 9 ≠ 16 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 16 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,6,12,17] := remove (a 9) 16 [0,6,12,16,17] t12 b13
  have b14 : a 9 ≠ 17 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 17 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,6,12] := remove (a 9) 17 [0,6,12,17] t13 b14
  have b15 : a 17 ≠ 1 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b15
  exact And.intro t14 (t15)

theorem chunk5 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1,2])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 17 ∈ [0,3,4,8] ∧ a 2 ∈ [0,2] ∧ a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,20,21,22,23] := by
  have b0 : a 17 ≠ 2 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 17) 2 [0,2,3,4,5,6,7,8,9,10,11] d17 b0
  have b1 : a 17 ≠ 5 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,3,4,6,7,8,9,10,11] := remove (a 17) 5 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 17 ≠ 6 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,3,4,7,8,9,10,11] := remove (a 17) 6 [0,3,4,6,7,8,9,10,11] t1 b2
  have b3 : a 17 ≠ 7 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,3,4,8,9,10,11] := remove (a 17) 7 [0,3,4,7,8,9,10,11] t2 b3
  have b4 : a 17 ≠ 9 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,3,4,8,10,11] := remove (a 17) 9 [0,3,4,8,9,10,11] t3 b4
  have b5 : a 17 ≠ 10 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 10 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,3,4,8,11] := remove (a 17) 10 [0,3,4,8,10,11] t4 b5
  have b6 : a 17 ≠ 11 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 11 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,3,4,8] := remove (a 17) 11 [0,3,4,8,11] t5 b6
  have b7 : a 2 ≠ 1 := exclude [0,1,2] (edge r9) (a 2) (a 3) 1 d3 c9 (by decide +kernel)
  have t7 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b7
  have b8 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 6 t7 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b8
  have b9 : a 6 ≠ 7 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 7 t7 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 8 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 8 t7 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 6 ≠ 9 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 9 t7 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 6 ≠ 10 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 10 t7 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 6 ≠ 11 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 11 t7 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 6 ≠ 18 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 18 t7 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,19,20,21,22,23] := remove (a 6) 18 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 6 ≠ 19 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 19 t7 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,20,21,22,23] := remove (a 6) 19 [0,1,2,3,4,5,12,13,14,15,16,17,19,20,21,22,23] t14 b15
  exact And.intro t6 (And.intro t7 (t15))

theorem chunk6 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,20,21,22,23])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1,4,5,13,17,21,23])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    : a 6 ∈ [0,2,4,5,12,13,14,15,16,17] ∧ a 10 ∈ [0,3,7,11] ∧ a 4 ∈ [0,1,4,5,21,23] := by
  have b0 : a 6 ≠ 20 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 20 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,21,22,23] := remove (a 6) 20 [0,1,2,3,4,5,12,13,14,15,16,17,20,21,22,23] d6 b0
  have b1 : a 6 ≠ 21 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 21 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,22,23] := remove (a 6) 21 [0,1,2,3,4,5,12,13,14,15,16,17,21,22,23] t0 b1
  have b2 : a 6 ≠ 22 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 22 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,23] := remove (a 6) 22 [0,1,2,3,4,5,12,13,14,15,16,17,22,23] t1 b2
  have b3 : a 6 ≠ 23 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 23 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] := remove (a 6) 23 [0,1,2,3,4,5,12,13,14,15,16,17,23] t2 b3
  have b4 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b4
  have b5 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 10 ≠ 4 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 10) 4 [0,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,3,6,7,8,9,10,11] := remove (a 10) 5 [0,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,3,7,8,9,10,11] := remove (a 10) 6 [0,3,6,7,8,9,10,11] t7 b8
  have b9 : a 10 ≠ 8 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,3,7,9,10,11] := remove (a 10) 8 [0,3,7,8,9,10,11] t8 b9
  have b10 : a 10 ≠ 9 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,3,7,10,11] := remove (a 10) 9 [0,3,7,9,10,11] t9 b10
  have b11 : a 10 ≠ 10 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,3,7,11] := remove (a 10) 10 [0,3,7,10,11] t10 b11
  have b12 : a 4 ≠ 13 := exclude [0,1,2,3,4,5,12,13,14,15,16,17] (edge r17) (a 4) (a 6) 13 t3 c17 (by decide +kernel)
  have t12 : a 4 ∈ [0,1,4,5,17,21,23] := remove (a 4) 13 [0,1,4,5,13,17,21,23] d4 b12
  have b13 : a 4 ≠ 17 := exclude [0,1,2,3,4,5,12,13,14,15,16,17] (edge r17) (a 4) (a 6) 17 t3 c17 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,4,5,21,23] := remove (a 4) 17 [0,1,4,5,17,21,23] t12 b13
  have b14 : a 6 ≠ 1 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 1 t13 c17 (by decide +kernel)
  have t14 : a 6 ∈ [0,2,3,4,5,12,13,14,15,16,17] := remove (a 6) 1 [0,1,2,3,4,5,12,13,14,15,16,17] t3 b14
  have b15 : a 6 ≠ 3 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 3 t13 c17 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,4,5,12,13,14,15,16,17] := remove (a 6) 3 [0,2,3,4,5,12,13,14,15,16,17] t14 b15
  exact And.intro t15 (And.intro t11 (t13))

theorem chunk7 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,4,5,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,1,4,5,21,23])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 6 ∈ [0,2,12,14] ∧ a 12 ∈ [0,2,10,11,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 6 ≠ 4 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 4 d4 c17 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,5,12,13,14,15,16,17] := remove (a 6) 4 [0,2,4,5,12,13,14,15,16,17] d6 b0
  have b1 : a 6 ≠ 5 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 5 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,12,13,14,15,16,17] := remove (a 6) 5 [0,2,5,12,13,14,15,16,17] t0 b1
  have b2 : a 6 ≠ 13 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 13 d4 c17 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,12,14,15,16,17] := remove (a 6) 13 [0,2,12,13,14,15,16,17] t1 b2
  have b3 : a 6 ≠ 15 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 15 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,12,14,16,17] := remove (a 6) 15 [0,2,12,14,15,16,17] t2 b3
  have b4 : a 6 ≠ 16 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 16 d4 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,12,14,17] := remove (a 6) 16 [0,2,12,14,16,17] t3 b4
  have b5 : a 6 ≠ 17 := exclude [0,1,4,5,21,23] (fun u v => edge r17 v u) (a 6) (a 4) 17 d4 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,12,14] := remove (a 6) 17 [0,2,12,14,17] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b6
  have b7 : a 12 ≠ 3 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 4 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 5 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 6 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 7 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 8 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 9 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 12 ≠ 12 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 12 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 12 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 12 ≠ 13 := exclude [0,1,4,5,21,23] (fun u v => edge r18 v u) (a 12) (a 4) 13 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,2,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 13 [0,2,10,11,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t5 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_216
