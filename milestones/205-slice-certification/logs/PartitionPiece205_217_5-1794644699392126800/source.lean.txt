import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,14,15,16,17])
    (d8 : a 8 ∈ [0,14])
    (d10 : a 10 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 9 ∈ [0,1,14,15] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0,2] ∧ a 12 ∈ [0,1] ∧ a 24 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 9 ≠ 16 := exclude [0,14] (fun u v => edge r28 v u) (a 9) (a 8) 16 d8 c28 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,14,15,17] := remove (a 9) 16 [0,1,14,15,16,17] d9 b0
  have b1 : a 9 ≠ 17 := exclude [0,14] (fun u v => edge r28 v u) (a 9) (a 8) 17 d8 c28 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,14,15] := remove (a 9) 17 [0,1,14,15,17] t0 b1
  have b2 : a 8 ≠ 14 := exclude [0,1,2] (edge r29) (a 8) (a 10) 14 d10 c29 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 14 [0,14] d8 b2
  have b3 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,2] := remove (a 10) 1 [0,1,2] d10 b3
  have b4 : a 12 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 2 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b4
  have b5 : a 12 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 3 t2 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t4 b5
  have b6 : a 12 ≠ 4 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 4 t2 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] t5 b6
  have b7 : a 12 ≠ 5 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 5 t2 c30 (by decide +kernel)
  have t7 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t6 b7
  have b8 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t2 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b8
  have b9 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 t2 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t2 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 t2 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 t2 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 7 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t2 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 8 [0,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 t2 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 9 [0,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 24 ≠ 10 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 10 t2 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 10 [0,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t7 (t15))))

theorem chunk21 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d8 : a 8 ∈ [0])
    (d9 : a 9 ∈ [0,1,14,15])
    (d11 : a 11 ∈ [0,4,7,8,9,10,11])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 24 ∈ [0,5,6,11,12,17,18,23] ∧ a 9 ∈ [0,14] ∧ a 11 ∈ [0] := by
  have b0 : a 24 ≠ 13 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,5,6,11,12,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 13 [0,5,6,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b0
  have b1 : a 24 ≠ 14 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,5,6,11,12,15,16,17,18,19,20,21,22,23] := remove (a 24) 14 [0,5,6,11,12,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 24 ≠ 15 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,5,6,11,12,16,17,18,19,20,21,22,23] := remove (a 24) 15 [0,5,6,11,12,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,5,6,11,12,17,18,19,20,21,22,23] := remove (a 24) 16 [0,5,6,11,12,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 24 ≠ 19 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 19 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,5,6,11,12,17,18,20,21,22,23] := remove (a 24) 19 [0,5,6,11,12,17,18,19,20,21,22,23] t3 b4
  have b5 : a 24 ≠ 20 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 20 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,5,6,11,12,17,18,21,22,23] := remove (a 24) 20 [0,5,6,11,12,17,18,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 21 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 21 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,5,6,11,12,17,18,22,23] := remove (a 24) 21 [0,5,6,11,12,17,18,21,22,23] t5 b6
  have b7 : a 24 ≠ 22 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 22 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,5,6,11,12,17,18,23] := remove (a 24) 22 [0,5,6,11,12,17,18,22,23] t6 b7
  have b8 : a 9 ≠ 1 := exclude [0,4,7,8,9,10,11] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t8 : a 9 ∈ [0,14,15] := remove (a 9) 1 [0,1,14,15] d9 b8
  have b9 : a 9 ≠ 15 := exclude [0,4,7,8,9,10,11] (edge r32) (a 9) (a 11) 15 d11 c32 (by decide +kernel)
  have t9 : a 9 ∈ [0,14] := remove (a 9) 15 [0,14,15] t8 b9
  have b10 : a 11 ≠ 4 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 4 t9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,7,8,9,10,11] := remove (a 11) 4 [0,4,7,8,9,10,11] d11 b10
  have b11 : a 11 ≠ 7 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 7 t9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,8,9,10,11] := remove (a 11) 7 [0,7,8,9,10,11] t10 b11
  have b12 : a 11 ≠ 8 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 8 t9 c32 (by decide +kernel)
  have t12 : a 11 ∈ [0,9,10,11] := remove (a 11) 8 [0,8,9,10,11] t11 b12
  have b13 : a 11 ≠ 9 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 9 t9 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,10,11] := remove (a 11) 9 [0,9,10,11] t12 b13
  have b14 : a 11 ≠ 10 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 10 t9 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,11] := remove (a 11) 10 [0,10,11] t13 b14
  have b15 : a 11 ≠ 11 := exclude [0,14] (fun u v => edge r32 v u) (a 11) (a 9) 11 t9 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0] := remove (a 11) 11 [0,11] t14 b15
  exact And.intro t7 (And.intro t9 (t15))

theorem chunk22 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,14])
    (d13 : a 13 ∈ [0,12])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 9 ∈ [0] ∧ a 25 ∈ [0,1,17,18,19,20,21,22,23] := by
  have b0 : a 9 ≠ 14 := exclude [0,12] (edge r33) (a 9) (a 13) 14 d13 c33 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 14 [0,14] d9 b0
  have b1 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 t0 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b1
  have b2 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 t0 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 4 t0 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 25 ≠ 5 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 5 t0 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 6 t0 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 25 ≠ 7 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 7 t0 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 8 t0 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 9 t0 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 t0 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 25 ≠ 11 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 11 t0 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 25 ≠ 12 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 12 t0 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 25 ≠ 13 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 13 t0 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 25 ≠ 14 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 14 t0 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 25) 14 [0,1,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 25 ≠ 15 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 15 t0 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 25) 15 [0,1,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 25 ≠ 16 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 16 t0 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 25) 16 [0,1,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

theorem chunk23 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,17,18,19,20,21,22,23])
    (d9 : a 9 ∈ [0])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 25 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 26 ∈ [0,7,10,11] := by
  have b0 : a 25 ≠ 17 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,18,19,20,21,22,23] := remove (a 25) 17 [0,1,17,18,19,20,21,22,23] d25 b0
  have b1 : a 25 ≠ 18 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 18 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,19,20,21,22,23] := remove (a 25) 18 [0,1,18,19,20,21,22,23] t0 b1
  have b2 : a 25 ≠ 19 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 19 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,20,21,22,23] := remove (a 25) 19 [0,1,19,20,21,22,23] t1 b2
  have b3 : a 25 ≠ 20 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 20 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,21,22,23] := remove (a 25) 20 [0,1,20,21,22,23] t2 b3
  have b4 : a 25 ≠ 21 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 21 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,22,23] := remove (a 25) 21 [0,1,21,22,23] t3 b4
  have b5 : a 25 ≠ 22 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 22 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,23] := remove (a 25) 22 [0,1,22,23] t4 b5
  have b6 : a 25 ≠ 23 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 23 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1] := remove (a 25) 23 [0,1,23] t5 b6
  have b7 : a 10 ≠ 2 := exclude [0] (edge r35) (a 10) (a 11) 2 d11 c35 (by decide +kernel)
  have t7 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b7
  have b8 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t7 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b8
  have b9 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t7 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t7 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t7 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,5,6,7,8,9,10,11] := remove (a 26) 4 [0,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 t7 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,6,7,8,9,10,11] := remove (a 26) 5 [0,5,6,7,8,9,10,11] t11 b12
  have b13 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 t7 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,7,8,9,10,11] := remove (a 26) 6 [0,6,7,8,9,10,11] t12 b13
  have b14 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 t7 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,7,9,10,11] := remove (a 26) 8 [0,7,8,9,10,11] t13 b14
  have b15 : a 26 ≠ 9 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 9 t7 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,7,10,11] := remove (a 26) 9 [0,7,9,10,11] t14 b15
  exact And.intro t6 (And.intro t7 (t15))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_217
