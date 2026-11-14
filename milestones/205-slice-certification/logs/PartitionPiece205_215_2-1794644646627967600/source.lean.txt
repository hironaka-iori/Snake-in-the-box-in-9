import PartitionData205_215
namespace PartitionCover205_215
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,3])
    (d9 : a 9 ∈ [0,1,2,3,8,9,10,11])
    (d10 : a 10 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,3,4,7,18,21])
    (c27 : edge r27 (a 8) (a 22)=true)
    (c28 : edge r28 (a 9) (a 10)=true)
    (c30 : edge r30 (a 9) (a 23)=true)
    (c31 : edge r31 (a 10) (a 14)=true)
    : a 22 ∈ [0,1] ∧ a 9 ∈ [0] ∧ a 10 ∈ [0] ∧ a 23 ∈ [0] ∧ a 14 ∈ [0,3,21] := by
  have b0 : a 22 ≠ 2 := exclude [0,3] (fun u v => edge r27 v u) (a 22) (a 8) 2 d8 c27 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,3] := remove (a 22) 2 [0,1,2,3] d22 b0
  have b1 : a 22 ≠ 3 := exclude [0,3] (fun u v => edge r27 v u) (a 22) (a 8) 3 d8 c27 (by decide +kernel)
  have t1 : a 22 ∈ [0,1] := remove (a 22) 3 [0,1,3] t0 b1
  have b2 : a 9 ≠ 1 := exclude [0,2] (edge r28) (a 9) (a 10) 1 d10 c28 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,3,8,9,10,11] := remove (a 9) 1 [0,1,2,3,8,9,10,11] d9 b2
  have b3 : a 9 ≠ 2 := exclude [0,2] (edge r28) (a 9) (a 10) 2 d10 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0,3,8,9,10,11] := remove (a 9) 2 [0,2,3,8,9,10,11] t2 b3
  have b4 : a 9 ≠ 3 := exclude [0,2] (edge r28) (a 9) (a 10) 3 d10 c28 (by decide +kernel)
  have t4 : a 9 ∈ [0,8,9,10,11] := remove (a 9) 3 [0,3,8,9,10,11] t3 b4
  have b5 : a 9 ≠ 8 := exclude [0,2] (edge r28) (a 9) (a 10) 8 d10 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,9,10,11] := remove (a 9) 8 [0,8,9,10,11] t4 b5
  have b6 : a 9 ≠ 9 := exclude [0,2] (edge r28) (a 9) (a 10) 9 d10 c28 (by decide +kernel)
  have t6 : a 9 ∈ [0,10,11] := remove (a 9) 9 [0,9,10,11] t5 b6
  have b7 : a 9 ≠ 10 := exclude [0,2] (edge r28) (a 9) (a 10) 10 d10 c28 (by decide +kernel)
  have t7 : a 9 ∈ [0,11] := remove (a 9) 10 [0,10,11] t6 b7
  have b8 : a 9 ≠ 11 := exclude [0,2] (edge r28) (a 9) (a 10) 11 d10 c28 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 11 [0,11] t7 b8
  have b9 : a 10 ≠ 2 := exclude [0] (fun u v => edge r28 v u) (a 10) (a 9) 2 t8 c28 (by decide +kernel)
  have t9 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 23) (a 9) 1 t8 c30 (by decide +kernel)
  have t10 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b10
  have b11 : a 23 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 23) (a 9) 2 t8 c30 (by decide +kernel)
  have t11 : a 23 ∈ [0,3] := remove (a 23) 2 [0,2,3] t10 b11
  have b12 : a 23 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 23) (a 9) 3 t8 c30 (by decide +kernel)
  have t12 : a 23 ∈ [0] := remove (a 23) 3 [0,3] t11 b12
  have b13 : a 14 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 14) (a 10) 4 t9 c31 (by decide +kernel)
  have t13 : a 14 ∈ [0,3,7,18,21] := remove (a 14) 4 [0,3,4,7,18,21] d14 b13
  have b14 : a 14 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 14) (a 10) 7 t9 c31 (by decide +kernel)
  have t14 : a 14 ∈ [0,3,18,21] := remove (a 14) 7 [0,3,7,18,21] t13 b14
  have b15 : a 14 ≠ 18 := exclude [0] (fun u v => edge r31 v u) (a 14) (a 10) 18 t9 c31 (by decide +kernel)
  have t15 : a 14 ∈ [0,3,21] := remove (a 14) 18 [0,3,18,21] t14 b15
  exact And.intro t1 (And.intro t8 (And.intro t9 (And.intro t12 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,3,21])
    (d10 : a 10 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,3])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c31 : edge r31 (a 10) (a 14)=true)
    (c32 : edge r32 (a 10) (a 24)=true)
    (c33 : edge r33 (a 11) (a 12)=true)
    (c35 : edge r35 (a 11) (a 25)=true)
    (c36 : edge r36 (a 12) (a 14)=true)
    : a 14 ∈ [0,3] ∧ a 24 ∈ [0,1] ∧ a 11 ∈ [0,3] ∧ a 25 ∈ [0,8,10,11] ∧ a 12 ∈ [0] := by
  have b0 : a 14 ≠ 21 := exclude [0] (fun u v => edge r31 v u) (a 14) (a 10) 21 d10 c31 (by decide +kernel)
  have t0 : a 14 ∈ [0,3] := remove (a 14) 21 [0,3,21] d14 b0
  have b1 : a 24 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 24) (a 10) 2 d10 c32 (by decide +kernel)
  have t1 : a 24 ∈ [0,1,3,4,5] := remove (a 24) 2 [0,1,2,3,4,5] d24 b1
  have b2 : a 24 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 24) (a 10) 3 d10 c32 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,4,5] := remove (a 24) 3 [0,1,3,4,5] t1 b2
  have b3 : a 24 ≠ 4 := exclude [0] (fun u v => edge r32 v u) (a 24) (a 10) 4 d10 c32 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,5] := remove (a 24) 4 [0,1,4,5] t2 b3
  have b4 : a 24 ≠ 5 := exclude [0] (fun u v => edge r32 v u) (a 24) (a 10) 5 d10 c32 (by decide +kernel)
  have t4 : a 24 ∈ [0,1] := remove (a 24) 5 [0,1,5] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0,3] (edge r33) (a 11) (a 12) 1 d12 c33 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0,3] (edge r33) (a 11) (a 12) 2 d12 c33 (by decide +kernel)
  have t6 : a 11 ∈ [0,3] := remove (a 11) 2 [0,2,3] t5 b6
  have b7 : a 25 ≠ 1 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 1 t6 c35 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b7
  have b8 : a 25 ≠ 2 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 2 t6 c35 (by decide +kernel)
  have t8 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 25 ≠ 3 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 3 t6 c35 (by decide +kernel)
  have t9 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 25 ≠ 4 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 4 t6 c35 (by decide +kernel)
  have t10 : a 25 ∈ [0,5,6,7,8,9,10,11] := remove (a 25) 4 [0,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 25 ≠ 5 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 5 t6 c35 (by decide +kernel)
  have t11 : a 25 ∈ [0,6,7,8,9,10,11] := remove (a 25) 5 [0,5,6,7,8,9,10,11] t10 b11
  have b12 : a 25 ≠ 6 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 6 t6 c35 (by decide +kernel)
  have t12 : a 25 ∈ [0,7,8,9,10,11] := remove (a 25) 6 [0,6,7,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 7 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 7 t6 c35 (by decide +kernel)
  have t13 : a 25 ∈ [0,8,9,10,11] := remove (a 25) 7 [0,7,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 9 := exclude [0,3] (fun u v => edge r35 v u) (a 25) (a 11) 9 t6 c35 (by decide +kernel)
  have t14 : a 25 ∈ [0,8,10,11] := remove (a 25) 9 [0,8,9,10,11] t13 b14
  have b15 : a 12 ≠ 3 := exclude [0,3] (edge r36) (a 12) (a 14) 3 t0 c36 (by decide +kernel)
  have t15 : a 12 ∈ [0] := remove (a 12) 3 [0,3] d12 b15
  exact And.intro t0 (And.intro t4 (And.intro t6 (And.intro t14 (t15))))

theorem chunk10 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (c37 : edge r37 (a 12) (a 26)=true)
    : a 26 ∈ [0,17,18,19,20,21,22,23] := by
  have b0 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 1 d12 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 2 d12 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 3 d12 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 4 d12 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 5 d12 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 6 d12 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 7 d12 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 8 d12 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 9 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 9 d12 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 10 d12 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 11 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 11 d12 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 12 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 12 d12 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 12 [0,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 13 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 13 d12 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 13 [0,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 14 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 14 d12 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 15 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 15 d12 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 16 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 16 d12 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,17,18,19,20,21,22,23] := remove (a 26) 16 [0,16,17,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk11 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d13 : a 13 ∈ [0])
    (c37 : edge r37 (a 12) (a 26)=true)
    (c39 : edge r39 (a 13) (a 27)=true)
    : a 26 ∈ [0,19] ∧ a 27 ∈ [0,1,2,3,4,5,16,17] := by
  have b0 : a 26 ≠ 17 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 17 d12 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,18,19,20,21,22,23] := remove (a 26) 17 [0,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 18 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 18 d12 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,19,20,21,22,23] := remove (a 26) 18 [0,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 20 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 20 d12 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,19,21,22,23] := remove (a 26) 20 [0,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 21 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 21 d12 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,19,22,23] := remove (a 26) 21 [0,19,21,22,23] t2 b3
  have b4 : a 26 ≠ 22 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 22 d12 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,19,23] := remove (a 26) 22 [0,19,22,23] t3 b4
  have b5 : a 26 ≠ 23 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 12) 23 d12 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,19] := remove (a 26) 23 [0,19,23] t4 b5
  have b6 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 6 d13 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b6
  have b7 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 7 d13 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 8 d13 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] := remove (a 27) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 9 d13 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17] := remove (a 27) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 10 d13 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17] := remove (a 27) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 11 d13 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] := remove (a 27) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17] t10 b11
  have b12 : a 27 ≠ 12 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 12 d13 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,2,3,4,5,13,14,15,16,17] := remove (a 27) 12 [0,1,2,3,4,5,12,13,14,15,16,17] t11 b12
  have b13 : a 27 ≠ 13 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 13 d13 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,2,3,4,5,14,15,16,17] := remove (a 27) 13 [0,1,2,3,4,5,13,14,15,16,17] t12 b13
  have b14 : a 27 ≠ 14 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 14 d13 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,2,3,4,5,15,16,17] := remove (a 27) 14 [0,1,2,3,4,5,14,15,16,17] t13 b14
  have b15 : a 27 ≠ 15 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 15 d13 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,2,3,4,5,16,17] := remove (a 27) 15 [0,1,2,3,4,5,15,16,17] t14 b15
  exact And.intro t5 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_215
