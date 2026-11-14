import PartitionData205_192
namespace PartitionCover205_192
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,3,4,5,6,7,8,9])
    (d7 : a 7 ∈ [0,2,3,5])
    (d9 : a 9 ∈ [0,2,4,6,7,10])
    (d8 : a 8 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,12,13,16,17])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 15 ∈ [0,1,4,5,6,7,9] ∧ a 9 ∈ [0,4] ∧ a 10 ∈ [0,1,4,5] ∧ a 12 ∈ [0,1,4,5] := by
  have b0 : a 15 ≠ 3 := exclude [0,2,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5,6,7,8,9] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9] d15 b0
  have b1 : a 15 ≠ 8 := exclude [0,2,3,5] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,4,5,6,7,9] := remove (a 15) 8 [0,1,4,5,6,7,8,9] t0 b1
  have b2 : a 9 ≠ 2 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t2 : a 9 ∈ [0,4,6,7,10] := remove (a 9) 2 [0,2,4,6,7,10] d9 b2
  have b3 : a 9 ≠ 6 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0,4,7,10] := remove (a 9) 6 [0,4,6,7,10] t2 b3
  have b4 : a 9 ≠ 7 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 7 d8 c28 (by decide +kernel)
  have t4 : a 9 ∈ [0,4,10] := remove (a 9) 7 [0,4,7,10] t3 b4
  have b5 : a 9 ≠ 10 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 10 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,4] := remove (a 9) 10 [0,4,10] t4 b5
  have b6 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,3,4,5,6,7,12,13,16,17] := remove (a 10) 2 [0,1,2,3,4,5,6,7,12,13,16,17] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5,6,7,12,13,16,17] := remove (a 10) 3 [0,1,3,4,5,6,7,12,13,16,17] t6 b7
  have b8 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 6 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5,7,12,13,16,17] := remove (a 10) 6 [0,1,4,5,6,7,12,13,16,17] t7 b8
  have b9 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 7 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,4,5,12,13,16,17] := remove (a 10) 7 [0,1,4,5,7,12,13,16,17] t8 b9
  have b10 : a 10 ≠ 12 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 12 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,4,5,13,16,17] := remove (a 10) 12 [0,1,4,5,12,13,16,17] t9 b10
  have b11 : a 10 ≠ 13 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 13 d8 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,4,5,16,17] := remove (a 10) 13 [0,1,4,5,13,16,17] t10 b11
  have b12 : a 10 ≠ 16 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 16 d8 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,4,5,17] := remove (a 10) 16 [0,1,4,5,16,17] t11 b12
  have b13 : a 10 ≠ 17 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 17 d8 c29 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,4,5] := remove (a 10) 17 [0,1,4,5,17] t12 b13
  have b14 : a 12 ≠ 2 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 2 d8 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 3 d8 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t13 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,5])
    (d8 : a 8 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,1])
    (d9 : a 9 ∈ [0,4])
    (d13 : a 13 ∈ [0,2,4,6])
    (d10 : a 10 ∈ [0,1,4,5])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    : a 12 ∈ [0,1] ∧ a 24 ∈ [0,1] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0,4] ∧ a 10 ∈ [0,4,5] := by
  have b0 : a 12 ≠ 4 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 4 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 5 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t0 b1
  have b2 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 4 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 24) 4 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,6,7,8,9,10,11] := remove (a 24) 5 [0,1,5,6,7,8,9,10,11] t4 b5
  have b6 : a 24 ≠ 6 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,7,8,9,10,11] := remove (a 24) 6 [0,1,6,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 7 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,8,9,10,11] := remove (a 24) 7 [0,1,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 8 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,9,10,11] := remove (a 24) 8 [0,1,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 9 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,10,11] := remove (a 24) 9 [0,1,9,10,11] t8 b9
  have b10 : a 24 ≠ 10 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,11] := remove (a 24) 10 [0,1,10,11] t9 b10
  have b11 : a 24 ≠ 11 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1] := remove (a 24) 11 [0,1,11] t10 b11
  have b12 : a 11 ≠ 1 := exclude [0,4] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t12 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b12
  have b13 : a 13 ≠ 2 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,4,6] := remove (a 13) 2 [0,2,4,6] d13 b13
  have b14 : a 13 ≠ 6 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 6 d9 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0,4] := remove (a 13) 6 [0,4,6] t13 b14
  have b15 : a 10 ≠ 1 := exclude [0] (edge r35) (a 10) (a 11) 1 t12 c35 (by decide +kernel)
  have t15 : a 10 ∈ [0,4,5] := remove (a 10) 1 [0,1,4,5] d10 b15
  exact And.intro t1 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,4,5])
    (d11 : a 11 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 10 ∈ [0,4] ∧ a 14 ∈ [0,4,17] := by
  have b0 : a 10 ≠ 5 := exclude [0] (edge r35) (a 10) (a 11) 5 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0,4] := remove (a 10) 5 [0,4,5] d10 b0
  have b1 : a 14 ≠ 1 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 1 t0 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b1
  have b2 : a 14 ≠ 2 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 2 t0 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 3 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 3 t0 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 5 t0 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 6 t0 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 7 t0 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 8 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 8 t0 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 9 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 9 t0 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,4,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 10 t0 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,4,11,12,13,14,15,16,17] := remove (a 14) 10 [0,4,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 11 t0 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,4,12,13,14,15,16,17] := remove (a 14) 11 [0,4,11,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 12 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 12 t0 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,4,13,14,15,16,17] := remove (a 14) 12 [0,4,12,13,14,15,16,17] t10 b11
  have b12 : a 14 ≠ 13 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 13 t0 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,4,14,15,16,17] := remove (a 14) 13 [0,4,13,14,15,16,17] t11 b12
  have b13 : a 14 ≠ 14 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 14 t0 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,4,15,16,17] := remove (a 14) 14 [0,4,14,15,16,17] t12 b13
  have b14 : a 14 ≠ 15 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 15 t0 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,4,16,17] := remove (a 14) 15 [0,4,15,16,17] t13 b14
  have b15 : a 14 ≠ 16 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 16 t0 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,17] := remove (a 14) 16 [0,4,16,17] t14 b15
  exact And.intro t0 (t15)

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,17])
    (d10 : a 10 ∈ [0,4])
    (d15 : a 15 ∈ [0,1,4,5,6,7,9])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (d28 : a 28 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,4])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 14 ∈ [0,4] ∧ a 15 ∈ [0,6] ∧ a 27 ∈ [0,3] ∧ a 28 ∈ [0,1] ∧ a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 17 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 17 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,4] := remove (a 14) 17 [0,4,17] d14 b0
  have b1 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,4,5,6,7,9] := remove (a 15) 1 [0,1,4,5,6,7,9] d15 b1
  have b2 : a 15 ≠ 4 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,5,6,7,9] := remove (a 15) 4 [0,4,5,6,7,9] t1 b2
  have b3 : a 15 ≠ 5 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,6,7,9] := remove (a 15) 5 [0,5,6,7,9] t2 b3
  have b4 : a 15 ≠ 7 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,6,9] := remove (a 15) 7 [0,6,7,9] t3 b4
  have b5 : a 15 ≠ 9 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 9 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,6] := remove (a 15) 9 [0,6,9] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,2,3,4,5,6,7,8] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8] d27 b6
  have b7 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,3,4,5,6,7,8] := remove (a 27) 2 [0,2,3,4,5,6,7,8] t6 b7
  have b8 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,3,5,6,7,8] := remove (a 27) 4 [0,3,4,5,6,7,8] t7 b8
  have b9 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,3,6,7,8] := remove (a 27) 5 [0,3,5,6,7,8] t8 b9
  have b10 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,3,7,8] := remove (a 27) 6 [0,3,6,7,8] t9 b10
  have b11 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,3,8] := remove (a 27) 7 [0,3,7,8] t10 b11
  have b12 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,3] := remove (a 27) 8 [0,3,8] t11 b12
  have b13 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1] := remove (a 28) 2 [0,1,2] d28 b13
  have b14 : a 29 ≠ 2 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b14
  have b15 : a 29 ≠ 3 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t5 (And.intro t12 (And.intro t13 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_192
