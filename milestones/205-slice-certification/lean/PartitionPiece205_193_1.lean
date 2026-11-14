import PartitionData205_193
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,2,4,5,6,8,9,10,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,4])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,2,3,5])
    (d8 : a 8 ∈ [0,3])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,5,6])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 20 ∈ [0,2,4,5,6,8,10,11,12,14,16,17] ∧ a 13 ∈ [0,2,3,5] ∧ a 9 ∈ [0,3] ∧ a 10 ∈ [0,1,6,7] ∧ a 12 ∈ [0,6] := by
  have b0 : a 20 ≠ 9 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,2,4,5,6,8,10,11,12,13,14,15,16,17] := remove (a 20) 9 [0,2,4,5,6,8,9,10,11,12,13,14,15,16,17] d20 b0
  have b1 : a 20 ≠ 13 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,4,5,6,8,10,11,12,14,15,16,17] := remove (a 20) 13 [0,2,4,5,6,8,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 20 ≠ 15 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,2,4,5,6,8,10,11,12,14,16,17] := remove (a 20) 15 [0,2,4,5,6,8,10,11,12,14,15,16,17] t1 b2
  have b3 : a 13 ≠ 1 := exclude [0,1,2] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,2,3,4,5] := remove (a 13) 1 [0,1,2,3,4,5] d13 b3
  have b4 : a 13 ≠ 4 := exclude [0,1,2] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,3,5] := remove (a 13) 4 [0,2,3,4,5] t3 b4
  have b5 : a 9 ≠ 2 := exclude [0,3] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,3,5] := remove (a 9) 2 [0,2,3,5] d9 b5
  have b6 : a 9 ≠ 5 := exclude [0,3] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t6 : a 9 ∈ [0,3] := remove (a 9) 5 [0,3,5] t5 b6
  have b7 : a 10 ≠ 2 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b7
  have b8 : a 10 ≠ 3 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,1,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 10 ≠ 4 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 10) 4 [0,1,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 10 ≠ 5 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,6,7,8,9,10,11] := remove (a 10) 5 [0,1,5,6,7,8,9,10,11] t9 b10
  have b11 : a 10 ≠ 8 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 8 d8 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,6,7,9,10,11] := remove (a 10) 8 [0,1,6,7,8,9,10,11] t10 b11
  have b12 : a 10 ≠ 9 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 9 d8 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,6,7,10,11] := remove (a 10) 9 [0,1,6,7,9,10,11] t11 b12
  have b13 : a 10 ≠ 10 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 10 d8 c29 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,6,7,11] := remove (a 10) 10 [0,1,6,7,10,11] t12 b13
  have b14 : a 10 ≠ 11 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 11 d8 c29 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,6,7] := remove (a 10) 11 [0,1,6,7,11] t13 b14
  have b15 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 5 d8 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,6] := remove (a 12) 5 [0,5,6] d12 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (And.intro t14 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d8 : a 8 ∈ [0,3])
    (d11 : a 11 ∈ [0,2])
    (d9 : a 9 ∈ [0,3])
    (d13 : a 13 ∈ [0,2,3,5])
    (d10 : a 10 ∈ [0,1,6,7])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 24 ∈ [0,2] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0,3] ∧ a 10 ∈ [0,6] ∧ a 14 ∈ [0,4,5,6,7,8,9,10,11] := by
  have b0 : a 24 ≠ 1 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9] d24 b0
  have b1 : a 24 ≠ 3 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,4,5,6,7,8,9] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9] t0 b1
  have b2 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,5,6,7,8,9] := remove (a 24) 4 [0,2,4,5,6,7,8,9] t1 b2
  have b3 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,2,6,7,8,9] := remove (a 24) 5 [0,2,5,6,7,8,9] t2 b3
  have b4 : a 24 ≠ 6 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,7,8,9] := remove (a 24) 6 [0,2,6,7,8,9] t3 b4
  have b5 : a 24 ≠ 7 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2,8,9] := remove (a 24) 7 [0,2,7,8,9] t4 b5
  have b6 : a 24 ≠ 8 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,9] := remove (a 24) 8 [0,2,8,9] t5 b6
  have b7 : a 24 ≠ 9 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,2] := remove (a 24) 9 [0,2,9] t6 b7
  have b8 : a 11 ≠ 2 := exclude [0,3] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b8
  have b9 : a 13 ≠ 2 := exclude [0,3] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0,3,5] := remove (a 13) 2 [0,2,3,5] d13 b9
  have b10 : a 13 ≠ 5 := exclude [0,3] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t10 : a 13 ∈ [0,3] := remove (a 13) 5 [0,3,5] t9 b10
  have b11 : a 10 ≠ 1 := exclude [0] (edge r35) (a 10) (a 11) 1 t8 c35 (by decide +kernel)
  have t11 : a 10 ∈ [0,6,7] := remove (a 10) 1 [0,1,6,7] d10 b11
  have b12 : a 10 ≠ 7 := exclude [0] (edge r35) (a 10) (a 11) 7 t8 c35 (by decide +kernel)
  have t12 : a 10 ∈ [0,6] := remove (a 10) 7 [0,6,7] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 1 t12 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b13
  have b14 : a 14 ≠ 2 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 2 t12 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 14 ≠ 3 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 3 t12 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0,6])
    (d15 : a 15 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,6])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 14 ∈ [0,6] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0,3] ∧ a 28 ∈ [0,3] := by
  have b0 : a 14 ≠ 4 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,5,6,7,8,9,10,11] := remove (a 14) 4 [0,4,5,6,7,8,9,10,11] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,6,7,8,9,10,11] := remove (a 14) 5 [0,5,6,7,8,9,10,11] t0 b1
  have b2 : a 14 ≠ 7 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,6,8,9,10,11] := remove (a 14) 7 [0,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 8 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,6,9,10,11] := remove (a 14) 8 [0,6,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 9 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 9 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,6,10,11] := remove (a 14) 9 [0,6,9,10,11] t3 b4
  have b5 : a 14 ≠ 10 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,6,11] := remove (a 14) 10 [0,6,10,11] t4 b5
  have b6 : a 14 ≠ 11 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,6] := remove (a 14) 11 [0,6,11] t5 b6
  have b7 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b7
  have b8 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t7 b8
  have b9 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 3 [0,3] t8 b9
  have b10 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b10
  have b11 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,3,4,5] := remove (a 27) 2 [0,2,3,4,5] t10 b11
  have b12 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,3,5] := remove (a 27) 4 [0,3,4,5] t11 b12
  have b13 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,3] := remove (a 27) 5 [0,3,5] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b14
  have b15 : a 28 ≠ 2 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,3] := remove (a 28) 2 [0,2,3] t14 b15
  exact And.intro t6 (And.intro t9 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,3])
    (d12 : a 12 ∈ [0,6])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,3])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d14 : a 14 ∈ [0,6])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0,1,6,7] ∧ a 30 ∈ [0,6,9] := by
  have b0 : a 28 ≠ 3 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b0
  have b1 : a 29 ≠ 2 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b1
  have b2 : a 29 ≠ 3 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 29 ≠ 4 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 29 ≠ 5 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,6,7,8,9,10,11] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11] t3 b4
  have b5 : a 29 ≠ 8 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,6,7,9,10,11] := remove (a 29) 8 [0,1,6,7,8,9,10,11] t4 b5
  have b6 : a 29 ≠ 9 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,6,7,10,11] := remove (a 29) 9 [0,1,6,7,9,10,11] t5 b6
  have b7 : a 29 ≠ 10 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,6,7,11] := remove (a 29) 10 [0,1,6,7,10,11] t6 b7
  have b8 : a 29 ≠ 11 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,6,7] := remove (a 29) 11 [0,1,6,7,11] t7 b8
  have b9 : a 30 ≠ 1 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9] d30 b9
  have b10 : a 30 ≠ 2 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,3,4,5,6,7,8,9] := remove (a 30) 2 [0,2,3,4,5,6,7,8,9] t9 b10
  have b11 : a 30 ≠ 3 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,4,5,6,7,8,9] := remove (a 30) 3 [0,3,4,5,6,7,8,9] t10 b11
  have b12 : a 30 ≠ 4 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,5,6,7,8,9] := remove (a 30) 4 [0,4,5,6,7,8,9] t11 b12
  have b13 : a 30 ≠ 5 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,6,7,8,9] := remove (a 30) 5 [0,5,6,7,8,9] t12 b13
  have b14 : a 30 ≠ 7 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,6,8,9] := remove (a 30) 7 [0,6,7,8,9] t13 b14
  have b15 : a 30 ≠ 8 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,6,9] := remove (a 30) 8 [0,6,8,9] t14 b15
  exact And.intro t0 (And.intro t8 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_193
