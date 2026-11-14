import PartitionData205_207
namespace PartitionCover205_207
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19])
    (d7 : a 7 ∈ [0,3])
    (d9 : a 9 ∈ [0,2,4,6,8,10])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,5,7])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,2,3,6,7,10,11])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 23 ∈ [0,1,2,3,5,7,9,11,13,15,17,19] ∧ a 9 ∈ [0,2] ∧ a 12 ∈ [0,1] ∧ a 24 ∈ [0,1] ∧ a 11 ∈ [0,2,6,7,10,11] := by
  have b0 : a 23 ≠ 12 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 12 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,5,7,9,11,13,14,15,16,17,18,19] := remove (a 23) 12 [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19] d23 b0
  have b1 : a 23 ≠ 14 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 14 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,5,7,9,11,13,15,16,17,18,19] := remove (a 23) 14 [0,1,2,3,5,7,9,11,13,14,15,16,17,18,19] t0 b1
  have b2 : a 23 ≠ 16 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 16 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,2,3,5,7,9,11,13,15,17,18,19] := remove (a 23) 16 [0,1,2,3,5,7,9,11,13,15,16,17,18,19] t1 b2
  have b3 : a 23 ≠ 18 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 18 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,3,5,7,9,11,13,15,17,19] := remove (a 23) 18 [0,1,2,3,5,7,9,11,13,15,17,18,19] t2 b3
  have b4 : a 9 ≠ 4 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,6,8,10] := remove (a 9) 4 [0,2,4,6,8,10] d9 b4
  have b5 : a 9 ≠ 6 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,2,8,10] := remove (a 9) 6 [0,2,6,8,10] t4 b5
  have b6 : a 9 ≠ 8 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 8 d8 c28 (by decide +kernel)
  have t6 : a 9 ∈ [0,2,10] := remove (a 9) 8 [0,2,8,10] t5 b6
  have b7 : a 9 ≠ 10 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 10 d8 c28 (by decide +kernel)
  have t7 : a 9 ∈ [0,2] := remove (a 9) 10 [0,2,10] t6 b7
  have b8 : a 12 ≠ 5 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 5 d8 c30 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,7] := remove (a 12) 5 [0,1,5,7] d12 b8
  have b9 : a 12 ≠ 7 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [0,1] := remove (a 12) 7 [0,1,7] t8 b9
  have b10 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,3,4,5] := remove (a 24) 2 [0,1,2,3,4,5] d24 b10
  have b11 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,4,5] := remove (a 24) 3 [0,1,3,4,5] t10 b11
  have b12 : a 24 ≠ 4 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,5] := remove (a 24) 4 [0,1,4,5] t11 b12
  have b13 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,1] := remove (a 24) 5 [0,1,5] t12 b13
  have b14 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 1 t7 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,3,6,7,10,11] := remove (a 11) 1 [0,1,2,3,6,7,10,11] d11 b14
  have b15 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 3 t7 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,6,7,10,11] := remove (a 11) 3 [0,2,3,6,7,10,11] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t9 (And.intro t13 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,6,7,10,11])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,3,5,6,11,12,17])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 11 ∈ [0,2] ∧ a 13 ∈ [0,1] ∧ a 14 ∈ [0,1] ∧ a 26 ∈ [0,1,4,5] := by
  have b0 : a 11 ≠ 6 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 6 d9 c32 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,7,10,11] := remove (a 11) 6 [0,2,6,7,10,11] d11 b0
  have b1 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,10,11] := remove (a 11) 7 [0,2,7,10,11] t0 b1
  have b2 : a 11 ≠ 10 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 10 d9 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,11] := remove (a 11) 10 [0,2,10,11] t1 b2
  have b3 : a 11 ≠ 11 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 11 d9 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,2] := remove (a 11) 11 [0,2,11] t2 b3
  have b4 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t4 b5
  have b6 : a 13 ≠ 4 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] t5 b6
  have b7 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t7 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t6 b7
  have b8 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,5,6,11,12,17] := remove (a 14) 3 [0,1,3,5,6,11,12,17] d14 b8
  have b9 : a 14 ≠ 5 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,6,11,12,17] := remove (a 14) 5 [0,1,5,6,11,12,17] t8 b9
  have b10 : a 14 ≠ 6 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,11,12,17] := remove (a 14) 6 [0,1,6,11,12,17] t9 b10
  have b11 : a 14 ≠ 11 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,12,17] := remove (a 14) 11 [0,1,11,12,17] t10 b11
  have b12 : a 14 ≠ 12 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 12 d10 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,17] := remove (a 14) 12 [0,1,12,17] t11 b12
  have b13 : a 14 ≠ 17 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 17 d10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,1] := remove (a 14) 17 [0,1,17] t12 b13
  have b14 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,3,4,5] := remove (a 26) 2 [0,1,2,3,4,5] d26 b14
  have b15 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,4,5] := remove (a 26) 3 [0,1,3,4,5] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t13 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,4,5])
    (d10 : a 10 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,1])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 26 ∈ [0,1] ∧ a 28 ∈ [0,1,4,8] ∧ a 29 ∈ [0,1] ∧ a 30 ∈ [0,1,2,3,6,7,8] := by
  have b0 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,5] := remove (a 26) 4 [0,1,4,5] d26 b0
  have b1 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1] := remove (a 26) 5 [0,1,5] t0 b1
  have b2 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 28) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b2
  have b3 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,4,6,7,8,9,10,11] := remove (a 28) 5 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 28 ≠ 6 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,4,7,8,9,10,11] := remove (a 28) 6 [0,1,4,6,7,8,9,10,11] t4 b5
  have b6 : a 28 ≠ 7 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,4,8,9,10,11] := remove (a 28) 7 [0,1,4,7,8,9,10,11] t5 b6
  have b7 : a 28 ≠ 9 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,4,8,10,11] := remove (a 28) 9 [0,1,4,8,9,10,11] t6 b7
  have b8 : a 28 ≠ 10 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,4,8,11] := remove (a 28) 10 [0,1,4,8,10,11] t7 b8
  have b9 : a 28 ≠ 11 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,4,8] := remove (a 28) 11 [0,1,4,8,11] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3,4,5] := remove (a 29) 2 [0,1,2,3,4,5] d29 b10
  have b11 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,4,5] := remove (a 29) 3 [0,1,3,4,5] t10 b11
  have b12 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,5] := remove (a 29) 4 [0,1,4,5] t11 b12
  have b13 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1] := remove (a 29) 5 [0,1,5] t12 b13
  have b14 : a 30 ≠ 4 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,3,5,6,7,8] := remove (a 30) 4 [0,1,2,3,4,5,6,7,8] d30 b14
  have b15 : a 30 ≠ 5 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,2,3,6,7,8] := remove (a 30) 5 [0,1,2,3,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t9 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,6,7,8])
    (d14 : a 14 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,3,5])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 30 ∈ [0,1,2,3] ∧ a 31 ∈ [0,1,2,3,4,6,8,10] ∧ a 17 ∈ [0,1] ∧ a 20 ∈ [0,1] ∧ a 19 ∈ [0,1,5,6,7,8,9,10,11] := by
  have b0 : a 30 ≠ 6 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,3,7,8] := remove (a 30) 6 [0,1,2,3,6,7,8] d30 b0
  have b1 : a 30 ≠ 7 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,3,8] := remove (a 30) 7 [0,1,2,3,7,8] t0 b1
  have b2 : a 30 ≠ 8 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,3] := remove (a 30) 8 [0,1,2,3,8] t1 b2
  have b3 : a 31 ≠ 5 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,4,6,7,8,9,10,11] := remove (a 31) 5 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b3
  have b4 : a 31 ≠ 7 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3,4,6,8,9,10,11] := remove (a 31) 7 [0,1,2,3,4,6,7,8,9,10,11] t3 b4
  have b5 : a 31 ≠ 9 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,2,3,4,6,8,10,11] := remove (a 31) 9 [0,1,2,3,4,6,8,9,10,11] t4 b5
  have b6 : a 31 ≠ 11 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,2,3,4,6,8,10] := remove (a 31) 11 [0,1,2,3,4,6,8,10,11] t5 b6
  have b7 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,3,4,5] := remove (a 17) 2 [0,1,2,3,4,5] d17 b7
  have b8 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,4,5] := remove (a 17) 3 [0,1,3,4,5] t7 b8
  have b9 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 4 d16 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,1,5] := remove (a 17) 4 [0,1,4,5] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,1] := remove (a 17) 5 [0,1,5] t9 b10
  have b11 : a 20 ≠ 3 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,5] := remove (a 20) 3 [0,1,3,5] d20 b11
  have b12 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 5 d16 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t11 b12
  have b13 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 2 t10 c52 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b13
  have b14 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 3 t10 c52 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 4 t10 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 19) 4 [0,1,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t10 (And.intro t12 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_207
