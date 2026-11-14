import PartitionData205_188
namespace PartitionCover205_188
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,4])
    (d15 : a 15 ∈ [0,1,3,4])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,6])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0,3,6,7] ∧ a 15 ∈ [0,3] ∧ a 29 ∈ [0,1,2,3] ∧ a 30 ∈ [0,1,2,5,6,7,8,9,10,11] := by
  have b0 : a 28 ≠ 2 := exclude [0,4] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,3,4,5,6,7,8] := remove (a 28) 2 [0,2,3,4,5,6,7,8] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0,4] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,3,5,6,7,8] := remove (a 28) 4 [0,3,4,5,6,7,8] t0 b1
  have b2 : a 28 ≠ 5 := exclude [0,4] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,3,6,7,8] := remove (a 28) 5 [0,3,5,6,7,8] t1 b2
  have b3 : a 28 ≠ 8 := exclude [0,4] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,3,6,7] := remove (a 28) 8 [0,3,6,7,8] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t4 : a 15 ∈ [0,3,4] := remove (a 15) 1 [0,1,3,4] d15 b4
  have b5 : a 15 ≠ 4 := exclude [0,1] (fun u v => edge r43 v u) (a 15) (a 13) 4 d13 c43 (by decide +kernel)
  have t5 : a 15 ∈ [0,3] := remove (a 15) 4 [0,3,4] t4 b5
  have b6 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b6
  have b7 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 29) 5 [0,1,2,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 29) 6 [0,1,2,3,6,7,8,9,10,11] t7 b8
  have b9 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,2,3,8,9,10,11] := remove (a 29) 7 [0,1,2,3,7,8,9,10,11] t8 b9
  have b10 : a 29 ≠ 8 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,2,3,9,10,11] := remove (a 29) 8 [0,1,2,3,8,9,10,11] t9 b10
  have b11 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,2,3,10,11] := remove (a 29) 9 [0,1,2,3,9,10,11] t10 b11
  have b12 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,2,3,11] := remove (a 29) 10 [0,1,2,3,10,11] t11 b12
  have b13 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,2,3] := remove (a 29) 11 [0,1,2,3,11] t12 b13
  have b14 : a 30 ≠ 3 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b14
  have b15 : a 30 ≠ 4 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,2,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t13 (t15)))

theorem chunk13 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,6])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,3])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,1,2] ∧ a 31 ∈ [0,2,9] := by
  have b0 : a 30 ≠ 5 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 30) 5 [0,1,2,5,6,7,8,9,10,11] d30 b0
  have b1 : a 30 ≠ 6 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,7,8,9,10,11] := remove (a 30) 6 [0,1,2,6,7,8,9,10,11] t0 b1
  have b2 : a 30 ≠ 7 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,8,9,10,11] := remove (a 30) 7 [0,1,2,7,8,9,10,11] t1 b2
  have b3 : a 30 ≠ 8 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,2,9,10,11] := remove (a 30) 8 [0,1,2,8,9,10,11] t2 b3
  have b4 : a 30 ≠ 9 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,2,10,11] := remove (a 30) 9 [0,1,2,9,10,11] t3 b4
  have b5 : a 30 ≠ 10 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,2,11] := remove (a 30) 10 [0,1,2,10,11] t4 b5
  have b6 : a 30 ≠ 11 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,2] := remove (a 30) 11 [0,1,2,11] t5 b6
  have b7 : a 31 ≠ 1 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b7
  have b8 : a 31 ≠ 3 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 31) 3 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 31 ≠ 4 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 31) 4 [0,2,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 31 ≠ 5 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,2,6,7,8,9,10,11] := remove (a 31) 5 [0,2,5,6,7,8,9,10,11] t9 b10
  have b11 : a 31 ≠ 6 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,7,8,9,10,11] := remove (a 31) 6 [0,2,6,7,8,9,10,11] t10 b11
  have b12 : a 31 ≠ 7 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,8,9,10,11] := remove (a 31) 7 [0,2,7,8,9,10,11] t11 b12
  have b13 : a 31 ≠ 8 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,9,10,11] := remove (a 31) 8 [0,2,8,9,10,11] t12 b13
  have b14 : a 31 ≠ 10 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,9,11] := remove (a 31) 10 [0,2,9,10,11] t13 b14
  have b15 : a 31 ≠ 11 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,9] := remove (a 31) 11 [0,2,9,11] t14 b15
  exact And.intro t6 (t15)

theorem chunk14 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2,3,6,7,8,9])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7])
    (d19 : a 19 ∈ [0,5,9])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 16 ∈ [0,1] ∧ a 18 ∈ [0,6] ∧ a 20 ∈ [0,1,2,3] ∧ a 19 ∈ [0] ∧ a 22 ∈ [0,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 16 ≠ 2 := exclude [0,1] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b0
  have b1 : a 16 ≠ 3 := exclude [0,1] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t1 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t0 b1
  have b2 : a 18 ≠ 2 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 2 t1 c49 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,3,6,7,8,9] := remove (a 18) 2 [0,1,2,3,6,7,8,9] d18 b2
  have b3 : a 18 ≠ 3 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 3 t1 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,6,7,8,9] := remove (a 18) 3 [0,1,3,6,7,8,9] t2 b3
  have b4 : a 18 ≠ 8 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 8 t1 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,6,7,9] := remove (a 18) 8 [0,1,6,7,8,9] t3 b4
  have b5 : a 18 ≠ 9 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 9 t1 c49 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,6,7] := remove (a 18) 9 [0,1,6,7,9] t4 b5
  have b6 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 4 t1 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,2,3,5,6,7] := remove (a 20) 4 [0,1,2,3,4,5,6,7] d20 b6
  have b7 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 5 t1 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,2,3,6,7] := remove (a 20) 5 [0,1,2,3,5,6,7] t6 b7
  have b8 : a 20 ≠ 6 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 6 t1 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,2,3,7] := remove (a 20) 6 [0,1,2,3,6,7] t7 b8
  have b9 : a 20 ≠ 7 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 7 t1 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,2,3] := remove (a 20) 7 [0,1,2,3,7] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,5,9] (edge r55) (a 18) (a 19) 1 d19 c55 (by decide +kernel)
  have t10 : a 18 ∈ [0,6,7] := remove (a 18) 1 [0,1,6,7] t5 b10
  have b11 : a 18 ≠ 7 := exclude [0,5,9] (edge r55) (a 18) (a 19) 7 d19 c55 (by decide +kernel)
  have t11 : a 18 ∈ [0,6] := remove (a 18) 7 [0,6,7] t10 b11
  have b12 : a 19 ≠ 5 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 5 t11 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,9] := remove (a 19) 5 [0,5,9] d19 b12
  have b13 : a 19 ≠ 9 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 9 t11 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0] := remove (a 19) 9 [0,9] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 1 t11 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b14
  have b15 : a 22 ≠ 3 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 3 t11 c56 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t11 (And.intro t9 (And.intro t13 (t15))))

theorem chunk15 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,6])
    (d23 : a 23 ∈ [0,1,2])
    (d19 : a 19 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,2,3,5])
    (d28 : a 28 ∈ [0,3,6,7])
    (d29 : a 29 ∈ [0,1,2,3])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    : a 22 ∈ [0,6,8] ∧ a 23 ∈ [0,1] ∧ a 20 ∈ [0,2] ∧ a 21 ∈ [0,3] ∧ a 28 ∈ [0,3] ∧ a 29 ∈ [0,2] := by
  have b0 : a 22 ≠ 4 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 22) 4 [0,2,4,5,6,7,8,9,10,11] d22 b0
  have b1 : a 22 ≠ 5 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,6,7,8,9,10,11] := remove (a 22) 5 [0,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 22 ≠ 7 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 7 d18 c56 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,6,8,9,10,11] := remove (a 22) 7 [0,2,6,7,8,9,10,11] t1 b2
  have b3 : a 22 ≠ 9 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 9 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,6,8,10,11] := remove (a 22) 9 [0,2,6,8,9,10,11] t2 b3
  have b4 : a 22 ≠ 10 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 10 d18 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,6,8,11] := remove (a 22) 10 [0,2,6,8,10,11] t3 b4
  have b5 : a 22 ≠ 11 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 11 d18 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,6,8] := remove (a 22) 11 [0,2,6,8,11] t4 b5
  have b6 : a 23 ≠ 2 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1] := remove (a 23) 2 [0,1,2] d23 b6
  have b7 : a 20 ≠ 1 := exclude [0,2,3,5] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t7 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b7
  have b8 : a 20 ≠ 3 := exclude [0,2,3,5] (edge r60) (a 20) (a 21) 3 d21 c60 (by decide +kernel)
  have t8 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t7 b8
  have b9 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r60 v u) (a 21) (a 20) 2 t8 c60 (by decide +kernel)
  have t9 : a 21 ∈ [0,3,5] := remove (a 21) 2 [0,2,3,5] d21 b9
  have b10 : a 21 ≠ 5 := exclude [0,2] (fun u v => edge r60 v u) (a 21) (a 20) 5 t8 c60 (by decide +kernel)
  have t10 : a 21 ∈ [0,3] := remove (a 21) 5 [0,3,5] t9 b10
  have b11 : a 28 ≠ 6 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 6 t8 c62 (by decide +kernel)
  have t11 : a 28 ∈ [0,3,7] := remove (a 28) 6 [0,3,6,7] d28 b11
  have b12 : a 28 ≠ 7 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 7 t8 c62 (by decide +kernel)
  have t12 : a 28 ∈ [0,3] := remove (a 28) 7 [0,3,7] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 1 t10 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 3 t10 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t13 b14
  have b15 : a 22 ≠ 2 := exclude [0,1] (edge r65) (a 22) (a 23) 2 t6 c65 (by decide +kernel)
  have t15 : a 22 ∈ [0,6,8] := remove (a 22) 2 [0,2,6,8] t5 b15
  exact And.intro t15 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (t14)))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_188
