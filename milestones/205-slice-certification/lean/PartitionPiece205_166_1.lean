import PartitionData205_166
namespace PartitionCover205_166
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,2,4,6,9,10,11])
    (d12 : a 12 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 13 ∈ [0,2,4,6] ∧ a 28 ∈ [0,1,2,4,6,7,8,10] ∧ a 29 ∈ [0,1,2,6,7,8,9,10,11] := by
  have b0 : a 13 ≠ 9 := exclude [0,1] (fun u v => edge r40 v u) (a 13) (a 12) 9 d12 c40 (by decide +kernel)
  have t0 : a 13 ∈ [0,2,4,6,10,11] := remove (a 13) 9 [0,2,4,6,9,10,11] d13 b0
  have b1 : a 13 ≠ 10 := exclude [0,1] (fun u v => edge r40 v u) (a 13) (a 12) 10 d12 c40 (by decide +kernel)
  have t1 : a 13 ∈ [0,2,4,6,11] := remove (a 13) 10 [0,2,4,6,10,11] t0 b1
  have b2 : a 13 ≠ 11 := exclude [0,1] (fun u v => edge r40 v u) (a 13) (a 12) 11 d12 c40 (by decide +kernel)
  have t2 : a 13 ∈ [0,2,4,6] := remove (a 13) 11 [0,2,4,6,11] t1 b2
  have b3 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d28 b3
  have b4 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,2,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 5 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 28 ≠ 9 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,2,4,6,7,8,10,11,12,13,14,15,16,17] := remove (a 28) 9 [0,1,2,4,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 28 ≠ 11 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,2,4,6,7,8,10,12,13,14,15,16,17] := remove (a 28) 11 [0,1,2,4,6,7,8,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 28 ≠ 12 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 12 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,2,4,6,7,8,10,13,14,15,16,17] := remove (a 28) 12 [0,1,2,4,6,7,8,10,12,13,14,15,16,17] t6 b7
  have b8 : a 28 ≠ 13 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 13 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,2,4,6,7,8,10,14,15,16,17] := remove (a 28) 13 [0,1,2,4,6,7,8,10,13,14,15,16,17] t7 b8
  have b9 : a 28 ≠ 14 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,2,4,6,7,8,10,15,16,17] := remove (a 28) 14 [0,1,2,4,6,7,8,10,14,15,16,17] t8 b9
  have b10 : a 28 ≠ 15 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,2,4,6,7,8,10,16,17] := remove (a 28) 15 [0,1,2,4,6,7,8,10,15,16,17] t9 b10
  have b11 : a 28 ≠ 16 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,2,4,6,7,8,10,17] := remove (a 28) 16 [0,1,2,4,6,7,8,10,16,17] t10 b11
  have b12 : a 28 ≠ 17 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,2,4,6,7,8,10] := remove (a 28) 17 [0,1,2,4,6,7,8,10,17] t11 b12
  have b13 : a 29 ≠ 3 := exclude [0,2,4,6] (fun u v => edge r44 v u) (a 29) (a 13) 3 t2 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b13
  have b14 : a 29 ≠ 4 := exclude [0,2,4,6] (fun u v => edge r44 v u) (a 29) (a 13) 4 t2 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,2,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 29 ≠ 5 := exclude [0,2,4,6] (fun u v => edge r44 v u) (a 29) (a 13) 5 t2 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 29) 5 [0,1,2,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t12 (t15))

theorem chunk5 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,2,4,6])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 29 ∈ [0,1,2,6,7,9,10] ∧ a 30 ∈ [0,1,3,4] ∧ a 31 ∈ [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 8 := exclude [0,2,4,6] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,2,6,7,9,10,11] := remove (a 29) 8 [0,1,2,6,7,8,9,10,11] d29 b0
  have b1 : a 29 ≠ 11 := exclude [0,2,4,6] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,2,6,7,9,10] := remove (a 29) 11 [0,1,2,6,7,9,10,11] t0 b1
  have b2 : a 30 ≠ 2 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,3,4,5,6,7,8] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8] d30 b2
  have b3 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,3,4,6,7,8] := remove (a 30) 5 [0,1,3,4,5,6,7,8] t2 b3
  have b4 : a 30 ≠ 6 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,3,4,7,8] := remove (a 30) 6 [0,1,3,4,6,7,8] t3 b4
  have b5 : a 30 ≠ 7 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,3,4,8] := remove (a 30) 7 [0,1,3,4,7,8] t4 b5
  have b6 : a 30 ≠ 8 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,3,4] := remove (a 30) 8 [0,1,3,4,8] t5 b6
  have b7 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b7
  have b8 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 31 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 31 ≠ 16 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23] := remove (a 31) 16 [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t6 (t15))

theorem chunk6 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,6])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d25 : a 25 ∈ [0,1,2,3,6,7,8,9])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    : a 31 ∈ [0,1,2,3,12,13,14,15,20,22] ∧ a 16 ∈ [0,6] ∧ a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11] := by
  have b0 : a 31 ≠ 17 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,12,13,14,15,18,19,20,21,22,23] := remove (a 31) 17 [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 18 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 18 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,12,13,14,15,19,20,21,22,23] := remove (a 31) 18 [0,1,2,3,12,13,14,15,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 19 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 19 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2,3,12,13,14,15,20,21,22,23] := remove (a 31) 19 [0,1,2,3,12,13,14,15,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 21 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,12,13,14,15,20,22,23] := remove (a 31) 21 [0,1,2,3,12,13,14,15,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 23 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3,12,13,14,15,20,22] := remove (a 31) 23 [0,1,2,3,12,13,14,15,20,22,23] t3 b4
  have b5 : a 16 ≠ 1 := exclude [0,6] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t5 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d16 b5
  have b6 : a 16 ≠ 2 := exclude [0,6] (edge r49) (a 16) (a 18) 2 d18 c49 (by decide +kernel)
  have t6 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 16) 2 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 16 ≠ 3 := exclude [0,6] (edge r49) (a 16) (a 18) 3 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 16) 3 [0,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 16 ≠ 4 := exclude [0,6] (edge r49) (a 16) (a 18) 4 d18 c49 (by decide +kernel)
  have t8 : a 16 ∈ [0,5,6,7,8,9,10,11] := remove (a 16) 4 [0,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 16 ≠ 5 := exclude [0,6] (edge r49) (a 16) (a 18) 5 d18 c49 (by decide +kernel)
  have t9 : a 16 ∈ [0,6,7,8,9,10,11] := remove (a 16) 5 [0,5,6,7,8,9,10,11] t8 b9
  have b10 : a 16 ≠ 7 := exclude [0,6] (edge r49) (a 16) (a 18) 7 d18 c49 (by decide +kernel)
  have t10 : a 16 ∈ [0,6,8,9,10,11] := remove (a 16) 7 [0,6,7,8,9,10,11] t9 b10
  have b11 : a 16 ≠ 8 := exclude [0,6] (edge r49) (a 16) (a 18) 8 d18 c49 (by decide +kernel)
  have t11 : a 16 ∈ [0,6,9,10,11] := remove (a 16) 8 [0,6,8,9,10,11] t10 b11
  have b12 : a 16 ≠ 9 := exclude [0,6] (edge r49) (a 16) (a 18) 9 d18 c49 (by decide +kernel)
  have t12 : a 16 ∈ [0,6,10,11] := remove (a 16) 9 [0,6,9,10,11] t11 b12
  have b13 : a 16 ≠ 10 := exclude [0,6] (edge r49) (a 16) (a 18) 10 d18 c49 (by decide +kernel)
  have t13 : a 16 ∈ [0,6,11] := remove (a 16) 10 [0,6,10,11] t12 b13
  have b14 : a 16 ≠ 11 := exclude [0,6] (edge r49) (a 16) (a 18) 11 d18 c49 (by decide +kernel)
  have t14 : a 16 ∈ [0,6] := remove (a 16) 11 [0,6,11] t13 b14
  have b15 : a 17 ≠ 4 := exclude [0,1,2,3,6,7,8,9] (edge r54) (a 17) (a 25) 4 d25 c54 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 17) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b15
  exact And.intro t4 (And.intro t14 (t15))

theorem chunk7 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,5,6,7,8,9,10,11])
    (d25 : a 25 ∈ [0,1,2,3,6,7,8,9])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d18 : a 18 ∈ [0,6])
    (d26 : a 26 ∈ [0,1,4])
    (d27 : a 27 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d22 : a 22 ∈ [0,3])
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    : a 17 ∈ [0,1,2,3,6,7,8,9] ∧ a 19 ∈ [0] ∧ a 26 ∈ [0] ∧ a 20 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := by
  have b0 : a 17 ≠ 5 := exclude [0,1,2,3,6,7,8,9] (edge r54) (a 17) (a 25) 5 d25 c54 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 17) 5 [0,1,2,3,5,6,7,8,9,10,11] d17 b0
  have b1 : a 17 ≠ 10 := exclude [0,1,2,3,6,7,8,9] (edge r54) (a 17) (a 25) 10 d25 c54 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,2,3,6,7,8,9,11] := remove (a 17) 10 [0,1,2,3,6,7,8,9,10,11] t0 b1
  have b2 : a 17 ≠ 11 := exclude [0,1,2,3,6,7,8,9] (edge r54) (a 17) (a 25) 11 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,2,3,6,7,8,9] := remove (a 17) 11 [0,1,2,3,6,7,8,9,11] t1 b2
  have b3 : a 19 ≠ 1 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b3
  have b4 : a 19 ≠ 2 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,3,4,5] := remove (a 19) 2 [0,2,3,4,5] t3 b4
  have b5 : a 19 ≠ 4 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,3,5] := remove (a 19) 4 [0,3,4,5] t4 b5
  have b6 : a 19 ≠ 5 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,3] := remove (a 19) 5 [0,3,5] t5 b6
  have b7 : a 26 ≠ 1 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 1 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,4] := remove (a 26) 1 [0,1,4] d26 b7
  have b8 : a 26 ≠ 4 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 4 [0,4] t7 b8
  have b9 : a 19 ≠ 3 := exclude [0] (edge r59) (a 19) (a 27) 3 d27 c59 (by decide +kernel)
  have t9 : a 19 ∈ [0] := remove (a 19) 3 [0,3] t6 b9
  have b10 : a 20 ≠ 2 := exclude [0,3] (edge r61) (a 20) (a 22) 2 d22 c61 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b10
  have b11 : a 20 ≠ 3 := exclude [0,3] (edge r61) (a 20) (a 22) 3 d22 c61 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 20 ≠ 4 := exclude [0,3] (edge r61) (a 20) (a 22) 4 d22 c61 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 20 ≠ 5 := exclude [0,3] (edge r61) (a 20) (a 22) 5 d22 c61 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 20 ≠ 8 := exclude [0,3] (edge r61) (a 20) (a 22) 8 d22 c61 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 20) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 9 := exclude [0,3] (edge r61) (a 20) (a 22) 9 d22 c61 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 20) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t9 (And.intro t8 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_166
