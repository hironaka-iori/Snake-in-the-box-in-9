import PartitionData205_200
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,1,12,13])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,6])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,2,11,13,14,15,19,23] ∧ a 31 ∈ [0,2,3,5,6,7,9,10,11] := by
  have b0 : a 30 ≠ 5 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 6 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 7 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 8 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 30 ≠ 9 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 10 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 12 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 16 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,11,13,14,15,17,18,19,20,21,22,23] := remove (a 30) 16 [0,2,11,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 30 ≠ 17 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,11,13,14,15,18,19,20,21,22,23] := remove (a 30) 17 [0,2,11,13,14,15,17,18,19,20,21,22,23] t7 b8
  have b9 : a 30 ≠ 18 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,11,13,14,15,19,20,21,22,23] := remove (a 30) 18 [0,2,11,13,14,15,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 20 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 20 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,11,13,14,15,19,21,22,23] := remove (a 30) 20 [0,2,11,13,14,15,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 21 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,11,13,14,15,19,22,23] := remove (a 30) 21 [0,2,11,13,14,15,19,21,22,23] t10 b11
  have b12 : a 30 ≠ 22 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,11,13,14,15,19,23] := remove (a 30) 22 [0,2,11,13,14,15,19,22,23] t11 b12
  have b13 : a 31 ≠ 1 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b13
  have b14 : a 31 ≠ 4 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 31) 4 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 31 ≠ 8 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,3,5,6,7,9,10,11] := remove (a 31) 8 [0,2,3,5,6,7,8,9,10,11] t14 b15
  exact And.intro t12 (t15)

theorem chunk13 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,3,5,6,7,9,10,11])
    (d15 : a 15 ∈ [0,6])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,4,5,10,16])
    (d25 : a 25 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,4])
    (d26 : a 26 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 31 ∈ [0,2,3,5,6,7,9] ∧ a 17 ∈ [0,2] ∧ a 24 ∈ [0,4] ∧ a 19 ∈ [0] ∧ a 26 ∈ [0,9,10,11,12,13,14,15,16,17,19,20,21,23] := by
  have b0 : a 31 ≠ 10 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,3,5,6,7,9,11] := remove (a 31) 10 [0,2,3,5,6,7,9,10,11] d31 b0
  have b1 : a 31 ≠ 11 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,3,5,6,7,9] := remove (a 31) 11 [0,2,3,5,6,7,9,11] t0 b1
  have b2 : a 17 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r48 v u) (a 17) (a 16) 4 d16 c48 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,2,3,5] := remove (a 17) 4 [0,1,2,3,4,5] d17 b2
  have b3 : a 17 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,2,3] := remove (a 17) 5 [0,1,2,3,5] t2 b3
  have b4 : a 24 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r51 v u) (a 24) (a 16) 1 d16 c51 (by decide +kernel)
  have t4 : a 24 ∈ [0,4,5,10,16] := remove (a 24) 1 [0,1,4,5,10,16] d24 b4
  have b5 : a 24 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r51 v u) (a 24) (a 16) 5 d16 c51 (by decide +kernel)
  have t5 : a 24 ∈ [0,4,10,16] := remove (a 24) 5 [0,4,5,10,16] t4 b5
  have b6 : a 24 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r51 v u) (a 24) (a 16) 10 d16 c51 (by decide +kernel)
  have t6 : a 24 ∈ [0,4,16] := remove (a 24) 10 [0,4,10,16] t5 b6
  have b7 : a 24 ≠ 16 := exclude [0,1,2,3] (fun u v => edge r51 v u) (a 24) (a 16) 16 d16 c51 (by decide +kernel)
  have t7 : a 24 ∈ [0,4] := remove (a 24) 16 [0,4,16] t6 b7
  have b8 : a 17 ≠ 1 := exclude [0,1] (edge r54) (a 17) (a 25) 1 d25 c54 (by decide +kernel)
  have t8 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] t3 b8
  have b9 : a 17 ≠ 3 := exclude [0,1] (edge r54) (a 17) (a 25) 3 d25 c54 (by decide +kernel)
  have t9 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t8 b9
  have b10 : a 19 ≠ 1 := exclude [0,4] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b10
  have b11 : a 19 ≠ 2 := exclude [0,4] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t10 b11
  have b12 : a 26 ≠ 2 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 2 d18 c57 (by decide +kernel)
  have t12 : a 26 ∈ [0,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 2 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] d26 b12
  have b13 : a 26 ≠ 4 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t13 : a 26 ∈ [0,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 4 [0,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] t12 b13
  have b14 : a 26 ≠ 6 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 6 d18 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,8,9,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 6 [0,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] t13 b14
  have b15 : a 26 ≠ 8 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 8 d18 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,9,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 8 [0,8,9,10,11,12,13,14,15,16,17,19,20,21,23] t14 b15
  exact And.intro t1 (And.intro t9 (And.intro t7 (And.intro t11 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,9,10,11,12,13,14,15,16,17,19,20,21,23])
    (d18 : a 18 ∈ [0,4])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,1,2])
    (d22 : a 22 ∈ [0,1,3,4])
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    : a 26 ∈ [0,14,15,19] ∧ a 23 ∈ [0,1] ∧ a 21 ∈ [0,2] ∧ a 22 ∈ [0,1,4] := by
  have b0 : a 26 ≠ 9 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 9 d18 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 9 [0,9,10,11,12,13,14,15,16,17,19,20,21,23] d26 b0
  have b1 : a 26 ≠ 10 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 10 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 10 [0,10,11,12,13,14,15,16,17,19,20,21,23] t0 b1
  have b2 : a 26 ≠ 11 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 11 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 11 [0,11,12,13,14,15,16,17,19,20,21,23] t1 b2
  have b3 : a 26 ≠ 12 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 12 d18 c57 (by decide +kernel)
  have t3 : a 26 ∈ [0,13,14,15,16,17,19,20,21,23] := remove (a 26) 12 [0,12,13,14,15,16,17,19,20,21,23] t2 b3
  have b4 : a 26 ≠ 13 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 13 d18 c57 (by decide +kernel)
  have t4 : a 26 ∈ [0,14,15,16,17,19,20,21,23] := remove (a 26) 13 [0,13,14,15,16,17,19,20,21,23] t3 b4
  have b5 : a 26 ≠ 16 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 16 d18 c57 (by decide +kernel)
  have t5 : a 26 ∈ [0,14,15,17,19,20,21,23] := remove (a 26) 16 [0,14,15,16,17,19,20,21,23] t4 b5
  have b6 : a 26 ≠ 17 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 17 d18 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,14,15,19,20,21,23] := remove (a 26) 17 [0,14,15,17,19,20,21,23] t5 b6
  have b7 : a 26 ≠ 20 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 20 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,14,15,19,21,23] := remove (a 26) 20 [0,14,15,19,20,21,23] t6 b7
  have b8 : a 26 ≠ 21 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 21 d18 c57 (by decide +kernel)
  have t8 : a 26 ∈ [0,14,15,19,23] := remove (a 26) 21 [0,14,15,19,21,23] t7 b8
  have b9 : a 26 ≠ 23 := exclude [0,4] (fun u v => edge r57 v u) (a 26) (a 18) 23 d18 c57 (by decide +kernel)
  have t9 : a 26 ∈ [0,14,15,19] := remove (a 26) 23 [0,14,15,19,23] t8 b9
  have b10 : a 23 ≠ 2 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b10
  have b11 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t10 b11
  have b12 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] t11 b12
  have b13 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t12 b13
  have b14 : a 21 ≠ 1 := exclude [0,1] (edge r63) (a 21) (a 23) 1 t13 c63 (by decide +kernel)
  have t14 : a 21 ∈ [0,2] := remove (a 21) 1 [0,1,2] d21 b14
  have b15 : a 22 ≠ 3 := exclude [0,1] (edge r65) (a 22) (a 23) 3 t13 c65 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,4] := remove (a 22) 3 [0,1,3,4] d22 b15
  exact And.intro t9 (And.intro t13 (And.intro t14 (t15)))

theorem chunk15 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,4])
    (d23 : a 23 ∈ [0,1])
    (d30 : a 30 ∈ [0,2,11,13,14,15,19,23])
    (d31 : a 31 ∈ [0,2,3,5,6,7,9])
    (d26 : a 26 ∈ [0,14,15,19])
    (d27 : a 27 ∈ [0,1,9,11])
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 22 ∈ [0,1] ∧ a 30 ∈ [0,19] ∧ a 31 ∈ [0,9] ∧ a 26 ∈ [0,19] ∧ a 27 ∈ [0,9] := by
  have b0 : a 22 ≠ 4 := exclude [0,1] (edge r65) (a 22) (a 23) 4 d23 c65 (by decide +kernel)
  have t0 : a 22 ∈ [0,1] := remove (a 22) 4 [0,1,4] d22 b0
  have b1 : a 30 ≠ 11 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 11 t0 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,13,14,15,19,23] := remove (a 30) 11 [0,2,11,13,14,15,19,23] d30 b1
  have b2 : a 30 ≠ 13 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 13 t0 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,14,15,19,23] := remove (a 30) 13 [0,2,13,14,15,19,23] t1 b2
  have b3 : a 30 ≠ 14 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 14 t0 c66 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,15,19,23] := remove (a 30) 14 [0,2,14,15,19,23] t2 b3
  have b4 : a 30 ≠ 15 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 15 t0 c66 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,19,23] := remove (a 30) 15 [0,2,15,19,23] t3 b4
  have b5 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,3,5,6,7,9] := remove (a 31) 2 [0,2,3,5,6,7,9] d31 b5
  have b6 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 3 d23 c67 (by decide +kernel)
  have t6 : a 31 ∈ [0,5,6,7,9] := remove (a 31) 3 [0,3,5,6,7,9] t5 b6
  have b7 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,6,7,9] := remove (a 31) 5 [0,5,6,7,9] t6 b7
  have b8 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 6 d23 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,7,9] := remove (a 31) 6 [0,6,7,9] t7 b8
  have b9 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 7 d23 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,9] := remove (a 31) 7 [0,7,9] t8 b9
  have b10 : a 26 ≠ 14 := exclude [0,1,9,11] (edge r73) (a 26) (a 27) 14 d27 c73 (by decide +kernel)
  have t10 : a 26 ∈ [0,15,19] := remove (a 26) 14 [0,14,15,19] d26 b10
  have b11 : a 26 ≠ 15 := exclude [0,1,9,11] (edge r73) (a 26) (a 27) 15 d27 c73 (by decide +kernel)
  have t11 : a 26 ∈ [0,19] := remove (a 26) 15 [0,15,19] t10 b11
  have b12 : a 27 ≠ 1 := exclude [0,19] (fun u v => edge r73 v u) (a 27) (a 26) 1 t11 c73 (by decide +kernel)
  have t12 : a 27 ∈ [0,9,11] := remove (a 27) 1 [0,1,9,11] d27 b12
  have b13 : a 27 ≠ 11 := exclude [0,19] (fun u v => edge r73 v u) (a 27) (a 26) 11 t11 c73 (by decide +kernel)
  have t13 : a 27 ∈ [0,9] := remove (a 27) 11 [0,9,11] t12 b13
  have b14 : a 30 ≠ 2 := exclude [0,19] (fun u v => edge r74 v u) (a 30) (a 26) 2 t11 c74 (by decide +kernel)
  have t14 : a 30 ∈ [0,19,23] := remove (a 30) 2 [0,2,19,23] t4 b14
  have b15 : a 30 ≠ 23 := exclude [0,19] (fun u v => edge r74 v u) (a 30) (a 26) 23 t11 c74 (by decide +kernel)
  have t15 : a 30 ∈ [0,19] := remove (a 30) 23 [0,19,23] t14 b15
  exact And.intro t0 (And.intro t15 (And.intro t9 (And.intro t11 (t13))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_200
