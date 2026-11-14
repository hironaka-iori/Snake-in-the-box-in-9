import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,1,12,13])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,8])
    (d17 : a 17 ∈ [0,4,6,8,10,11])
    (d16 : a 16 ∈ [0,8,12,16])
    (d19 : a 19 ∈ [0,1,3,5,6,7,8,9,11,13,15,17])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 30 ∈ [0,2,11,13,14,15,19,23] ∧ a 31 ∈ [0,2,3,5,6,7,11] ∧ a 17 ∈ [0,4,6,8] ∧ a 19 ∈ [0,1,3,5,7,8,9,11,13,15,17] := by
  have b0 : a 30 ≠ 10 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 12 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 16 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,11,13,14,15,17,18,19,20,21,22,23] := remove (a 30) 16 [0,2,11,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 17 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,11,13,14,15,18,19,20,21,22,23] := remove (a 30) 17 [0,2,11,13,14,15,17,18,19,20,21,22,23] t2 b3
  have b4 : a 30 ≠ 18 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,11,13,14,15,19,20,21,22,23] := remove (a 30) 18 [0,2,11,13,14,15,18,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 20 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 20 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,11,13,14,15,19,21,22,23] := remove (a 30) 20 [0,2,11,13,14,15,19,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 21 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,11,13,14,15,19,22,23] := remove (a 30) 21 [0,2,11,13,14,15,19,21,22,23] t5 b6
  have b7 : a 30 ≠ 22 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,11,13,14,15,19,23] := remove (a 30) 22 [0,2,11,13,14,15,19,22,23] t6 b7
  have b8 : a 31 ≠ 1 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b8
  have b9 : a 31 ≠ 4 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 31) 4 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 31 ≠ 8 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,2,3,5,6,7,9,10,11] := remove (a 31) 8 [0,2,3,5,6,7,8,9,10,11] t9 b10
  have b11 : a 31 ≠ 9 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,3,5,6,7,10,11] := remove (a 31) 9 [0,2,3,5,6,7,9,10,11] t10 b11
  have b12 : a 31 ≠ 10 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,3,5,6,7,11] := remove (a 31) 10 [0,2,3,5,6,7,10,11] t11 b12
  have b13 : a 17 ≠ 10 := exclude [0,8,12,16] (fun u v => edge r48 v u) (a 17) (a 16) 10 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,4,6,8,11] := remove (a 17) 10 [0,4,6,8,10,11] d17 b13
  have b14 : a 17 ≠ 11 := exclude [0,8,12,16] (fun u v => edge r48 v u) (a 17) (a 16) 11 d16 c48 (by decide +kernel)
  have t14 : a 17 ∈ [0,4,6,8] := remove (a 17) 11 [0,4,6,8,11] t13 b14
  have b15 : a 19 ≠ 6 := exclude [0,4,6,8] (fun u v => edge r52 v u) (a 19) (a 17) 6 t14 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,3,5,7,8,9,11,13,15,17] := remove (a 19) 6 [0,1,3,5,6,7,8,9,11,13,15,17] d19 b15
  exact And.intro t7 (And.intro t12 (And.intro t14 (t15)))

theorem chunk17 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,3,5,7,8,9,11,13,15,17])
    (d17 : a 17 ∈ [0,4,6,8])
    (d25 : a 25 ∈ [0,1,3,4])
    (d18 : a 18 ∈ [0,8])
    (d22 : a 22 ∈ [0,1,2,3,8,9,10,11])
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 19 ∈ [0,1] ∧ a 17 ∈ [0,6] ∧ a 25 ∈ [0,3] ∧ a 22 ∈ [0,1,9,10,11] := by
  have b0 : a 19 ≠ 9 := exclude [0,4,6,8] (fun u v => edge r52 v u) (a 19) (a 17) 9 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,3,5,7,8,11,13,15,17] := remove (a 19) 9 [0,1,3,5,7,8,9,11,13,15,17] d19 b0
  have b1 : a 19 ≠ 11 := exclude [0,4,6,8] (fun u v => edge r52 v u) (a 19) (a 17) 11 d17 c52 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,3,5,7,8,13,15,17] := remove (a 19) 11 [0,1,3,5,7,8,11,13,15,17] t0 b1
  have b2 : a 19 ≠ 13 := exclude [0,4,6,8] (fun u v => edge r52 v u) (a 19) (a 17) 13 d17 c52 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,3,5,7,8,15,17] := remove (a 19) 13 [0,1,3,5,7,8,13,15,17] t1 b2
  have b3 : a 17 ≠ 4 := exclude [0,1,3,4] (edge r54) (a 17) (a 25) 4 d25 c54 (by decide +kernel)
  have t3 : a 17 ∈ [0,6,8] := remove (a 17) 4 [0,4,6,8] d17 b3
  have b4 : a 17 ≠ 8 := exclude [0,1,3,4] (edge r54) (a 17) (a 25) 8 d25 c54 (by decide +kernel)
  have t4 : a 17 ∈ [0,6] := remove (a 17) 8 [0,6,8] t3 b4
  have b5 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 1 t4 c54 (by decide +kernel)
  have t5 : a 25 ∈ [0,3,4] := remove (a 25) 1 [0,1,3,4] d25 b5
  have b6 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 4 t4 c54 (by decide +kernel)
  have t6 : a 25 ∈ [0,3] := remove (a 25) 4 [0,3,4] t5 b6
  have b7 : a 19 ≠ 3 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,5,7,8,15,17] := remove (a 19) 3 [0,1,3,5,7,8,15,17] t2 b7
  have b8 : a 19 ≠ 5 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,7,8,15,17] := remove (a 19) 5 [0,1,5,7,8,15,17] t7 b8
  have b9 : a 19 ≠ 7 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,8,15,17] := remove (a 19) 7 [0,1,7,8,15,17] t8 b9
  have b10 : a 19 ≠ 8 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,15,17] := remove (a 19) 8 [0,1,8,15,17] t9 b10
  have b11 : a 19 ≠ 15 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 15 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,17] := remove (a 19) 15 [0,1,15,17] t10 b11
  have b12 : a 19 ≠ 17 := exclude [0,8] (fun u v => edge r55 v u) (a 19) (a 18) 17 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,1] := remove (a 19) 17 [0,1,17] t11 b12
  have b13 : a 22 ≠ 2 := exclude [0,8] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,3,8,9,10,11] := remove (a 22) 2 [0,1,2,3,8,9,10,11] d22 b13
  have b14 : a 22 ≠ 3 := exclude [0,8] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,8,9,10,11] := remove (a 22) 3 [0,1,3,8,9,10,11] t13 b14
  have b15 : a 22 ≠ 8 := exclude [0,8] (fun u v => edge r56 v u) (a 22) (a 18) 8 d18 c56 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,9,10,11] := remove (a 22) 8 [0,1,8,9,10,11] t14 b15
  exact And.intro t12 (And.intro t4 (And.intro t6 (t15)))

theorem chunk18 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,9,10,11])
    (d18 : a 18 ∈ [0,8])
    (d26 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20])
    (d23 : a 23 ∈ [0,1,2])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,9,11])
    (d21 : a 21 ∈ [0,2,3,4,5,6,8])
    (d20 : a 20 ∈ [0,1,6,7,8,9,12,13])
    (d28 : a 28 ∈ [0,4,10,11])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 22 ∈ [0,1,10,11] ∧ a 26 ∈ [0,14,16,20] ∧ a 23 ∈ [0,1] ∧ a 27 ∈ [0,11] ∧ a 21 ∈ [0,3,4,6] ∧ a 20 ∈ [0,6,7,8,9,12,13] := by
  have b0 : a 22 ≠ 9 := exclude [0,8] (fun u v => edge r56 v u) (a 22) (a 18) 9 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,10,11] := remove (a 22) 9 [0,1,9,10,11] d22 b0
  have b1 : a 26 ≠ 4 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,6,7,8,10,12,13,14,16,19,20] := remove (a 26) 4 [0,4,6,7,8,10,12,13,14,16,19,20] d26 b1
  have b2 : a 26 ≠ 6 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 6 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,7,8,10,12,13,14,16,19,20] := remove (a 26) 6 [0,6,7,8,10,12,13,14,16,19,20] t1 b2
  have b3 : a 26 ≠ 7 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 7 d18 c57 (by decide +kernel)
  have t3 : a 26 ∈ [0,8,10,12,13,14,16,19,20] := remove (a 26) 7 [0,7,8,10,12,13,14,16,19,20] t2 b3
  have b4 : a 26 ≠ 8 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 8 d18 c57 (by decide +kernel)
  have t4 : a 26 ∈ [0,10,12,13,14,16,19,20] := remove (a 26) 8 [0,8,10,12,13,14,16,19,20] t3 b4
  have b5 : a 26 ≠ 10 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 10 d18 c57 (by decide +kernel)
  have t5 : a 26 ∈ [0,12,13,14,16,19,20] := remove (a 26) 10 [0,10,12,13,14,16,19,20] t4 b5
  have b6 : a 26 ≠ 12 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 12 d18 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,13,14,16,19,20] := remove (a 26) 12 [0,12,13,14,16,19,20] t5 b6
  have b7 : a 26 ≠ 13 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 13 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,14,16,19,20] := remove (a 26) 13 [0,13,14,16,19,20] t6 b7
  have b8 : a 26 ≠ 19 := exclude [0,8] (fun u v => edge r57 v u) (a 26) (a 18) 19 d18 c57 (by decide +kernel)
  have t8 : a 26 ∈ [0,14,16,20] := remove (a 26) 19 [0,14,16,19,20] t7 b8
  have b9 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1] := remove (a 23) 2 [0,1,2] d23 b9
  have b10 : a 27 ≠ 1 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0,9,11] := remove (a 27) 1 [0,1,9,11] d27 b10
  have b11 : a 27 ≠ 9 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 9 d19 c59 (by decide +kernel)
  have t11 : a 27 ∈ [0,11] := remove (a 27) 9 [0,9,11] t10 b11
  have b12 : a 21 ≠ 2 := exclude [0,1,6,7,8,9,12,13] (fun u v => edge r60 v u) (a 21) (a 20) 2 d20 c60 (by decide +kernel)
  have t12 : a 21 ∈ [0,3,4,5,6,8] := remove (a 21) 2 [0,2,3,4,5,6,8] d21 b12
  have b13 : a 21 ≠ 5 := exclude [0,1,6,7,8,9,12,13] (fun u v => edge r60 v u) (a 21) (a 20) 5 d20 c60 (by decide +kernel)
  have t13 : a 21 ∈ [0,3,4,6,8] := remove (a 21) 5 [0,3,4,5,6,8] t12 b13
  have b14 : a 21 ≠ 8 := exclude [0,1,6,7,8,9,12,13] (fun u v => edge r60 v u) (a 21) (a 20) 8 d20 c60 (by decide +kernel)
  have t14 : a 21 ∈ [0,3,4,6] := remove (a 21) 8 [0,3,4,6,8] t13 b14
  have b15 : a 20 ≠ 1 := exclude [0,4,10,11] (edge r62) (a 20) (a 28) 1 d28 c62 (by decide +kernel)
  have t15 : a 20 ∈ [0,6,7,8,9,12,13] := remove (a 20) 1 [0,1,6,7,8,9,12,13] d20 b15
  exact And.intro t0 (And.intro t8 (And.intro t9 (And.intro t11 (And.intro t14 (t15)))))

theorem chunk19 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,6,7,8,9,12,13])
    (d28 : a 28 ∈ [0,4,10,11])
    (d21 : a 21 ∈ [0,3,4,6])
    (d23 : a 23 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,8,9])
    (d22 : a 22 ∈ [0,1,10,11])
    (d30 : a 30 ∈ [0,2,11,13,14,15,19,23])
    (d31 : a 31 ∈ [0,2,3,5,6,7,11])
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 20 ∈ [0,6,8,12] ∧ a 21 ∈ [0,6] ∧ a 29 ∈ [0,8] ∧ a 22 ∈ [0,11] ∧ a 30 ∈ [0,2,19,23] ∧ a 31 ∈ [0,2,3,11] := by
  have b0 : a 20 ≠ 7 := exclude [0,4,10,11] (edge r62) (a 20) (a 28) 7 d28 c62 (by decide +kernel)
  have t0 : a 20 ∈ [0,6,8,9,12,13] := remove (a 20) 7 [0,6,7,8,9,12,13] d20 b0
  have b1 : a 20 ≠ 9 := exclude [0,4,10,11] (edge r62) (a 20) (a 28) 9 d28 c62 (by decide +kernel)
  have t1 : a 20 ∈ [0,6,8,12,13] := remove (a 20) 9 [0,6,8,9,12,13] t0 b1
  have b2 : a 20 ≠ 13 := exclude [0,4,10,11] (edge r62) (a 20) (a 28) 13 d28 c62 (by decide +kernel)
  have t2 : a 20 ∈ [0,6,8,12] := remove (a 20) 13 [0,6,8,12,13] t1 b2
  have b3 : a 21 ≠ 3 := exclude [0,1] (edge r63) (a 21) (a 23) 3 d23 c63 (by decide +kernel)
  have t3 : a 21 ∈ [0,4,6] := remove (a 21) 3 [0,3,4,6] d21 b3
  have b4 : a 21 ≠ 4 := exclude [0,1] (edge r63) (a 21) (a 23) 4 d23 c63 (by decide +kernel)
  have t4 : a 21 ∈ [0,6] := remove (a 21) 4 [0,4,6] t3 b4
  have b5 : a 29 ≠ 1 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 1 t4 c64 (by decide +kernel)
  have t5 : a 29 ∈ [0,8,9] := remove (a 29) 1 [0,1,8,9] d29 b5
  have b6 : a 29 ≠ 9 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 9 t4 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,8] := remove (a 29) 9 [0,8,9] t5 b6
  have b7 : a 22 ≠ 1 := exclude [0,1] (edge r65) (a 22) (a 23) 1 d23 c65 (by decide +kernel)
  have t7 : a 22 ∈ [0,10,11] := remove (a 22) 1 [0,1,10,11] d22 b7
  have b8 : a 22 ≠ 10 := exclude [0,1] (edge r65) (a 22) (a 23) 10 d23 c65 (by decide +kernel)
  have t8 : a 22 ∈ [0,11] := remove (a 22) 10 [0,10,11] t7 b8
  have b9 : a 30 ≠ 11 := exclude [0,11] (fun u v => edge r66 v u) (a 30) (a 22) 11 t8 c66 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,13,14,15,19,23] := remove (a 30) 11 [0,2,11,13,14,15,19,23] d30 b9
  have b10 : a 30 ≠ 13 := exclude [0,11] (fun u v => edge r66 v u) (a 30) (a 22) 13 t8 c66 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,14,15,19,23] := remove (a 30) 13 [0,2,13,14,15,19,23] t9 b10
  have b11 : a 30 ≠ 14 := exclude [0,11] (fun u v => edge r66 v u) (a 30) (a 22) 14 t8 c66 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,15,19,23] := remove (a 30) 14 [0,2,14,15,19,23] t10 b11
  have b12 : a 30 ≠ 15 := exclude [0,11] (fun u v => edge r66 v u) (a 30) (a 22) 15 t8 c66 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,19,23] := remove (a 30) 15 [0,2,15,19,23] t11 b12
  have b13 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,6,7,11] := remove (a 31) 5 [0,2,3,5,6,7,11] d31 b13
  have b14 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 6 d23 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,3,7,11] := remove (a 31) 6 [0,2,3,6,7,11] t13 b14
  have b15 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 7 d23 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,3,11] := remove (a 31) 7 [0,2,3,7,11] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t12 (t15)))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_201
