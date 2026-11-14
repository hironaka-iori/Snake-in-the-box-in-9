import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,4])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0,2])
    (d18 : a 18 ∈ [0,1,3,4,6,7,8])
    (d16 : a 16 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (d17 : a 17 ∈ [0,2])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 30 ∈ [0,3,4,5] ∧ a 31 ∈ [0,1,4,5,6,7,9] ∧ a 18 ∈ [0,3] ∧ a 21 ∈ [0,2,3,4,5,6,7] := by
  have b0 : a 30 ≠ 2 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,2,3,4,5,6,7,8,9,10,11] d30 b0
  have b1 : a 30 ≠ 6 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,3,4,5,7,8,9,10,11] := remove (a 30) 6 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 30 ≠ 7 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,3,4,5,8,9,10,11] := remove (a 30) 7 [0,3,4,5,7,8,9,10,11] t1 b2
  have b3 : a 30 ≠ 8 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,3,4,5,9,10,11] := remove (a 30) 8 [0,3,4,5,8,9,10,11] t2 b3
  have b4 : a 30 ≠ 9 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,3,4,5,10,11] := remove (a 30) 9 [0,3,4,5,9,10,11] t3 b4
  have b5 : a 30 ≠ 10 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,3,4,5,11] := remove (a 30) 10 [0,3,4,5,10,11] t4 b5
  have b6 : a 30 ≠ 11 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,3,4,5] := remove (a 30) 11 [0,3,4,5,11] t5 b6
  have b7 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9] d31 b7
  have b8 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,4,5,6,7,8,9] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9] t7 b8
  have b9 : a 31 ≠ 8 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,4,5,6,7,9] := remove (a 31) 8 [0,1,4,5,6,7,8,9] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t10 : a 18 ∈ [0,3,4,6,7,8] := remove (a 18) 1 [0,1,3,4,6,7,8] d18 b10
  have b11 : a 18 ≠ 4 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 4 d16 c49 (by decide +kernel)
  have t11 : a 18 ∈ [0,3,6,7,8] := remove (a 18) 4 [0,3,4,6,7,8] t10 b11
  have b12 : a 18 ≠ 6 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 6 d16 c49 (by decide +kernel)
  have t12 : a 18 ∈ [0,3,7,8] := remove (a 18) 6 [0,3,6,7,8] t11 b12
  have b13 : a 18 ≠ 7 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 7 d16 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,3,8] := remove (a 18) 7 [0,3,7,8] t12 b13
  have b14 : a 18 ≠ 8 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 8 d16 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0,3] := remove (a 18) 8 [0,3,8] t13 b14
  have b15 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,2,3,4,5,6,7] := remove (a 21) 1 [0,1,2,3,4,5,6,7] d21 b15
  exact And.intro t6 (And.intro t9 (And.intro t14 (t15)))

theorem chunk13 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,2,3,4,5,6,7])
    (d17 : a 17 ∈ [0,2])
    (d19 : a 19 ∈ [0,2,6,7,10,11])
    (d18 : a 18 ∈ [0,3])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 21 ∈ [0,4] ∧ a 19 ∈ [0,6] ∧ a 22 ∈ [0,1,4,10,11] := by
  have b0 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,3,4,5,6,7] := remove (a 21) 2 [0,2,3,4,5,6,7] d21 b0
  have b1 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0,4,5,6,7] := remove (a 21) 3 [0,3,4,5,6,7] t0 b1
  have b2 : a 21 ≠ 5 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t2 : a 21 ∈ [0,4,6,7] := remove (a 21) 5 [0,4,5,6,7] t1 b2
  have b3 : a 21 ≠ 6 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 6 d17 c53 (by decide +kernel)
  have t3 : a 21 ∈ [0,4,7] := remove (a 21) 6 [0,4,6,7] t2 b3
  have b4 : a 21 ≠ 7 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 7 d17 c53 (by decide +kernel)
  have t4 : a 21 ∈ [0,4] := remove (a 21) 7 [0,4,7] t3 b4
  have b5 : a 19 ≠ 2 := exclude [0,3] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,6,7,10,11] := remove (a 19) 2 [0,2,6,7,10,11] d19 b5
  have b6 : a 19 ≠ 7 := exclude [0,3] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,6,10,11] := remove (a 19) 7 [0,6,7,10,11] t5 b6
  have b7 : a 19 ≠ 10 := exclude [0,3] (fun u v => edge r55 v u) (a 19) (a 18) 10 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,6,11] := remove (a 19) 10 [0,6,10,11] t6 b7
  have b8 : a 19 ≠ 11 := exclude [0,3] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,6] := remove (a 19) 11 [0,6,11] t7 b8
  have b9 : a 22 ≠ 2 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b9
  have b10 : a 22 ≠ 3 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 22 ≠ 5 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,4,6,7,8,9,10,11] := remove (a 22) 5 [0,1,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 22 ≠ 6 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 6 d18 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,4,7,8,9,10,11] := remove (a 22) 6 [0,1,4,6,7,8,9,10,11] t11 b12
  have b13 : a 22 ≠ 7 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 7 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,4,8,9,10,11] := remove (a 22) 7 [0,1,4,7,8,9,10,11] t12 b13
  have b14 : a 22 ≠ 8 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 8 d18 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,4,9,10,11] := remove (a 22) 8 [0,1,4,8,9,10,11] t13 b14
  have b15 : a 22 ≠ 9 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 9 d18 c56 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,4,10,11] := remove (a 22) 9 [0,1,4,9,10,11] t14 b15
  exact And.intro t4 (And.intro t8 (t15))

theorem chunk14 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,4,10,11])
    (d18 : a 18 ∈ [0,3])
    (d26 : a 26 ∈ [0,4,9,10])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (d19 : a 19 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,9,10])
    (d20 : a 20 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,4])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    : a 22 ∈ [0,1,10] ∧ a 26 ∈ [0,10] ∧ a 23 ∈ [0,1,2,3,4,6,12,13] ∧ a 27 ∈ [0,9] ∧ a 20 ∈ [0,2] := by
  have b0 : a 22 ≠ 11 := exclude [0,3] (fun u v => edge r56 v u) (a 22) (a 18) 11 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,4,10] := remove (a 22) 11 [0,1,4,10,11] d22 b0
  have b1 : a 26 ≠ 4 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,9,10] := remove (a 26) 4 [0,4,9,10] d26 b1
  have b2 : a 26 ≠ 9 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 9 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,10] := remove (a 26) 9 [0,9,10] t1 b2
  have b3 : a 23 ≠ 5 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15] := remove (a 23) 5 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d23 b3
  have b4 : a 23 ≠ 7 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15] := remove (a 23) 7 [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15] t3 b4
  have b5 : a 23 ≠ 8 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 8 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,3,4,6,9,10,11,12,13,14,15] := remove (a 23) 8 [0,1,2,3,4,6,8,9,10,11,12,13,14,15] t4 b5
  have b6 : a 23 ≠ 9 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 9 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,3,4,6,10,11,12,13,14,15] := remove (a 23) 9 [0,1,2,3,4,6,9,10,11,12,13,14,15] t5 b6
  have b7 : a 23 ≠ 10 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 10 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,2,3,4,6,11,12,13,14,15] := remove (a 23) 10 [0,1,2,3,4,6,10,11,12,13,14,15] t6 b7
  have b8 : a 23 ≠ 11 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 11 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,2,3,4,6,12,13,14,15] := remove (a 23) 11 [0,1,2,3,4,6,11,12,13,14,15] t7 b8
  have b9 : a 23 ≠ 14 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 14 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,3,4,6,12,13,15] := remove (a 23) 14 [0,1,2,3,4,6,12,13,14,15] t8 b9
  have b10 : a 23 ≠ 15 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 15 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,3,4,6,12,13] := remove (a 23) 15 [0,1,2,3,4,6,12,13,15] t9 b10
  have b11 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t11 : a 27 ∈ [0,9,10] := remove (a 27) 1 [0,1,9,10] d27 b11
  have b12 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r59 v u) (a 27) (a 19) 10 d19 c59 (by decide +kernel)
  have t12 : a 27 ∈ [0,9] := remove (a 27) 10 [0,9,10] t11 b12
  have b13 : a 20 ≠ 1 := exclude [0,4] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t13 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b13
  have b14 : a 20 ≠ 3 := exclude [0,4] (edge r60) (a 20) (a 21) 3 d21 c60 (by decide +kernel)
  have t14 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t13 b14
  have b15 : a 22 ≠ 4 := exclude [0,2] (fun u v => edge r61 v u) (a 22) (a 20) 4 t14 c61 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,10] := remove (a 22) 4 [0,1,4,10] t0 b15
  exact And.intro t15 (And.intro t2 (And.intro t10 (And.intro t12 (t14))))

theorem chunk15 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,10])
    (d20 : a 20 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,14,15,16,18,19])
    (d23 : a 23 ∈ [0,1,2,3,4,6,12,13])
    (d21 : a 21 ∈ [0,4])
    (d29 : a 29 ∈ [0,1,4,5])
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    : a 22 ∈ [0,1] ∧ a 28 ∈ [0,4,5,8,10,11,14,19] ∧ a 23 ∈ [0,1,6] ∧ a 29 ∈ [0,4] := by
  have b0 : a 22 ≠ 10 := exclude [0,2] (fun u v => edge r61 v u) (a 22) (a 20) 10 d20 c61 (by decide +kernel)
  have t0 : a 22 ∈ [0,1] := remove (a 22) 10 [0,1,10] d22 b0
  have b1 : a 28 ≠ 1 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 1 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11,14,15,16,18,19] := remove (a 28) 1 [0,1,2,4,5,6,7,8,9,10,11,14,15,16,18,19] d28 b1
  have b2 : a 28 ≠ 2 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t2 : a 28 ∈ [0,4,5,6,7,8,9,10,11,14,15,16,18,19] := remove (a 28) 2 [0,2,4,5,6,7,8,9,10,11,14,15,16,18,19] t1 b2
  have b3 : a 28 ≠ 6 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 6 d20 c62 (by decide +kernel)
  have t3 : a 28 ∈ [0,4,5,7,8,9,10,11,14,15,16,18,19] := remove (a 28) 6 [0,4,5,6,7,8,9,10,11,14,15,16,18,19] t2 b3
  have b4 : a 28 ≠ 7 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 7 d20 c62 (by decide +kernel)
  have t4 : a 28 ∈ [0,4,5,8,9,10,11,14,15,16,18,19] := remove (a 28) 7 [0,4,5,7,8,9,10,11,14,15,16,18,19] t3 b4
  have b5 : a 28 ≠ 9 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 9 d20 c62 (by decide +kernel)
  have t5 : a 28 ∈ [0,4,5,8,10,11,14,15,16,18,19] := remove (a 28) 9 [0,4,5,8,9,10,11,14,15,16,18,19] t4 b5
  have b6 : a 28 ≠ 15 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 15 d20 c62 (by decide +kernel)
  have t6 : a 28 ∈ [0,4,5,8,10,11,14,16,18,19] := remove (a 28) 15 [0,4,5,8,10,11,14,15,16,18,19] t5 b6
  have b7 : a 28 ≠ 16 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 16 d20 c62 (by decide +kernel)
  have t7 : a 28 ∈ [0,4,5,8,10,11,14,18,19] := remove (a 28) 16 [0,4,5,8,10,11,14,16,18,19] t6 b7
  have b8 : a 28 ≠ 18 := exclude [0,2] (fun u v => edge r62 v u) (a 28) (a 20) 18 d20 c62 (by decide +kernel)
  have t8 : a 28 ∈ [0,4,5,8,10,11,14,19] := remove (a 28) 18 [0,4,5,8,10,11,14,18,19] t7 b8
  have b9 : a 23 ≠ 3 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 3 d21 c63 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,2,4,6,12,13] := remove (a 23) 3 [0,1,2,3,4,6,12,13] d23 b9
  have b10 : a 23 ≠ 4 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 4 d21 c63 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,6,12,13] := remove (a 23) 4 [0,1,2,4,6,12,13] t9 b10
  have b11 : a 23 ≠ 12 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 12 d21 c63 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,6,13] := remove (a 23) 12 [0,1,2,6,12,13] t10 b11
  have b12 : a 23 ≠ 13 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 13 d21 c63 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,6] := remove (a 23) 13 [0,1,2,6,13] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,4] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,4,5] := remove (a 29) 1 [0,1,4,5] d29 b13
  have b14 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,4] := remove (a 29) 5 [0,4,5] t13 b14
  have b15 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r65 v u) (a 23) (a 22) 2 t0 c65 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,6] := remove (a 23) 2 [0,1,2,6] t12 b15
  exact And.intro t0 (And.intro t8 (And.intro t15 (t14)))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_185
