import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,10,11,22,23])
    (d13 : a 13 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d15 : a 15 ∈ [0,1])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 29 ∈ [0,1,10,11] ∧ a 30 ∈ [0,2,5,8] ∧ a 31 ∈ [0,5,6,12,13,14,15,16,17] := by
  have b0 : a 29 ≠ 22 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,10,11,23] := remove (a 29) 22 [0,1,10,11,22,23] d29 b0
  have b1 : a 29 ≠ 23 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,10,11] := remove (a 29) 23 [0,1,10,11,23] t0 b1
  have b2 : a 30 ≠ 1 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,3,4,5,6,7,8] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8] d30 b2
  have b3 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,4,5,6,7,8] := remove (a 30) 3 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,5,6,7,8] := remove (a 30) 4 [0,2,4,5,6,7,8] t3 b4
  have b5 : a 30 ≠ 6 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,5,7,8] := remove (a 30) 6 [0,2,5,6,7,8] t4 b5
  have b6 : a 30 ≠ 7 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,5,8] := remove (a 30) 7 [0,2,5,7,8] t5 b6
  have b7 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d31 b7
  have b8 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,5,6,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 7 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,5,6,9,10,11,12,13,14,15,16,17] := remove (a 31) 8 [0,5,6,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 31 ≠ 9 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,5,6,10,11,12,13,14,15,16,17] := remove (a 31) 9 [0,5,6,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 31 ≠ 10 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,5,6,11,12,13,14,15,16,17] := remove (a 31) 10 [0,5,6,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 31 ≠ 11 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,5,6,12,13,14,15,16,17] := remove (a 31) 11 [0,5,6,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t6 (t15))

theorem chunk17 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,5,6,12,13,14,15,16,17])
    (d15 : a 15 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0,1,2,9,10,11])
    (d24 : a 24 ∈ [0,6,8,9])
    (d21 : a 21 ∈ [0,1,6,7,18,19])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 31 ∈ [0,5,6,12] ∧ a 16 ∈ [0,1] ∧ a 17 ∈ [0,3] ∧ a 20 ∈ [0,1,9,10] ∧ a 24 ∈ [0,9] ∧ a 21 ∈ [0,6,7,18,19] := by
  have b0 : a 31 ≠ 13 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,5,6,12,14,15,16,17] := remove (a 31) 13 [0,5,6,12,13,14,15,16,17] d31 b0
  have b1 : a 31 ≠ 14 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,5,6,12,15,16,17] := remove (a 31) 14 [0,5,6,12,14,15,16,17] t0 b1
  have b2 : a 31 ≠ 15 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,5,6,12,16,17] := remove (a 31) 15 [0,5,6,12,15,16,17] t1 b2
  have b3 : a 31 ≠ 16 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,5,6,12,17] := remove (a 31) 16 [0,5,6,12,16,17] t2 b3
  have b4 : a 31 ≠ 17 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,5,6,12] := remove (a 31) 17 [0,5,6,12,17] t3 b4
  have b5 : a 16 ≠ 2 := exclude [0,1,2,3,4,5] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b5
  have b6 : a 16 ≠ 3 := exclude [0,1,2,3,4,5] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t6 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t5 b6
  have b7 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 1 t6 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0,2,3,4,5] := remove (a 17) 1 [0,1,2,3,4,5] d17 b7
  have b8 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 2 t6 c48 (by decide +kernel)
  have t8 : a 17 ∈ [0,3,4,5] := remove (a 17) 2 [0,2,3,4,5] t7 b8
  have b9 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 4 t6 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,5] := remove (a 17) 4 [0,3,4,5] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 5 t6 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,3] := remove (a 17) 5 [0,3,5] t9 b10
  have b11 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 2 t6 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,9,10,11] := remove (a 20) 2 [0,1,2,9,10,11] d20 b11
  have b12 : a 20 ≠ 11 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 11 t6 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,9,10] := remove (a 20) 11 [0,1,9,10,11] t11 b12
  have b13 : a 24 ≠ 6 := exclude [0,1] (fun u v => edge r51 v u) (a 24) (a 16) 6 t6 c51 (by decide +kernel)
  have t13 : a 24 ∈ [0,8,9] := remove (a 24) 6 [0,6,8,9] d24 b13
  have b14 : a 24 ≠ 8 := exclude [0,1] (fun u v => edge r51 v u) (a 24) (a 16) 8 t6 c51 (by decide +kernel)
  have t14 : a 24 ∈ [0,9] := remove (a 24) 8 [0,8,9] t13 b14
  have b15 : a 21 ≠ 1 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 1 t10 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,6,7,18,19] := remove (a 21) 1 [0,1,6,7,18,19] d21 b15
  exact And.intro t4 (And.intro t6 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk18 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,6,7,18,19])
    (d17 : a 17 ∈ [0,3])
    (d18 : a 18 ∈ [0,4,12,14])
    (d19 : a 19 ∈ [0,5,6,9])
    (d26 : a 26 ∈ [0,2,3,5])
    (d23 : a 23 ∈ [0,1,2,3,4,7,9,10,11])
    (d20 : a 20 ∈ [0,1,9,10])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 21 ∈ [0,18] ∧ a 18 ∈ [0,12] ∧ a 19 ∈ [0,6] ∧ a 26 ∈ [0,5] ∧ a 23 ∈ [0,1,9,10] ∧ a 20 ∈ [0,9] := by
  have b0 : a 21 ≠ 19 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 19 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,6,7,18] := remove (a 21) 19 [0,6,7,18,19] d21 b0
  have b1 : a 18 ≠ 4 := exclude [0,5,6,9] (edge r55) (a 18) (a 19) 4 d19 c55 (by decide +kernel)
  have t1 : a 18 ∈ [0,12,14] := remove (a 18) 4 [0,4,12,14] d18 b1
  have b2 : a 18 ≠ 14 := exclude [0,5,6,9] (edge r55) (a 18) (a 19) 14 d19 c55 (by decide +kernel)
  have t2 : a 18 ∈ [0,12] := remove (a 18) 14 [0,12,14] t1 b2
  have b3 : a 19 ≠ 5 := exclude [0,12] (fun u v => edge r55 v u) (a 19) (a 18) 5 t2 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,6,9] := remove (a 19) 5 [0,5,6,9] d19 b3
  have b4 : a 19 ≠ 9 := exclude [0,12] (fun u v => edge r55 v u) (a 19) (a 18) 9 t2 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,6] := remove (a 19) 9 [0,6,9] t3 b4
  have b5 : a 26 ≠ 2 := exclude [0,12] (fun u v => edge r57 v u) (a 26) (a 18) 2 t2 c57 (by decide +kernel)
  have t5 : a 26 ∈ [0,3,5] := remove (a 26) 2 [0,2,3,5] d26 b5
  have b6 : a 26 ≠ 3 := exclude [0,12] (fun u v => edge r57 v u) (a 26) (a 18) 3 t2 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,5] := remove (a 26) 3 [0,3,5] t5 b6
  have b7 : a 23 ≠ 2 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 2 t4 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,3,4,7,9,10,11] := remove (a 23) 2 [0,1,2,3,4,7,9,10,11] d23 b7
  have b8 : a 23 ≠ 3 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 3 t4 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,4,7,9,10,11] := remove (a 23) 3 [0,1,3,4,7,9,10,11] t7 b8
  have b9 : a 23 ≠ 4 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 4 t4 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,7,9,10,11] := remove (a 23) 4 [0,1,4,7,9,10,11] t8 b9
  have b10 : a 23 ≠ 7 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 7 t4 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,9,10,11] := remove (a 23) 7 [0,1,7,9,10,11] t9 b10
  have b11 : a 23 ≠ 11 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 11 t4 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,9,10] := remove (a 23) 11 [0,1,9,10,11] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0,6,7,18] (edge r60) (a 20) (a 21) 1 t0 c60 (by decide +kernel)
  have t12 : a 20 ∈ [0,9,10] := remove (a 20) 1 [0,1,9,10] d20 b12
  have b13 : a 20 ≠ 10 := exclude [0,6,7,18] (edge r60) (a 20) (a 21) 10 t0 c60 (by decide +kernel)
  have t13 : a 20 ∈ [0,9] := remove (a 20) 10 [0,9,10] t12 b13
  have b14 : a 21 ≠ 6 := exclude [0,9] (fun u v => edge r60 v u) (a 21) (a 20) 6 t13 c60 (by decide +kernel)
  have t14 : a 21 ∈ [0,7,18] := remove (a 21) 6 [0,6,7,18] t0 b14
  have b15 : a 21 ≠ 7 := exclude [0,9] (fun u v => edge r60 v u) (a 21) (a 20) 7 t13 c60 (by decide +kernel)
  have t15 : a 21 ∈ [0,18] := remove (a 21) 7 [0,7,18] t14 b15
  exact And.intro t15 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t11 (t13)))))

theorem chunk19 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,4])
    (d20 : a 20 ∈ [0,9])
    (d29 : a 29 ∈ [0,1,10,11])
    (d21 : a 21 ∈ [0,18])
    (d23 : a 23 ∈ [0,1,9,10])
    (d22 : a 22 ∈ [0,11])
    (d25 : a 25 ∈ [0,10,18,22])
    (d24 : a 24 ∈ [0,9])
    (d27 : a 27 ∈ [0,3,7,8])
    (d30 : a 30 ∈ [0,2,5,8])
    (d26 : a 26 ∈ [0,5])
    (d31 : a 31 ∈ [0,5,6,12])
    (d3 : a 3 ∈ [0,5,6,11])
    (d11 : a 11 ∈ [0,6])
    (d5 : a 5 ∈ [0,4,20,22])
    (d4 : a 4 ∈ [0,9])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 28 ∈ [0,4] ∧ a 29 ∈ [0,10] ∧ a 23 ∈ [0,9] ∧ a 25 ∈ [0,10] ∧ a 27 ∈ [0,8] ∧ a 30 ∈ [0,2] ∧ a 31 ∈ [0,5] ∧ a 3 ∈ [0,6] ∧ a 5 ∈ [0,20,22] := by
  have b0 : a 28 ≠ 1 := exclude [0,9] (fun u v => edge r62 v u) (a 28) (a 20) 1 d20 c62 (by decide +kernel)
  have t0 : a 28 ∈ [0,4] := remove (a 28) 1 [0,1,4] d28 b0
  have b1 : a 29 ≠ 1 := exclude [0,18] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,10,11] := remove (a 29) 1 [0,1,10,11] d29 b1
  have b2 : a 29 ≠ 11 := exclude [0,18] (fun u v => edge r64 v u) (a 29) (a 21) 11 d21 c64 (by decide +kernel)
  have t2 : a 29 ∈ [0,10] := remove (a 29) 11 [0,10,11] t1 b2
  have b3 : a 23 ≠ 1 := exclude [0,11] (fun u v => edge r65 v u) (a 23) (a 22) 1 d22 c65 (by decide +kernel)
  have t3 : a 23 ∈ [0,9,10] := remove (a 23) 1 [0,1,9,10] d23 b3
  have b4 : a 23 ≠ 10 := exclude [0,11] (fun u v => edge r65 v u) (a 23) (a 22) 10 d22 c65 (by decide +kernel)
  have t4 : a 23 ∈ [0,9] := remove (a 23) 10 [0,9,10] t3 b4
  have b5 : a 25 ≠ 18 := exclude [0,9] (fun u v => edge r68 v u) (a 25) (a 24) 18 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,10,22] := remove (a 25) 18 [0,10,18,22] d25 b5
  have b6 : a 25 ≠ 22 := exclude [0,9] (fun u v => edge r68 v u) (a 25) (a 24) 22 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,10] := remove (a 25) 22 [0,10,22] t5 b6
  have b7 : a 27 ≠ 3 := exclude [0,10] (fun u v => edge r71 v u) (a 27) (a 25) 3 t6 c71 (by decide +kernel)
  have t7 : a 27 ∈ [0,7,8] := remove (a 27) 3 [0,3,7,8] d27 b7
  have b8 : a 27 ≠ 7 := exclude [0,10] (fun u v => edge r71 v u) (a 27) (a 25) 7 t6 c71 (by decide +kernel)
  have t8 : a 27 ∈ [0,8] := remove (a 27) 7 [0,7,8] t7 b8
  have b9 : a 30 ≠ 5 := exclude [0,5] (fun u v => edge r74 v u) (a 30) (a 26) 5 d26 c74 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,8] := remove (a 30) 5 [0,2,5,8] d30 b9
  have b10 : a 30 ≠ 8 := exclude [0,5] (fun u v => edge r74 v u) (a 30) (a 26) 8 d26 c74 (by decide +kernel)
  have t10 : a 30 ∈ [0,2] := remove (a 30) 8 [0,2,8] t9 b10
  have b11 : a 31 ≠ 6 := exclude [0,8] (fun u v => edge r75 v u) (a 31) (a 27) 6 t8 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0,5,12] := remove (a 31) 6 [0,5,6,12] d31 b11
  have b12 : a 31 ≠ 12 := exclude [0,8] (fun u v => edge r75 v u) (a 31) (a 27) 12 t8 c75 (by decide +kernel)
  have t12 : a 31 ∈ [0,5] := remove (a 31) 12 [0,5,12] t11 b12
  have b13 : a 3 ≠ 5 := exclude [0,6] (edge r14) (a 3) (a 11) 5 d11 c14 (by decide +kernel)
  have t13 : a 3 ∈ [0,6,11] := remove (a 3) 5 [0,5,6,11] d3 b13
  have b14 : a 3 ≠ 11 := exclude [0,6] (edge r14) (a 3) (a 11) 11 d11 c14 (by decide +kernel)
  have t14 : a 3 ∈ [0,6] := remove (a 3) 11 [0,6,11] t13 b14
  have b15 : a 5 ≠ 4 := exclude [0,9] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t15 : a 5 ∈ [0,20,22] := remove (a 5) 4 [0,4,20,22] d5 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_187
