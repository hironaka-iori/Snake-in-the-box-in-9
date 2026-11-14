import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,1,8,9,13,17] ∧ a 31 ∈ [0,1,9,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,8,9,11,12,13,14,15,16,17,18,19] := remove (a 30) 10 [0,1,8,9,10,11,12,13,14,15,16,17,18,19] d30 b0
  have b1 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,8,9,12,13,14,15,16,17,18,19] := remove (a 30) 11 [0,1,8,9,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 30 ≠ 12 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,8,9,13,14,15,16,17,18,19] := remove (a 30) 12 [0,1,8,9,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 30 ≠ 14 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,8,9,13,15,16,17,18,19] := remove (a 30) 14 [0,1,8,9,13,14,15,16,17,18,19] t2 b3
  have b4 : a 30 ≠ 15 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,8,9,13,16,17,18,19] := remove (a 30) 15 [0,1,8,9,13,15,16,17,18,19] t3 b4
  have b5 : a 30 ≠ 16 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,8,9,13,17,18,19] := remove (a 30) 16 [0,1,8,9,13,16,17,18,19] t4 b5
  have b6 : a 30 ≠ 18 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,8,9,13,17,19] := remove (a 30) 18 [0,1,8,9,13,17,18,19] t5 b6
  have b7 : a 30 ≠ 19 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,8,9,13,17] := remove (a 30) 19 [0,1,8,9,13,17,19] t6 b7
  have b8 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b8
  have b9 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 31 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,9,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (t15)

theorem chunk17 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,9,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,6,7])
    (d17 : a 17 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 31 ∈ [0,1,9] ∧ a 16 ∈ [0,1] ∧ a 18 ∈ [0,1,2,3,6,8,9,10,11,12,13,14,15,16,18] := by
  have b0 : a 31 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,9,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,1,9,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 12 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 12 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,9,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 12 [0,1,9,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 13 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,9,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 13 [0,1,9,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 14 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,9,15,16,17,18,19,20,21,22,23] := remove (a 31) 14 [0,1,9,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 15 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,9,16,17,18,19,20,21,22,23] := remove (a 31) 15 [0,1,9,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 16 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,9,17,18,19,20,21,22,23] := remove (a 31) 16 [0,1,9,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 17 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,9,18,19,20,21,22,23] := remove (a 31) 17 [0,1,9,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 18 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 18 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,9,19,20,21,22,23] := remove (a 31) 18 [0,1,9,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 19 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 19 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,9,20,21,22,23] := remove (a 31) 19 [0,1,9,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 20 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,9,21,22,23] := remove (a 31) 20 [0,1,9,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 21 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,9,22,23] := remove (a 31) 21 [0,1,9,21,22,23] t9 b10
  have b11 : a 31 ≠ 22 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 22 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,9,23] := remove (a 31) 22 [0,1,9,22,23] t10 b11
  have b12 : a 31 ≠ 23 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,9] := remove (a 31) 23 [0,1,9,23] t11 b12
  have b13 : a 16 ≠ 6 := exclude [0,1] (edge r48) (a 16) (a 17) 6 d17 c48 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,7] := remove (a 16) 6 [0,1,6,7] d16 b13
  have b14 : a 16 ≠ 7 := exclude [0,1] (edge r48) (a 16) (a 17) 7 d17 c48 (by decide +kernel)
  have t14 : a 16 ∈ [0,1] := remove (a 16) 7 [0,1,7] t13 b14
  have b15 : a 18 ≠ 4 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 4 t14 c49 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,2,3,6,8,9,10,11,12,13,14,15,16,18] := remove (a 18) 4 [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,18] d18 b15
  exact And.intro t12 (And.intro t14 (t15))

theorem chunk18 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3,6,8,9,10,11,12,13,14,15,16,18])
    (d16 : a 16 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d17 : a 17 ∈ [0,1])
    (d22 : a 22 ∈ [0,4])
    (d23 : a 23 ∈ [0,1,2])
    (d19 : a 19 ∈ [0,1])
    (c49 : edge r49 (a 16) (a 18)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 18 ∈ [0,2] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 18 ≠ 6 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 6 d16 c49 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,18] := remove (a 18) 6 [0,1,2,3,6,8,9,10,11,12,13,14,15,16,18] d18 b0
  have b1 : a 18 ≠ 8 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 8 d16 c49 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,18] := remove (a 18) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,18] t0 b1
  have b2 : a 18 ≠ 9 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 9 d16 c49 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,2,3,10,11,12,13,14,15,16,18] := remove (a 18) 9 [0,1,2,3,9,10,11,12,13,14,15,16,18] t1 b2
  have b3 : a 18 ≠ 10 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 10 d16 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,2,3,11,12,13,14,15,16,18] := remove (a 18) 10 [0,1,2,3,10,11,12,13,14,15,16,18] t2 b3
  have b4 : a 18 ≠ 11 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 11 d16 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,2,3,12,13,14,15,16,18] := remove (a 18) 11 [0,1,2,3,11,12,13,14,15,16,18] t3 b4
  have b5 : a 18 ≠ 12 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 12 d16 c49 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,2,3,13,14,15,16,18] := remove (a 18) 12 [0,1,2,3,12,13,14,15,16,18] t4 b5
  have b6 : a 18 ≠ 13 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 13 d16 c49 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,2,3,14,15,16,18] := remove (a 18) 13 [0,1,2,3,13,14,15,16,18] t5 b6
  have b7 : a 18 ≠ 14 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 14 d16 c49 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,2,3,15,16,18] := remove (a 18) 14 [0,1,2,3,14,15,16,18] t6 b7
  have b8 : a 18 ≠ 15 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 15 d16 c49 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,2,3,16,18] := remove (a 18) 15 [0,1,2,3,15,16,18] t7 b8
  have b9 : a 18 ≠ 16 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 16 d16 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,2,3,18] := remove (a 18) 16 [0,1,2,3,16,18] t8 b9
  have b10 : a 18 ≠ 18 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 18 d16 c49 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,2,3] := remove (a 18) 18 [0,1,2,3,18] t9 b10
  have b11 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b11
  have b12 : a 18 ≠ 1 := exclude [0,4] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] t10 b12
  have b13 : a 18 ≠ 3 := exclude [0,4] (edge r56) (a 18) (a 22) 3 d22 c56 (by decide +kernel)
  have t13 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t12 b13
  have b14 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] d23 b14
  have b15 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0] := remove (a 23) 2 [0,2] t14 b15
  exact And.intro t13 (And.intro t11 (t15))

theorem chunk19 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,2,4,6])
    (d20 : a 20 ∈ [0,12,14])
    (d21 : a 21 ∈ [0])
    (d22 : a 22 ∈ [0,4])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18])
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 19 ∈ [0] ∧ a 27 ∈ [0,2] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 29 ∈ [0,1,5,8,16,18] := by
  have b0 : a 19 ≠ 1 := exclude [0,2,4,6] (edge r59) (a 19) (a 27) 1 d27 c59 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b0
  have b1 : a 27 ≠ 4 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 4 t0 c59 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,6] := remove (a 27) 4 [0,2,4,6] d27 b1
  have b2 : a 27 ≠ 6 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 6 t0 c59 (by decide +kernel)
  have t2 : a 27 ∈ [0,2] := remove (a 27) 6 [0,2,6] t1 b2
  have b3 : a 20 ≠ 12 := exclude [0] (edge r60) (a 20) (a 21) 12 d21 c60 (by decide +kernel)
  have t3 : a 20 ∈ [0,14] := remove (a 20) 12 [0,12,14] d20 b3
  have b4 : a 20 ≠ 14 := exclude [0] (edge r60) (a 20) (a 21) 14 d21 c60 (by decide +kernel)
  have t4 : a 20 ∈ [0] := remove (a 20) 14 [0,14] t3 b4
  have b5 : a 22 ≠ 4 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 4 t4 c61 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 4 [0,4] d22 b5
  have b6 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 d21 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,14,16,18] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18] d29 b6
  have b7 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,14,16,18] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,14,16,18] t6 b7
  have b8 : a 29 ≠ 4 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 4 d21 c64 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,14,16,18] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,14,16,18] t7 b8
  have b9 : a 29 ≠ 6 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 6 d21 c64 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,5,7,8,9,10,11,12,14,16,18] := remove (a 29) 6 [0,1,5,6,7,8,9,10,11,12,14,16,18] t8 b9
  have b10 : a 29 ≠ 7 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,5,8,9,10,11,12,14,16,18] := remove (a 29) 7 [0,1,5,7,8,9,10,11,12,14,16,18] t9 b10
  have b11 : a 29 ≠ 9 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 9 d21 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,5,8,10,11,12,14,16,18] := remove (a 29) 9 [0,1,5,8,9,10,11,12,14,16,18] t10 b11
  have b12 : a 29 ≠ 10 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 10 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,5,8,11,12,14,16,18] := remove (a 29) 10 [0,1,5,8,10,11,12,14,16,18] t11 b12
  have b13 : a 29 ≠ 11 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 11 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,5,8,12,14,16,18] := remove (a 29) 11 [0,1,5,8,11,12,14,16,18] t12 b13
  have b14 : a 29 ≠ 12 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 12 d21 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,5,8,14,16,18] := remove (a 29) 12 [0,1,5,8,12,14,16,18] t13 b14
  have b15 : a 29 ≠ 14 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 14 d21 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,5,8,16,18] := remove (a 29) 14 [0,1,5,8,14,16,18] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t5 (t15))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_170
