import PartitionData205_192
namespace PartitionCover205_192
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,4])
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 29 ∈ [0,1,8,9,22,23] := by
  have b0 : a 29 ≠ 4 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 6 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 7 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 10 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 11 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 12 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 13 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,8,9,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 14 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,8,9,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,1,8,9,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 15 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,8,9,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,1,8,9,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 16 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,8,9,17,18,19,20,21,22,23] := remove (a 29) 16 [0,1,8,9,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 17 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,8,9,18,19,20,21,22,23] := remove (a 29) 17 [0,1,8,9,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 18 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,8,9,19,20,21,22,23] := remove (a 29) 18 [0,1,8,9,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 19 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,8,9,20,21,22,23] := remove (a 29) 19 [0,1,8,9,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 20 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,8,9,21,22,23] := remove (a 29) 20 [0,1,8,9,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 21 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,8,9,22,23] := remove (a 29) 21 [0,1,8,9,21,22,23] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,8,9,22,23])
    (d13 : a 13 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0,4])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,1,8,9] ∧ a 30 ∈ [0,1,6,7] := by
  have b0 : a 29 ≠ 22 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,8,9,23] := remove (a 29) 22 [0,1,8,9,22,23] d29 b0
  have b1 : a 29 ≠ 23 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,8,9] := remove (a 29) 23 [0,1,8,9,23] t0 b1
  have b2 : a 30 ≠ 2 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d30 b2
  have b3 : a 30 ≠ 3 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 30 ≠ 4 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 30 ≠ 5 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 30 ≠ 8 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 30) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 30 ≠ 9 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 30) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 30 ≠ 10 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 30) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 30 ≠ 11 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 30) 11 [0,1,6,7,11,12,13,14,15,16,17] t8 b9
  have b10 : a 30 ≠ 12 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 30) 12 [0,1,6,7,12,13,14,15,16,17] t9 b10
  have b11 : a 30 ≠ 13 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,6,7,14,15,16,17] := remove (a 30) 13 [0,1,6,7,13,14,15,16,17] t10 b11
  have b12 : a 30 ≠ 14 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,6,7,15,16,17] := remove (a 30) 14 [0,1,6,7,14,15,16,17] t11 b12
  have b13 : a 30 ≠ 15 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,6,7,16,17] := remove (a 30) 15 [0,1,6,7,15,16,17] t12 b13
  have b14 : a 30 ≠ 16 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,6,7,17] := remove (a 30) 16 [0,1,6,7,16,17] t13 b14
  have b15 : a 30 ≠ 17 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,6,7] := remove (a 30) 17 [0,1,6,7,17] t14 b15
  exact And.intro t1 (t15)

theorem chunk10 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,6])
    (d18 : a 18 ∈ [0,1,3,5])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1,3,5])
    (d17 : a 17 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0])
    (d29 : a 29 ∈ [0,1,8,9])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 31 ∈ [0,1,2,3,6,7,8,10,11] ∧ a 18 ∈ [0,1] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0,1] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 29 ∈ [0,8,9] := by
  have b0 : a 31 ≠ 4 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 31) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b0
  have b1 : a 31 ≠ 5 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 31) 5 [0,1,2,3,5,6,7,8,9,10,11] t0 b1
  have b2 : a 31 ≠ 9 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2,3,6,7,8,10,11] := remove (a 31) 9 [0,1,2,3,6,7,8,9,10,11] t1 b2
  have b3 : a 18 ≠ 3 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 3 d16 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,5] := remove (a 18) 3 [0,1,3,5] d18 b3
  have b4 : a 18 ≠ 5 := exclude [0,1] (fun u v => edge r49 v u) (a 18) (a 16) 5 d16 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0,1] := remove (a 18) 5 [0,1,5] t3 b4
  have b5 : a 20 ≠ 1 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 1 d16 c50 (by decide +kernel)
  have t5 : a 20 ∈ [0,2] := remove (a 20) 1 [0,1,2] d20 b5
  have b6 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 2 [0,2] t5 b6
  have b7 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,5] := remove (a 21) 3 [0,1,3,5] d21 b7
  have b8 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t7 b8
  have b9 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 1 t4 c56 (by decide +kernel)
  have t9 : a 22 ∈ [0,2] := remove (a 22) 1 [0,1,2] d22 b9
  have b10 : a 22 ≠ 2 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 2 t4 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0] := remove (a 22) 2 [0,2] t9 b10
  have b11 : a 23 ≠ 2 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b11
  have b12 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t11 b12
  have b13 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] t12 b13
  have b14 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t13 b14
  have b15 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 1 t8 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,8,9] := remove (a 29) 1 [0,1,8,9] d29 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))))

theorem chunk11 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,8,9])
    (d21 : a 21 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,6,7,8,10,11])
    (d23 : a 23 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d24 : a 24 ∈ [0,1])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 29 ∈ [0,8] ∧ a 31 ∈ [0,1,6,7,10,11] ∧ a 25 ∈ [0,2,8,10,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 9 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,8] := remove (a 29) 9 [0,8,9] d29 b0
  have b1 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,3,6,7,8,10,11] := remove (a 31) 2 [0,1,2,3,6,7,8,10,11] d31 b1
  have b2 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 3 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,6,7,8,10,11] := remove (a 31) 3 [0,1,3,6,7,8,10,11] t1 b2
  have b3 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 8 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,6,7,10,11] := remove (a 31) 8 [0,1,6,7,8,10,11] t2 b3
  have b4 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b4
  have b5 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 25 ≠ 9 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 9 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 25 ≠ 11 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 11 d24 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,8,10,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 11 [0,2,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 25 ≠ 12 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 12 d24 c68 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,8,10,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 12 [0,2,8,10,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 25 ≠ 13 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 13 d24 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,2,8,10,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 13 [0,2,8,10,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 25 ≠ 14 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 14 d24 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,8,10,15,16,17,18,19,20,21,22,23] := remove (a 25) 14 [0,2,8,10,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 25 ≠ 15 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 15 d24 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,8,10,16,17,18,19,20,21,22,23] := remove (a 25) 15 [0,2,8,10,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t3 (t15))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_192
