import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,1,5,9,11])
    (d13 : a 13 ∈ [0,2,3])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,2] ∧ a 15 ∈ [0,5,9] ∧ a 29 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 28 ≠ 20 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 20 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,21,22,23] := remove (a 28) 20 [0,2,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 21 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 21 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,22,23] := remove (a 28) 21 [0,2,21,22,23] t0 b1
  have b2 : a 28 ≠ 22 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 22 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,23] := remove (a 28) 22 [0,2,22,23] t1 b2
  have b3 : a 28 ≠ 23 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 23 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2] := remove (a 28) 23 [0,2,23] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0,2,3] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t4 : a 15 ∈ [0,5,9,11] := remove (a 15) 1 [0,1,5,9,11] d15 b4
  have b5 : a 15 ≠ 11 := exclude [0,2,3] (fun u v => edge r43 v u) (a 15) (a 13) 11 d13 c43 (by decide +kernel)
  have t5 : a 15 ∈ [0,5,9] := remove (a 15) 11 [0,5,9,11] t4 b5
  have b6 : a 29 ≠ 1 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b6
  have b7 : a 29 ≠ 2 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 3 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 4 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 5 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 6 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 7 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 8 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 9 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 10 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t5 (t15))

theorem chunk21 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,2,3])
    (d15 : a 15 ∈ [0,5,9])
    (d14 : a 14 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,11,21] ∧ a 15 ∈ [0,5] ∧ a 30 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 12 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 13 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,11,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,11,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 14 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,11,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,11,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 15 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,11,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,11,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 16 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,11,17,18,19,20,21,22,23] := remove (a 29) 16 [0,11,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 17 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,11,18,19,20,21,22,23] := remove (a 29) 17 [0,11,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 18 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,11,19,20,21,22,23] := remove (a 29) 18 [0,11,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 19 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,11,20,21,22,23] := remove (a 29) 19 [0,11,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 20 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,11,21,22,23] := remove (a 29) 20 [0,11,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 22 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,11,21,23] := remove (a 29) 22 [0,11,21,22,23] t8 b9
  have b10 : a 29 ≠ 23 := exclude [0,2,3] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,11,21] := remove (a 29) 23 [0,11,21,23] t9 b10
  have b11 : a 15 ≠ 9 := exclude [0] (fun u v => edge r45 v u) (a 15) (a 14) 9 d14 c45 (by decide +kernel)
  have t11 : a 15 ∈ [0,5] := remove (a 15) 9 [0,5,9] d15 b11
  have b12 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b12
  have b13 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t10 (And.intro t11 (t15))

theorem chunk22 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,5])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,1,2,3,4,5] ∧ a 31 ∈ [0,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 12 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 13 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 30 ≠ 14 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 30) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 15 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 30) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 16 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 30) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 17 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 30) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t6 b7
  have b8 : a 30 ≠ 18 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 30) 18 [0,1,2,3,4,5,18,19,20,21,22,23] t7 b8
  have b9 : a 30 ≠ 19 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 30) 19 [0,1,2,3,4,5,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 20 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 20 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 30) 20 [0,1,2,3,4,5,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 21 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,2,3,4,5,22,23] := remove (a 30) 21 [0,1,2,3,4,5,21,22,23] t10 b11
  have b12 : a 30 ≠ 22 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,3,4,5,23] := remove (a 30) 22 [0,1,2,3,4,5,22,23] t11 b12
  have b13 : a 30 ≠ 23 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 23 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,3,4,5] := remove (a 30) 23 [0,1,2,3,4,5,23] t12 b13
  have b14 : a 31 ≠ 1 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b14
  have b15 : a 31 ≠ 3 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 31) 3 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t13 (t15)

theorem chunk23 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,5])
    (d17 : a 17 ∈ [0,3,4,8])
    (d16 : a 16 ∈ [0,8,12,22])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d20 : a 20 ∈ [0,1,12,13,18,19,20,21])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 31 ∈ [0,2,5,11] ∧ a 17 ∈ [0,4] ∧ a 18 ∈ [0,2,3,6,8,11] ∧ a 20 ∈ [0,1,13,18,19,21] := by
  have b0 : a 31 ≠ 4 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 31) 4 [0,2,4,5,6,7,8,9,10,11] d31 b0
  have b1 : a 31 ≠ 6 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,5,7,8,9,10,11] := remove (a 31) 6 [0,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 31 ≠ 7 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,2,5,8,9,10,11] := remove (a 31) 7 [0,2,5,7,8,9,10,11] t1 b2
  have b3 : a 31 ≠ 8 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,2,5,9,10,11] := remove (a 31) 8 [0,2,5,8,9,10,11] t2 b3
  have b4 : a 31 ≠ 9 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,5,10,11] := remove (a 31) 9 [0,2,5,9,10,11] t3 b4
  have b5 : a 31 ≠ 10 := exclude [0,5] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,2,5,11] := remove (a 31) 10 [0,2,5,10,11] t4 b5
  have b6 : a 17 ≠ 3 := exclude [0,8,12,22] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t6 : a 17 ∈ [0,4,8] := remove (a 17) 3 [0,3,4,8] d17 b6
  have b7 : a 17 ≠ 8 := exclude [0,8,12,22] (fun u v => edge r48 v u) (a 17) (a 16) 8 d16 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0,4] := remove (a 17) 8 [0,4,8] t6 b7
  have b8 : a 18 ≠ 1 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b8
  have b9 : a 18 ≠ 4 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 4 d16 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 18) 4 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 18 ≠ 5 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 5 d16 c49 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3,6,7,8,9,10,11] := remove (a 18) 5 [0,2,3,5,6,7,8,9,10,11] t9 b10
  have b11 : a 18 ≠ 7 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 7 d16 c49 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,3,6,8,9,10,11] := remove (a 18) 7 [0,2,3,6,7,8,9,10,11] t10 b11
  have b12 : a 18 ≠ 9 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 9 d16 c49 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,3,6,8,10,11] := remove (a 18) 9 [0,2,3,6,8,9,10,11] t11 b12
  have b13 : a 18 ≠ 10 := exclude [0,8,12,22] (fun u v => edge r49 v u) (a 18) (a 16) 10 d16 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,3,6,8,11] := remove (a 18) 10 [0,2,3,6,8,10,11] t12 b13
  have b14 : a 20 ≠ 12 := exclude [0,8,12,22] (fun u v => edge r50 v u) (a 20) (a 16) 12 d16 c50 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,13,18,19,20,21] := remove (a 20) 12 [0,1,12,13,18,19,20,21] d20 b14
  have b15 : a 20 ≠ 20 := exclude [0,8,12,22] (fun u v => edge r50 v u) (a 20) (a 16) 20 d16 c50 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,13,18,19,21] := remove (a 20) 20 [0,1,13,18,19,20,21] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t13 (t15)))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_216
