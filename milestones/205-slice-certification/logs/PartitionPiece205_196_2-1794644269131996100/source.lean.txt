import PartitionData205_196
namespace PartitionCover205_196
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0,2])
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 28 ∈ [0,2,12,18,21,22,23] := by
  have b0 : a 28 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 28 ≠ 5 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 28 ≠ 6 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 28 ≠ 7 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 28 ≠ 8 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 9 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 10 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 28 ≠ 11 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 28 ≠ 13 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 13 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,12,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 13 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 28 ≠ 14 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,12,15,16,17,18,19,20,21,22,23] := remove (a 28) 14 [0,2,12,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 28 ≠ 15 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,12,16,17,18,19,20,21,22,23] := remove (a 28) 15 [0,2,12,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 28 ≠ 16 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,12,17,18,19,20,21,22,23] := remove (a 28) 16 [0,2,12,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 28 ≠ 17 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,12,18,19,20,21,22,23] := remove (a 28) 17 [0,2,12,17,18,19,20,21,22,23] t12 b13
  have b14 : a 28 ≠ 19 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 19 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,12,18,20,21,22,23] := remove (a 28) 19 [0,2,12,18,19,20,21,22,23] t13 b14
  have b15 : a 28 ≠ 20 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 20 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,12,18,21,22,23] := remove (a 28) 20 [0,2,12,18,20,21,22,23] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,12,18,21,22,23])
    (d12 : a 12 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,4])
    (d13 : a 13 ∈ [0,2])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,2,12,18] ∧ a 15 ∈ [0,1] ∧ a 29 ∈ [0,1,3,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 28 ≠ 21 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 21 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,12,18,22,23] := remove (a 28) 21 [0,2,12,18,21,22,23] d28 b0
  have b1 : a 28 ≠ 22 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 22 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,12,18,23] := remove (a 28) 22 [0,2,12,18,22,23] t0 b1
  have b2 : a 28 ≠ 23 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 23 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,12,18] := remove (a 28) 23 [0,2,12,18,23] t1 b2
  have b3 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r43 v u) (a 15) (a 13) 2 d13 c43 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,4] := remove (a 15) 2 [0,1,2,4] d15 b3
  have b4 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r43 v u) (a 15) (a 13) 4 d13 c43 (by decide +kernel)
  have t4 : a 15 ∈ [0,1] := remove (a 15) 4 [0,1,4] t3 b4
  have b5 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b5
  have b6 : a 29 ≠ 4 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 5 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 6 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,1,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 7 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,1,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 8 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,1,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 9 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,1,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 10 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,1,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 11 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,1,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 12 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,3,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,1,3,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 13 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,3,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,1,3,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t4 (t15))

theorem chunk10 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,3,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,1])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 29 ∈ [0,1,3,15] ∧ a 30 ∈ [0,1,2,6,7,8] ∧ a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 14 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,3,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,1,3,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 16 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,3,15,17,18,19,20,21,22,23] := remove (a 29) 16 [0,1,3,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 17 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,3,15,18,19,20,21,22,23] := remove (a 29) 17 [0,1,3,15,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 18 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,3,15,19,20,21,22,23] := remove (a 29) 18 [0,1,3,15,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 19 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,3,15,20,21,22,23] := remove (a 29) 19 [0,1,3,15,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 20 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,3,15,21,22,23] := remove (a 29) 20 [0,1,3,15,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 21 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,3,15,22,23] := remove (a 29) 21 [0,1,3,15,21,22,23] t5 b6
  have b7 : a 29 ≠ 22 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,3,15,23] := remove (a 29) 22 [0,1,3,15,22,23] t6 b7
  have b8 : a 29 ≠ 23 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,3,15] := remove (a 29) 23 [0,1,3,15,23] t7 b8
  have b9 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b9
  have b10 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,2,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 30) 5 [0,1,2,5,6,7,8,9,10,11] t10 b11
  have b12 : a 30 ≠ 9 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,6,7,8,10,11] := remove (a 30) 9 [0,1,2,6,7,8,9,10,11] t11 b12
  have b13 : a 30 ≠ 10 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,6,7,8,11] := remove (a 30) 10 [0,1,2,6,7,8,10,11] t12 b13
  have b14 : a 30 ≠ 11 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,6,7,8] := remove (a 30) 11 [0,1,2,6,7,8,11] t13 b14
  have b15 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b15
  exact And.intro t8 (And.intro t14 (t15))

theorem chunk11 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,3])
    (d16 : a 16 ∈ [0,3])
    (d20 : a 20 ∈ [0,1,2])
    (d24 : a 24 ∈ [0,6,12,14])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d17 : a 17 ∈ [0,3])
    (d26 : a 26 ∈ [0,1,10,11,12,13,18,19,20,22])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] ∧ a 18 ∈ [0,3] ∧ a 20 ∈ [0] ∧ a 24 ∈ [0,6] ∧ a 19 ∈ [0,3] ∧ a 26 ∈ [0,1,12,13,18,19,20,22] := by
  have b0 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 20 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23] := remove (a 31) 20 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 21 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,22,23] := remove (a 31) 21 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23] t1 b2
  have b3 : a 31 ≠ 22 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 22 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,23] := remove (a 31) 22 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,22,23] t2 b3
  have b4 : a 31 ≠ 23 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 31) 23 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,23] t3 b4
  have b5 : a 18 ≠ 1 := exclude [0,3] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t5 : a 18 ∈ [0,3] := remove (a 18) 1 [0,1,3] d18 b5
  have b6 : a 20 ≠ 1 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 1 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,2] := remove (a 20) 1 [0,1,2] d20 b6
  have b7 : a 20 ≠ 2 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0] := remove (a 20) 2 [0,2] t6 b7
  have b8 : a 24 ≠ 12 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 12 d16 c51 (by decide +kernel)
  have t8 : a 24 ∈ [0,6,14] := remove (a 24) 12 [0,6,12,14] d24 b8
  have b9 : a 24 ≠ 14 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 14 d16 c51 (by decide +kernel)
  have t9 : a 24 ∈ [0,6] := remove (a 24) 14 [0,6,14] t8 b9
  have b10 : a 19 ≠ 1 := exclude [0,3] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t10 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b10
  have b11 : a 19 ≠ 2 := exclude [0,3] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t11 : a 19 ∈ [0,3,4,5] := remove (a 19) 2 [0,2,3,4,5] t10 b11
  have b12 : a 19 ≠ 4 := exclude [0,3] (fun u v => edge r52 v u) (a 19) (a 17) 4 d17 c52 (by decide +kernel)
  have t12 : a 19 ∈ [0,3,5] := remove (a 19) 4 [0,3,4,5] t11 b12
  have b13 : a 19 ≠ 5 := exclude [0,3] (fun u v => edge r52 v u) (a 19) (a 17) 5 d17 c52 (by decide +kernel)
  have t13 : a 19 ∈ [0,3] := remove (a 19) 5 [0,3,5] t12 b13
  have b14 : a 26 ≠ 10 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 10 t5 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,11,12,13,18,19,20,22] := remove (a 26) 10 [0,1,10,11,12,13,18,19,20,22] d26 b14
  have b15 : a 26 ≠ 11 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 11 t5 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,12,13,18,19,20,22] := remove (a 26) 11 [0,1,11,12,13,18,19,20,22] t14 b15
  exact And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_196
