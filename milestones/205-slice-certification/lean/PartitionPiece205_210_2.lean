import PartitionData205_210
namespace PartitionCover205_210
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0,12])
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 28 ∈ [0,10,12,14,22,23] := by
  have b0 : a 28 ≠ 3 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 28 ≠ 5 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 28 ≠ 6 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 28 ≠ 7 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 28 ≠ 8 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 9 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 11 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,10,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 11 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 28 ≠ 13 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 13 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,10,12,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 13 [0,10,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 28 ≠ 15 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,10,12,14,16,17,18,19,20,21,22,23] := remove (a 28) 15 [0,10,12,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 28 ≠ 16 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,10,12,14,17,18,19,20,21,22,23] := remove (a 28) 16 [0,10,12,14,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 28 ≠ 17 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,10,12,14,18,19,20,21,22,23] := remove (a 28) 17 [0,10,12,14,17,18,19,20,21,22,23] t10 b11
  have b12 : a 28 ≠ 18 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 18 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,10,12,14,19,20,21,22,23] := remove (a 28) 18 [0,10,12,14,18,19,20,21,22,23] t11 b12
  have b13 : a 28 ≠ 19 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 19 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,10,12,14,20,21,22,23] := remove (a 28) 19 [0,10,12,14,19,20,21,22,23] t12 b13
  have b14 : a 28 ≠ 20 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 20 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,10,12,14,21,22,23] := remove (a 28) 20 [0,10,12,14,20,21,22,23] t13 b14
  have b15 : a 28 ≠ 21 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 21 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,10,12,14,22,23] := remove (a 28) 21 [0,10,12,14,21,22,23] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,10,12,14,22,23])
    (d12 : a 12 ∈ [0,12])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,1,12,13])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,1])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 28 ∈ [0,10,12,14] ∧ a 29 ∈ [0,1,4,5,7,8] ∧ a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22] ∧ a 31 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 28 ≠ 22 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 22 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,10,12,14,23] := remove (a 28) 22 [0,10,12,14,22,23] d28 b0
  have b1 : a 28 ≠ 23 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 23 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,10,12,14] := remove (a 28) 23 [0,10,12,14,23] t0 b1
  have b2 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b2
  have b3 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 29) 6 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,4,5,7,8,10,11] := remove (a 29) 9 [0,1,4,5,7,8,9,10,11] t4 b5
  have b6 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,4,5,7,8,11] := remove (a 29) 10 [0,1,4,5,7,8,10,11] t5 b6
  have b7 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,4,5,7,8] := remove (a 29) 11 [0,1,4,5,7,8,11] t6 b7
  have b8 : a 30 ≠ 2 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b8
  have b9 : a 30 ≠ 8 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 15 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,17,18,19,20,21,22,23] := remove (a 30) 15 [0,1,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 17 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,18,19,20,21,22,23] := remove (a 30) 17 [0,1,3,4,5,6,7,9,10,11,12,13,14,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 30 ≠ 18 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22,23] := remove (a 30) 18 [0,1,3,4,5,6,7,9,10,11,12,13,14,16,18,19,20,21,22,23] t11 b12
  have b13 : a 30 ≠ 23 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 23 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22] := remove (a 30) 23 [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b14
  have b15 : a 31 ≠ 9 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t7 (And.intro t13 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,8])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 31 ∈ [0,1,2,3,4,5,6,7] ∧ a 16 ∈ [0,1] := by
  have b0 : a 31 ≠ 10 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 11 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,1,2,3,4,5,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 12 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 12 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2,3,4,5,6,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 12 [0,1,2,3,4,5,6,7,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 13 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,4,5,6,7,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 13 [0,1,2,3,4,5,6,7,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 14 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3,4,5,6,7,15,16,17,18,19,20,21,22,23] := remove (a 31) 14 [0,1,2,3,4,5,6,7,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 15 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] := remove (a 31) 15 [0,1,2,3,4,5,6,7,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 16 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,2,3,4,5,6,7,17,18,19,20,21,22,23] := remove (a 31) 16 [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 17 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,3,4,5,6,7,18,19,20,21,22,23] := remove (a 31) 17 [0,1,2,3,4,5,6,7,17,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 18 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 18 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,3,4,5,6,7,19,20,21,22,23] := remove (a 31) 18 [0,1,2,3,4,5,6,7,18,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 19 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 19 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,2,3,4,5,6,7,20,21,22,23] := remove (a 31) 19 [0,1,2,3,4,5,6,7,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 20 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,2,3,4,5,6,7,21,22,23] := remove (a 31) 20 [0,1,2,3,4,5,6,7,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 21 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,2,3,4,5,6,7,22,23] := remove (a 31) 21 [0,1,2,3,4,5,6,7,21,22,23] t10 b11
  have b12 : a 31 ≠ 22 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 22 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,2,3,4,5,6,7,23] := remove (a 31) 22 [0,1,2,3,4,5,6,7,22,23] t11 b12
  have b13 : a 31 ≠ 23 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,2,3,4,5,6,7] := remove (a 31) 23 [0,1,2,3,4,5,6,7,23] t12 b13
  have b14 : a 16 ≠ 2 := exclude [0,8] (edge r51) (a 16) (a 24) 2 d24 c51 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b14
  have b15 : a 16 ≠ 3 := exclude [0,8] (edge r51) (a 16) (a 24) 3 d24 c51 (by decide +kernel)
  have t15 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t14 b15
  exact And.intro t13 (t15)

theorem chunk11 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,3,5,6])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,1,6,7,10,11,12,13])
    (d22 : a 22 ∈ [0,1,2,3,4,5,7,9,10,11])
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 17 ∈ [0,2] ∧ a 25 ∈ [0,8] ∧ a 18 ∈ [0,6,10,12] := by
  have b0 : a 17 ≠ 1 := exclude [0,3,5,6] (edge r52) (a 17) (a 19) 1 d19 c52 (by decide +kernel)
  have t0 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b0
  have b1 : a 17 ≠ 3 := exclude [0,3,5,6] (edge r52) (a 17) (a 19) 3 d19 c52 (by decide +kernel)
  have t1 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 1 t1 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b2
  have b3 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 2 t1 c54 (by decide +kernel)
  have t3 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 3 t1 c54 (by decide +kernel)
  have t4 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 4 t1 c54 (by decide +kernel)
  have t5 : a 25 ∈ [0,5,6,7,8,9,10,11] := remove (a 25) 4 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 5 t1 c54 (by decide +kernel)
  have t6 : a 25 ∈ [0,6,7,8,9,10,11] := remove (a 25) 5 [0,5,6,7,8,9,10,11] t5 b6
  have b7 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 6 t1 c54 (by decide +kernel)
  have t7 : a 25 ∈ [0,7,8,9,10,11] := remove (a 25) 6 [0,6,7,8,9,10,11] t6 b7
  have b8 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 7 t1 c54 (by decide +kernel)
  have t8 : a 25 ∈ [0,8,9,10,11] := remove (a 25) 7 [0,7,8,9,10,11] t7 b8
  have b9 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 9 t1 c54 (by decide +kernel)
  have t9 : a 25 ∈ [0,8,10,11] := remove (a 25) 9 [0,8,9,10,11] t8 b9
  have b10 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 10 t1 c54 (by decide +kernel)
  have t10 : a 25 ∈ [0,8,11] := remove (a 25) 10 [0,8,10,11] t9 b10
  have b11 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 11 t1 c54 (by decide +kernel)
  have t11 : a 25 ∈ [0,8] := remove (a 25) 11 [0,8,11] t10 b11
  have b12 : a 18 ≠ 1 := exclude [0,1,2,3,4,5,7,9,10,11] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t12 : a 18 ∈ [0,6,7,10,11,12,13] := remove (a 18) 1 [0,1,6,7,10,11,12,13] d18 b12
  have b13 : a 18 ≠ 7 := exclude [0,1,2,3,4,5,7,9,10,11] (edge r56) (a 18) (a 22) 7 d22 c56 (by decide +kernel)
  have t13 : a 18 ∈ [0,6,10,11,12,13] := remove (a 18) 7 [0,6,7,10,11,12,13] t12 b13
  have b14 : a 18 ≠ 11 := exclude [0,1,2,3,4,5,7,9,10,11] (edge r56) (a 18) (a 22) 11 d22 c56 (by decide +kernel)
  have t14 : a 18 ∈ [0,6,10,12,13] := remove (a 18) 11 [0,6,10,11,12,13] t13 b14
  have b15 : a 18 ≠ 13 := exclude [0,1,2,3,4,5,7,9,10,11] (edge r56) (a 18) (a 22) 13 d22 c56 (by decide +kernel)
  have t15 : a 18 ∈ [0,6,10,12] := remove (a 18) 13 [0,6,10,12,13] t14 b15
  exact And.intro t1 (And.intro t11 (t15))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_210
