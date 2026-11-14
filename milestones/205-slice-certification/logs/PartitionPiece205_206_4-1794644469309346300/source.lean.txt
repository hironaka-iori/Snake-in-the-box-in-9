import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,1])
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 29 ∈ [0,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 8 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 12 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 13 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 14 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 15 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 16 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,17,18,19,20,21,22,23] := remove (a 29) 16 [0,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 17 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,18,19,20,21,22,23] := remove (a 29) 17 [0,17,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk17 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,3,12,15])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,18] ∧ a 30 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 19 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,18,20,21,22,23] := remove (a 29) 19 [0,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 20 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,18,21,22,23] := remove (a 29) 20 [0,18,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 21 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,18,22,23] := remove (a 29) 21 [0,18,21,22,23] t1 b2
  have b3 : a 29 ≠ 22 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,18,23] := remove (a 29) 22 [0,18,22,23] t2 b3
  have b4 : a 29 ≠ 23 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,18] := remove (a 29) 23 [0,18,23] t3 b4
  have b5 : a 30 ≠ 2 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b5
  have b6 : a 30 ≠ 3 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 4 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 30 ≠ 5 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 30 ≠ 6 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 7 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 8 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 30 ≠ 9 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 30 ≠ 10 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 30 ≠ 11 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 12 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t4 (t15)

theorem chunk18 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,3,12,15])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,4])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,1,13,23] ∧ a 31 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 30 ≠ 14 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,13,15,16,17,18,19,20,21,22,23] := remove (a 30) 14 [0,1,13,14,15,16,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 15 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,13,16,17,18,19,20,21,22,23] := remove (a 30) 15 [0,1,13,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 16 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,13,17,18,19,20,21,22,23] := remove (a 30) 16 [0,1,13,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 17 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,13,18,19,20,21,22,23] := remove (a 30) 17 [0,1,13,17,18,19,20,21,22,23] t2 b3
  have b4 : a 30 ≠ 18 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,13,19,20,21,22,23] := remove (a 30) 18 [0,1,13,18,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 19 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,13,20,21,22,23] := remove (a 30) 19 [0,1,13,19,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 20 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 20 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,13,21,22,23] := remove (a 30) 20 [0,1,13,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 21 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,13,22,23] := remove (a 30) 21 [0,1,13,21,22,23] t6 b7
  have b8 : a 30 ≠ 22 := exclude [0,3,12,15] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,13,23] := remove (a 30) 22 [0,1,13,22,23] t7 b8
  have b9 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b9
  have b10 : a 31 ≠ 3 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 6 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 31 ≠ 7 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 31 ≠ 8 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 9 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 31 ≠ 10 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (t15)

theorem chunk19 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,4])
    (d16 : a 16 ∈ [0,1,6,7,8,9,12,13,15,17])
    (d20 : a 20 ∈ [0,6])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 31 ∈ [0,1,4,5] ∧ a 16 ∈ [0,6,8,12,13,15,17] := by
  have b0 : a 31 ≠ 11 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 12 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 12 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 13 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 14 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 31) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 15 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 31) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 16 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 31) 16 [0,1,4,5,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 17 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 31) 17 [0,1,4,5,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 18 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 18 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 31) 18 [0,1,4,5,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 19 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 19 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,4,5,20,21,22,23] := remove (a 31) 19 [0,1,4,5,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 20 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,4,5,21,22,23] := remove (a 31) 20 [0,1,4,5,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 21 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,4,5,22,23] := remove (a 31) 21 [0,1,4,5,21,22,23] t9 b10
  have b11 : a 31 ≠ 22 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 22 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,4,5,23] := remove (a 31) 22 [0,1,4,5,22,23] t10 b11
  have b12 : a 31 ≠ 23 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,4,5] := remove (a 31) 23 [0,1,4,5,23] t11 b12
  have b13 : a 16 ≠ 1 := exclude [0,6] (edge r50) (a 16) (a 20) 1 d20 c50 (by decide +kernel)
  have t13 : a 16 ∈ [0,6,7,8,9,12,13,15,17] := remove (a 16) 1 [0,1,6,7,8,9,12,13,15,17] d16 b13
  have b14 : a 16 ≠ 7 := exclude [0,6] (edge r50) (a 16) (a 20) 7 d20 c50 (by decide +kernel)
  have t14 : a 16 ∈ [0,6,8,9,12,13,15,17] := remove (a 16) 7 [0,6,7,8,9,12,13,15,17] t13 b14
  have b15 : a 16 ≠ 9 := exclude [0,6] (edge r50) (a 16) (a 20) 9 d20 c50 (by decide +kernel)
  have t15 : a 16 ∈ [0,6,8,12,13,15,17] := remove (a 16) 9 [0,6,8,9,12,13,15,17] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_206
