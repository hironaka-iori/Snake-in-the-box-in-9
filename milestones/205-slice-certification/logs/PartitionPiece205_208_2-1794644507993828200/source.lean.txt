import PartitionData205_208
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,8,9,10,11])
    (d11 : a 11 ∈ [0,8])
    (d13 : a 13 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 26 ∈ [0,9] ∧ a 15 ∈ [0,8] ∧ a 13 ∈ [0,1] ∧ a 28 ∈ [0,1,5,6,7,8,9,10,11] := by
  have b0 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,6,7,8,9,10,11] := remove (a 26) 5 [0,5,6,7,8,9,10,11] d26 b0
  have b1 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,7,8,9,10,11] := remove (a 26) 6 [0,6,7,8,9,10,11] t0 b1
  have b2 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,8,9,10,11] := remove (a 26) 7 [0,7,8,9,10,11] t1 b2
  have b3 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,9,10,11] := remove (a 26) 8 [0,8,9,10,11] t2 b3
  have b4 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,9,11] := remove (a 26) 10 [0,9,10,11] t3 b4
  have b5 : a 26 ≠ 11 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,9] := remove (a 26) 11 [0,9,11] t4 b5
  have b6 : a 15 ≠ 1 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,3,8,9,10,11] := remove (a 15) 1 [0,1,2,3,8,9,10,11] d15 b6
  have b7 : a 15 ≠ 2 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,3,8,9,10,11] := remove (a 15) 2 [0,2,3,8,9,10,11] t6 b7
  have b8 : a 15 ≠ 3 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,8,9,10,11] := remove (a 15) 3 [0,3,8,9,10,11] t7 b8
  have b9 : a 15 ≠ 9 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 9 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,8,10,11] := remove (a 15) 9 [0,8,9,10,11] t8 b9
  have b10 : a 15 ≠ 10 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 10 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,8,11] := remove (a 15) 10 [0,8,10,11] t9 b10
  have b11 : a 15 ≠ 11 := exclude [0,8] (fun u v => edge r38 v u) (a 15) (a 11) 11 d11 c38 (by decide +kernel)
  have t11 : a 15 ∈ [0,8] := remove (a 15) 11 [0,8,11] t10 b11
  have b12 : a 13 ≠ 2 := exclude [0,6] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0,1] := remove (a 13) 2 [0,1,2] d13 b12
  have b13 : a 28 ≠ 2 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 28) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b13
  have b14 : a 28 ≠ 3 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,1,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 28 ≠ 4 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 28) 4 [0,1,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t5 (And.intro t11 (And.intro t12 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,6])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d13 : a 13 ∈ [0,1])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,1,6] ∧ a 29 ∈ [0,4,12,13,14,15,16,17,18,19] := by
  have b0 : a 28 ≠ 5 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,6,7,8,9,10,11] := remove (a 28) 5 [0,1,5,6,7,8,9,10,11] d28 b0
  have b1 : a 28 ≠ 7 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,1,6,8,9,10,11] := remove (a 28) 7 [0,1,6,7,8,9,10,11] t0 b1
  have b2 : a 28 ≠ 8 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,1,6,9,10,11] := remove (a 28) 8 [0,1,6,8,9,10,11] t1 b2
  have b3 : a 28 ≠ 9 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,6,10,11] := remove (a 28) 9 [0,1,6,9,10,11] t2 b3
  have b4 : a 28 ≠ 10 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,6,11] := remove (a 28) 10 [0,1,6,10,11] t3 b4
  have b5 : a 28 ≠ 11 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,6] := remove (a 28) 11 [0,1,6,11] t4 b5
  have b6 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d29 b6
  have b7 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 29 ≠ 8 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 8 [0,4,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,4,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 9 [0,4,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,4,11,12,13,14,15,16,17,18,19] := remove (a 29) 10 [0,4,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,4,12,13,14,15,16,17,18,19] := remove (a 29) 11 [0,4,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t5 (t15)

theorem chunk10 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,4,12,13,14,15,16,17,18,19])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,4,12,16] ∧ a 30 ∈ [0,1] := by
  have b0 : a 29 ≠ 13 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,4,12,14,15,16,17,18,19] := remove (a 29) 13 [0,4,12,13,14,15,16,17,18,19] d29 b0
  have b1 : a 29 ≠ 14 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,4,12,15,16,17,18,19] := remove (a 29) 14 [0,4,12,14,15,16,17,18,19] t0 b1
  have b2 : a 29 ≠ 15 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,4,12,16,17,18,19] := remove (a 29) 15 [0,4,12,15,16,17,18,19] t1 b2
  have b3 : a 29 ≠ 17 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,4,12,16,18,19] := remove (a 29) 17 [0,4,12,16,17,18,19] t2 b3
  have b4 : a 29 ≠ 18 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,4,12,16,19] := remove (a 29) 18 [0,4,12,16,18,19] t3 b4
  have b5 : a 29 ≠ 19 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,4,12,16] := remove (a 29) 19 [0,4,12,16,19] t4 b5
  have b6 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b6
  have b7 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,6,7,8,9,10,11] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11] t8 b9
  have b10 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,7,8,9,10,11] := remove (a 30) 6 [0,1,6,7,8,9,10,11] t9 b10
  have b11 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,8,9,10,11] := remove (a 30) 7 [0,1,7,8,9,10,11] t10 b11
  have b12 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,9,10,11] := remove (a 30) 8 [0,1,8,9,10,11] t11 b12
  have b13 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,10,11] := remove (a 30) 9 [0,1,9,10,11] t12 b13
  have b14 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,11] := remove (a 30) 10 [0,1,10,11] t13 b14
  have b15 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1] := remove (a 30) 11 [0,1,11] t14 b15
  exact And.intro t5 (t15)

theorem chunk11 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0,8])
    (d17 : a 17 ∈ [0,2,3,5])
    (d16 : a 16 ∈ [0,3])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 31 ∈ [0,6] ∧ a 17 ∈ [0,3] ∧ a 20 ∈ [0,1,6,7,10,11] := by
  have b0 : a 31 ≠ 1 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9] d31 b0
  have b1 : a 31 ≠ 2 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,3,4,5,6,7,8,9] := remove (a 31) 2 [0,2,3,4,5,6,7,8,9] t0 b1
  have b2 : a 31 ≠ 3 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,4,5,6,7,8,9] := remove (a 31) 3 [0,3,4,5,6,7,8,9] t1 b2
  have b3 : a 31 ≠ 4 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,5,6,7,8,9] := remove (a 31) 4 [0,4,5,6,7,8,9] t2 b3
  have b4 : a 31 ≠ 5 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,6,7,8,9] := remove (a 31) 5 [0,5,6,7,8,9] t3 b4
  have b5 : a 31 ≠ 7 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,6,8,9] := remove (a 31) 7 [0,6,7,8,9] t4 b5
  have b6 : a 31 ≠ 8 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,6,9] := remove (a 31) 8 [0,6,8,9] t5 b6
  have b7 : a 31 ≠ 9 := exclude [0,8] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,6] := remove (a 31) 9 [0,6,9] t6 b7
  have b8 : a 17 ≠ 2 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t8 : a 17 ∈ [0,3,5] := remove (a 17) 2 [0,2,3,5] d17 b8
  have b9 : a 17 ≠ 5 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,3] := remove (a 17) 5 [0,3,5] t8 b9
  have b10 : a 20 ≠ 2 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b10
  have b11 : a 20 ≠ 3 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 20 ≠ 4 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 4 d16 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 20 ≠ 5 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 5 d16 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,6,7,8,9,10,11] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11] t12 b13
  have b14 : a 20 ≠ 8 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 8 d16 c50 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,6,7,9,10,11] := remove (a 20) 8 [0,1,6,7,8,9,10,11] t13 b14
  have b15 : a 20 ≠ 9 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 9 d16 c50 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,6,7,10,11] := remove (a 20) 9 [0,1,6,7,9,10,11] t14 b15
  exact And.intro t7 (And.intro t9 (t15))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_208
