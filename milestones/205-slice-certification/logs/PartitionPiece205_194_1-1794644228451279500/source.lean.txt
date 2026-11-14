import PartitionData205_194
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1])
    (d13 : a 13 ∈ [0,2,4,6])
    (d9 : a 9 ∈ [0,4])
    (d14 : a 14 ∈ [0,1,3,5])
    (d10 : a 10 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 24 ∈ [0,2] ∧ a 13 ∈ [0,4] ∧ a 14 ∈ [0,1] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,3,7,8] := by
  have b0 : a 24 ≠ 6 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,7,8,9,10,11] := remove (a 24) 6 [0,2,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,8,9,10,11] := remove (a 24) 7 [0,2,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 8 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,9,10,11] := remove (a 24) 8 [0,2,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 9 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,2,10,11] := remove (a 24) 9 [0,2,9,10,11] t2 b3
  have b4 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,11] := remove (a 24) 10 [0,2,10,11] t3 b4
  have b5 : a 24 ≠ 11 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2] := remove (a 24) 11 [0,2,11] t4 b5
  have b6 : a 13 ≠ 2 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,4,6] := remove (a 13) 2 [0,2,4,6] d13 b6
  have b7 : a 13 ≠ 6 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 6 d9 c33 (by decide +kernel)
  have t7 : a 13 ∈ [0,4] := remove (a 13) 6 [0,4,6] t6 b7
  have b8 : a 14 ≠ 3 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,5] := remove (a 14) 3 [0,1,3,5] d14 b8
  have b9 : a 14 ≠ 5 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,1] := remove (a 14) 5 [0,1,5] t8 b9
  have b10 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,1] := remove (a 15) 2 [0,1,2] d15 b10
  have b11 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,2,3,4,5,6,7,8] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8] d27 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,3,4,5,6,7,8] := remove (a 27) 2 [0,2,3,4,5,6,7,8] t11 b12
  have b13 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,3,5,6,7,8] := remove (a 27) 4 [0,3,4,5,6,7,8] t12 b13
  have b14 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,3,6,7,8] := remove (a 27) 5 [0,3,5,6,7,8] t13 b14
  have b15 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,3,7,8] := remove (a 27) 6 [0,3,6,7,8] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,3,7,8])
    (d11 : a 11 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d13 : a 13 ∈ [0,4])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,3] ∧ a 28 ∈ [0,2,6,8] ∧ a 29 ∈ [0,1,6,7,12,13,15,16,17] := by
  have b0 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,3,8] := remove (a 27) 7 [0,3,7,8] d27 b0
  have b1 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,3] := remove (a 27) 8 [0,3,8] t0 b1
  have b2 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,3,4,5,6,7,8] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8] d28 b2
  have b3 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,4,5,6,7,8] := remove (a 28) 3 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,5,6,7,8] := remove (a 28) 4 [0,2,4,5,6,7,8] t3 b4
  have b5 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,6,7,8] := remove (a 28) 5 [0,2,5,6,7,8] t4 b5
  have b6 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,6,8] := remove (a 28) 7 [0,2,6,7,8] t5 b6
  have b7 : a 29 ≠ 2 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d29 b7
  have b8 : a 29 ≠ 3 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 29 ≠ 4 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 29 ≠ 8 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 29) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 29 ≠ 9 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 29) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 29 ≠ 10 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 29) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 29 ≠ 11 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 29) 11 [0,1,6,7,11,12,13,14,15,16,17] t13 b14
  have b15 : a 29 ≠ 14 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,6,7,12,13,15,16,17] := remove (a 29) 14 [0,1,6,7,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t6 (t15))

theorem chunk6 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,6,7,12,13,15,16,17])
    (d13 : a 13 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0,2,3,4,6,7])
    (d16 : a 16 ∈ [0,2])
    (d18 : a 18 ∈ [0,1,2,4,5,6,7,9,10])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 29 ∈ [0,1,6,7,12,13] ∧ a 30 ∈ [0,1,2,3,4,5] ∧ a 31 ∈ [0,1,2,3,4,5] ∧ a 17 ∈ [0,4] ∧ a 18 ∈ [0,5,6,7,9,10] := by
  have b0 : a 29 ≠ 15 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,6,7,12,13,16,17] := remove (a 29) 15 [0,1,6,7,12,13,15,16,17] d29 b0
  have b1 : a 29 ≠ 16 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,6,7,12,13,17] := remove (a 29) 16 [0,1,6,7,12,13,16,17] t0 b1
  have b2 : a 29 ≠ 17 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,6,7,12,13] := remove (a 29) 17 [0,1,6,7,12,13,17] t1 b2
  have b3 : a 30 ≠ 6 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,2,3,4,5,7,8] := remove (a 30) 6 [0,1,2,3,4,5,6,7,8] d30 b3
  have b4 : a 30 ≠ 7 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,2,3,4,5,8] := remove (a 30) 7 [0,1,2,3,4,5,7,8] t3 b4
  have b5 : a 30 ≠ 8 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,2,3,4,5] := remove (a 30) 8 [0,1,2,3,4,5,8] t4 b5
  have b6 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,2,3,4,5,7,8] := remove (a 31) 6 [0,1,2,3,4,5,6,7,8] d31 b6
  have b7 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,3,4,5,8] := remove (a 31) 7 [0,1,2,3,4,5,7,8] t6 b7
  have b8 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,3,4,5] := remove (a 31) 8 [0,1,2,3,4,5,8] t7 b8
  have b9 : a 17 ≠ 2 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,4,6,7] := remove (a 17) 2 [0,2,3,4,6,7] d17 b9
  have b10 : a 17 ≠ 3 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,4,6,7] := remove (a 17) 3 [0,3,4,6,7] t9 b10
  have b11 : a 17 ≠ 6 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 6 d16 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,4,7] := remove (a 17) 6 [0,4,6,7] t10 b11
  have b12 : a 17 ≠ 7 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 7 d16 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,4] := remove (a 17) 7 [0,4,7] t11 b12
  have b13 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,4,5,6,7,9,10] := remove (a 18) 1 [0,1,2,4,5,6,7,9,10] d18 b13
  have b14 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 2 d16 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0,4,5,6,7,9,10] := remove (a 18) 2 [0,2,4,5,6,7,9,10] t13 b14
  have b15 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 4 d16 c49 (by decide +kernel)
  have t15 : a 18 ∈ [0,5,6,7,9,10] := remove (a 18) 4 [0,4,5,6,7,9,10] t14 b15
  exact And.intro t2 (And.intro t5 (And.intro t8 (And.intro t12 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,5,6,7,9,10])
    (d16 : a 16 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,3])
    (d17 : a 17 ∈ [0,4])
    (d21 : a 21 ∈ [0,2,4,6])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 18 ∈ [0] ∧ a 20 ∈ [0,2] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0,4] ∧ a 22 ∈ [0,3] ∧ a 26 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 5 d16 c49 (by decide +kernel)
  have t0 : a 18 ∈ [0,6,7,9,10] := remove (a 18) 5 [0,5,6,7,9,10] d18 b0
  have b1 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 6 d16 c49 (by decide +kernel)
  have t1 : a 18 ∈ [0,7,9,10] := remove (a 18) 6 [0,6,7,9,10] t0 b1
  have b2 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 7 d16 c49 (by decide +kernel)
  have t2 : a 18 ∈ [0,9,10] := remove (a 18) 7 [0,7,9,10] t1 b2
  have b3 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 9 d16 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0,10] := remove (a 18) 9 [0,9,10] t2 b3
  have b4 : a 18 ≠ 10 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 10 d16 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 10 [0,10] t3 b4
  have b5 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 1 d16 c50 (by decide +kernel)
  have t5 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b5
  have b6 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t5 b6
  have b7 : a 19 ≠ 3 := exclude [0,4] (fun u v => edge r52 v u) (a 19) (a 17) 3 d17 c52 (by decide +kernel)
  have t7 : a 19 ∈ [0] := remove (a 19) 3 [0,3] d19 b7
  have b8 : a 21 ≠ 2 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,4,6] := remove (a 21) 2 [0,2,4,6] d21 b8
  have b9 : a 21 ≠ 6 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 6 d17 c53 (by decide +kernel)
  have t9 : a 21 ∈ [0,4] := remove (a 21) 6 [0,4,6] t8 b9
  have b10 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 t4 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b10
  have b11 : a 22 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 2 t4 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] t10 b11
  have b12 : a 22 ≠ 4 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 4 t4 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,3,5] := remove (a 22) 4 [0,3,4,5] t11 b12
  have b13 : a 22 ≠ 5 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 5 t4 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,3] := remove (a 22) 5 [0,3,5] t12 b13
  have b14 : a 26 ≠ 4 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 4 t4 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b14
  have b15 : a 26 ≠ 5 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 5 t4 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_194
