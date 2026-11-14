import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d8 : a 8 ∈ [0,4,6,10])
    (d11 : a 11 ∈ [0,3,4,6,7,8])
    (d9 : a 9 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0,4])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    : a 24 ∈ [0,12,16,18] ∧ a 11 ∈ [0,4] ∧ a 25 ∈ [0,1,3,4,5,6,7,8,9,10] := by
  have b0 : a 24 ≠ 11 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b0
  have b1 : a 24 ≠ 13 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,12,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 13 [0,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 24 ≠ 14 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,12,15,16,17,18,19,20,21,22,23] := remove (a 24) 14 [0,12,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 24 ≠ 15 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,12,16,17,18,19,20,21,22,23] := remove (a 24) 15 [0,12,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 24 ≠ 17 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,12,16,18,19,20,21,22,23] := remove (a 24) 17 [0,12,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 24 ≠ 19 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 19 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,12,16,18,20,21,22,23] := remove (a 24) 19 [0,12,16,18,19,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 20 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 20 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,12,16,18,21,22,23] := remove (a 24) 20 [0,12,16,18,20,21,22,23] t5 b6
  have b7 : a 24 ≠ 21 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 21 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,12,16,18,22,23] := remove (a 24) 21 [0,12,16,18,21,22,23] t6 b7
  have b8 : a 24 ≠ 22 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 22 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,12,16,18,23] := remove (a 24) 22 [0,12,16,18,22,23] t7 b8
  have b9 : a 24 ≠ 23 := exclude [0,4,6,10] (fun u v => edge r31 v u) (a 24) (a 8) 23 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,12,16,18] := remove (a 24) 23 [0,12,16,18,23] t8 b9
  have b10 : a 11 ≠ 7 := exclude [0,1,2,3] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,3,4,6,8] := remove (a 11) 7 [0,3,4,6,7,8] d11 b10
  have b11 : a 11 ≠ 8 := exclude [0,1,2,3] (fun u v => edge r32 v u) (a 11) (a 9) 8 d9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,3,4,6] := remove (a 11) 8 [0,3,4,6,8] t10 b11
  have b12 : a 25 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b12
  have b13 : a 25 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10] := remove (a 25) 11 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 11 ≠ 3 := exclude [0,4] (fun u v => edge r35 v u) (a 11) (a 10) 3 d10 c35 (by decide +kernel)
  have t14 : a 11 ∈ [0,4,6] := remove (a 11) 3 [0,3,4,6] t11 b14
  have b15 : a 11 ≠ 6 := exclude [0,4] (fun u v => edge r35 v u) (a 11) (a 10) 6 d10 c35 (by decide +kernel)
  have t15 : a 11 ∈ [0,4] := remove (a 11) 6 [0,4,6] t14 b15
  exact And.intro t9 (And.intro t15 (t13))

theorem chunk13 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,12,13,14,15])
    (d10 : a 10 ∈ [0,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 14 ∈ [0,3,12,15] ∧ a 26 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 1 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,3,4,5,6,7,12,13,14,15] := remove (a 14) 1 [0,1,2,3,4,5,6,7,12,13,14,15] d14 b0
  have b1 : a 14 ≠ 2 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 2 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,3,4,5,6,7,12,13,14,15] := remove (a 14) 2 [0,2,3,4,5,6,7,12,13,14,15] t0 b1
  have b2 : a 14 ≠ 4 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,5,6,7,12,13,14,15] := remove (a 14) 4 [0,3,4,5,6,7,12,13,14,15] t1 b2
  have b3 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,3,6,7,12,13,14,15] := remove (a 14) 5 [0,3,5,6,7,12,13,14,15] t2 b3
  have b4 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,3,7,12,13,14,15] := remove (a 14) 6 [0,3,6,7,12,13,14,15] t3 b4
  have b5 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,3,12,13,14,15] := remove (a 14) 7 [0,3,7,12,13,14,15] t4 b5
  have b6 : a 14 ≠ 13 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 13 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,3,12,14,15] := remove (a 14) 13 [0,3,12,13,14,15] t5 b6
  have b7 : a 14 ≠ 14 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 14 d10 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,3,12,15] := remove (a 14) 14 [0,3,12,14,15] t6 b7
  have b8 : a 26 ≠ 1 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b8
  have b9 : a 26 ≠ 2 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 3 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 4 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 5 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 6 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 7 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 9 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (t15)

theorem chunk14 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,4])
    (d15 : a 15 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,4])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,8,12,20] ∧ a 15 ∈ [0,4] ∧ a 27 ∈ [0,1,2,5,6,7,8] := by
  have b0 : a 26 ≠ 10 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 11 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 13 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 13 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,8,12,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 13 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 14 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 14 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,8,12,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,8,12,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 15 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 15 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,8,12,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,8,12,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 26 ≠ 16 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 16 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,8,12,17,18,19,20,21,22,23] := remove (a 26) 16 [0,8,12,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 26 ≠ 17 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 17 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,8,12,18,19,20,21,22,23] := remove (a 26) 17 [0,8,12,17,18,19,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 18 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 18 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,8,12,19,20,21,22,23] := remove (a 26) 18 [0,8,12,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 19 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 19 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,8,12,20,21,22,23] := remove (a 26) 19 [0,8,12,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 21 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 21 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,8,12,20,22,23] := remove (a 26) 21 [0,8,12,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 22 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 22 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,8,12,20,23] := remove (a 26) 22 [0,8,12,20,22,23] t9 b10
  have b11 : a 26 ≠ 23 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 23 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,8,12,20] := remove (a 26) 23 [0,8,12,20,23] t10 b11
  have b12 : a 15 ≠ 1 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t12 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b12
  have b13 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t13 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] t12 b13
  have b14 : a 27 ≠ 3 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,2,4,5,6,7,8] := remove (a 27) 3 [0,1,2,3,4,5,6,7,8] d27 b14
  have b15 : a 27 ≠ 4 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,2,5,6,7,8] := remove (a 27) 4 [0,1,2,4,5,6,7,8] t14 b15
  exact And.intro t11 (And.intro t13 (t15))

theorem chunk15 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,5,6,7,8])
    (d11 : a 11 ∈ [0,4])
    (d13 : a 13 ∈ [0,1,3,4,5,11,12,14])
    (d12 : a 12 ∈ [0,12])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,1,2] ∧ a 13 ∈ [0,1] ∧ a 28 ∈ [0,1,2,3,8,9,11] ∧ a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 5 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,2,6,7,8] := remove (a 27) 5 [0,1,2,5,6,7,8] d27 b0
  have b1 : a 27 ≠ 6 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,2,7,8] := remove (a 27) 6 [0,1,2,6,7,8] t0 b1
  have b2 : a 27 ≠ 7 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,2,8] := remove (a 27) 7 [0,1,2,7,8] t1 b2
  have b3 : a 27 ≠ 8 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,2] := remove (a 27) 8 [0,1,2,8] t2 b3
  have b4 : a 13 ≠ 3 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 3 d12 c40 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,4,5,11,12,14] := remove (a 13) 3 [0,1,3,4,5,11,12,14] d13 b4
  have b5 : a 13 ≠ 4 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 4 d12 c40 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,5,11,12,14] := remove (a 13) 4 [0,1,4,5,11,12,14] t4 b5
  have b6 : a 13 ≠ 5 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 5 d12 c40 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,11,12,14] := remove (a 13) 5 [0,1,5,11,12,14] t5 b6
  have b7 : a 13 ≠ 11 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 11 d12 c40 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,12,14] := remove (a 13) 11 [0,1,11,12,14] t6 b7
  have b8 : a 13 ≠ 12 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 12 d12 c40 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,14] := remove (a 13) 12 [0,1,12,14] t7 b8
  have b9 : a 13 ≠ 14 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 14 d12 c40 (by decide +kernel)
  have t9 : a 13 ∈ [0,1] := remove (a 13) 14 [0,1,14] t8 b9
  have b10 : a 28 ≠ 4 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 28) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b10
  have b11 : a 28 ≠ 5 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 28) 5 [0,1,2,3,5,6,7,8,9,10,11] t10 b11
  have b12 : a 28 ≠ 6 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 28) 6 [0,1,2,3,6,7,8,9,10,11] t11 b12
  have b13 : a 28 ≠ 7 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,2,3,8,9,10,11] := remove (a 28) 7 [0,1,2,3,7,8,9,10,11] t12 b13
  have b14 : a 28 ≠ 10 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,2,3,8,9,11] := remove (a 28) 10 [0,1,2,3,8,9,10,11] t13 b14
  have b15 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 1 t9 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b15
  exact And.intro t3 (And.intro t9 (And.intro t14 (t15)))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_206
