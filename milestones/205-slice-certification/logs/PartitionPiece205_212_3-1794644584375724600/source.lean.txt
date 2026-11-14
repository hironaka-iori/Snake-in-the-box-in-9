import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,12,14,15,16,17,18,19,20,21,22,23])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,2,12,14])
    (d9 : a 9 ∈ [0,6])
    (d13 : a 13 ∈ [0,6])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,12] ∧ a 11 ∈ [0,12] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 24 ≠ 14 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,12,15,16,17,18,19,20,21,22,23] := remove (a 24) 14 [0,12,14,15,16,17,18,19,20,21,22,23] d24 b0
  have b1 : a 24 ≠ 15 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,12,16,17,18,19,20,21,22,23] := remove (a 24) 15 [0,12,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,12,17,18,19,20,21,22,23] := remove (a 24) 16 [0,12,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 24 ≠ 17 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,12,18,19,20,21,22,23] := remove (a 24) 17 [0,12,17,18,19,20,21,22,23] t2 b3
  have b4 : a 24 ≠ 18 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 18 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,12,19,20,21,22,23] := remove (a 24) 18 [0,12,18,19,20,21,22,23] t3 b4
  have b5 : a 24 ≠ 19 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 19 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,12,20,21,22,23] := remove (a 24) 19 [0,12,19,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 20 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 20 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,12,21,22,23] := remove (a 24) 20 [0,12,20,21,22,23] t5 b6
  have b7 : a 24 ≠ 21 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 21 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,12,22,23] := remove (a 24) 21 [0,12,21,22,23] t6 b7
  have b8 : a 24 ≠ 22 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 22 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,12,23] := remove (a 24) 22 [0,12,22,23] t7 b8
  have b9 : a 24 ≠ 23 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 23 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,12] := remove (a 24) 23 [0,12,23] t8 b9
  have b10 : a 11 ≠ 2 := exclude [0,6] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,12,14] := remove (a 11) 2 [0,2,12,14] d11 b10
  have b11 : a 11 ≠ 14 := exclude [0,6] (fun u v => edge r32 v u) (a 11) (a 9) 14 d9 c32 (by decide +kernel)
  have t11 : a 11 ∈ [0,12] := remove (a 11) 14 [0,12,14] t10 b11
  have b12 : a 13 ≠ 6 := exclude [0,6] (fun u v => edge r33 v u) (a 13) (a 9) 6 d9 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 6 [0,6] d13 b12
  have b13 : a 25 ≠ 6 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b13
  have b14 : a 25 ≠ 7 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 25 ≠ 8 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t9 (And.intro t11 (And.intro t12 (t15)))

theorem chunk13 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d9 : a 9 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,8,10,11])
    (d10 : a 10 ∈ [0,1,4,5])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 25 ∈ [0,1,2,3,4,5] ∧ a 14 ∈ [0,2,3,4,5,6,8,10,11] := by
  have b0 : a 25 ≠ 9 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b0
  have b1 : a 25 ≠ 10 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 25 ≠ 11 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 25 ≠ 12 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 25 ≠ 13 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 25 ≠ 14 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 25) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 25 ≠ 15 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 25) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 25 ≠ 16 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 25) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 25 ≠ 17 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 25) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t7 b8
  have b9 : a 25 ≠ 18 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 18 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 25) 18 [0,1,2,3,4,5,18,19,20,21,22,23] t8 b9
  have b10 : a 25 ≠ 19 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 19 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 25) 19 [0,1,2,3,4,5,19,20,21,22,23] t9 b10
  have b11 : a 25 ≠ 20 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 20 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 25) 20 [0,1,2,3,4,5,20,21,22,23] t10 b11
  have b12 : a 25 ≠ 21 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 21 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,2,3,4,5,22,23] := remove (a 25) 21 [0,1,2,3,4,5,21,22,23] t11 b12
  have b13 : a 25 ≠ 22 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 22 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,2,3,4,5,23] := remove (a 25) 22 [0,1,2,3,4,5,22,23] t12 b13
  have b14 : a 25 ≠ 23 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 23 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,4,5] := remove (a 25) 23 [0,1,2,3,4,5,23] t13 b14
  have b15 : a 14 ≠ 1 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,3,4,5,6,8,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,8,10,11] d14 b15
  exact And.intro t14 (t15)

theorem chunk14 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,3,4,5,6,8,10,11])
    (d10 : a 10 ∈ [0,1,4,5])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d11 : a 11 ∈ [0,12])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 14 ∈ [0,2] ∧ a 26 ∈ [0,2,3,5] ∧ a 15 ∈ [0,2,3,4,5,6,7,8] := by
  have b0 : a 14 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,4,5,6,8,10,11] := remove (a 14) 3 [0,2,3,4,5,6,8,10,11] d14 b0
  have b1 : a 14 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,5,6,8,10,11] := remove (a 14) 4 [0,2,4,5,6,8,10,11] t0 b1
  have b2 : a 14 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,6,8,10,11] := remove (a 14) 5 [0,2,5,6,8,10,11] t1 b2
  have b3 : a 14 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,8,10,11] := remove (a 14) 6 [0,2,6,8,10,11] t2 b3
  have b4 : a 14 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,10,11] := remove (a 14) 8 [0,2,8,10,11] t3 b4
  have b5 : a 14 ≠ 10 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,11] := remove (a 14) 10 [0,2,10,11] t4 b5
  have b6 : a 14 ≠ 11 := exclude [0,1,4,5] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,2] := remove (a 14) 11 [0,2,11] t5 b6
  have b7 : a 26 ≠ 1 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b7
  have b8 : a 26 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 26) 6 [0,2,3,5,6,7,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 7 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,2,3,5,8,9,10,11] := remove (a 26) 7 [0,2,3,5,7,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,3,5,9,10,11] := remove (a 26) 8 [0,2,3,5,8,9,10,11] t10 b11
  have b12 : a 26 ≠ 9 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,5,10,11] := remove (a 26) 9 [0,2,3,5,9,10,11] t11 b12
  have b13 : a 26 ≠ 10 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,5,11] := remove (a 26) 10 [0,2,3,5,10,11] t12 b13
  have b14 : a 26 ≠ 11 := exclude [0,1,4,5] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,2,3,5] := remove (a 26) 11 [0,2,3,5,11] t13 b14
  have b15 : a 15 ≠ 1 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,2,3,4,5,6,7,8] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8] d15 b15
  exact And.intro t6 (And.intro t14 (t15))

theorem chunk15 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2,3,4,5,6,7,8])
    (d11 : a 11 ∈ [0,12])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 15 ∈ [0,6] ∧ a 27 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 15 ≠ 2 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,3,4,5,6,7,8] := remove (a 15) 2 [0,2,3,4,5,6,7,8] d15 b0
  have b1 : a 15 ≠ 3 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,4,5,6,7,8] := remove (a 15) 3 [0,3,4,5,6,7,8] t0 b1
  have b2 : a 15 ≠ 4 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,5,6,7,8] := remove (a 15) 4 [0,4,5,6,7,8] t1 b2
  have b3 : a 15 ≠ 5 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,6,7,8] := remove (a 15) 5 [0,5,6,7,8] t2 b3
  have b4 : a 15 ≠ 7 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,6,8] := remove (a 15) 7 [0,6,7,8] t3 b4
  have b5 : a 15 ≠ 8 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 8 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,6] := remove (a 15) 8 [0,6,8] t4 b5
  have b6 : a 27 ≠ 2 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d27 b6
  have b7 : a 27 ≠ 3 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 27 ≠ 4 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 27 ≠ 5 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 27 ≠ 6 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 27 ≠ 7 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 27 ≠ 8 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 27 ≠ 9 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 27 ≠ 10 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 27 ≠ 11 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t5 (t15)

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_212
