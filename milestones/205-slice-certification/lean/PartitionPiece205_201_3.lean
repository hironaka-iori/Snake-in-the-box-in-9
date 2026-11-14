import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,3,4,7,8])
    (d9 : a 9 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,1,16,17])
    (d14 : a 14 ∈ [0,1,2,12,13,16])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 25 ∈ [0,1,3,4] ∧ a 10 ∈ [0,1] ∧ a 11 ∈ [0,16] ∧ a 14 ∈ [0,1,12,13] ∧ a 26 ∈ [0,4,6,7,8,10,12,13,14,16,18,19,20,21,22,23] := by
  have b0 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,3,4,8] := remove (a 25) 7 [0,1,3,4,7,8] d25 b0
  have b1 : a 25 ≠ 8 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,3,4] := remove (a 25) 8 [0,1,3,4,8] t0 b1
  have b2 : a 10 ≠ 4 := exclude [0,1,16,17] (edge r35) (a 10) (a 11) 4 d11 c35 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,5] := remove (a 10) 4 [0,1,4,5] d10 b2
  have b3 : a 10 ≠ 5 := exclude [0,1,16,17] (edge r35) (a 10) (a 11) 5 d11 c35 (by decide +kernel)
  have t3 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 1 t3 c35 (by decide +kernel)
  have t4 : a 11 ∈ [0,16,17] := remove (a 11) 1 [0,1,16,17] d11 b4
  have b5 : a 11 ≠ 17 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 17 t3 c35 (by decide +kernel)
  have t5 : a 11 ∈ [0,16] := remove (a 11) 17 [0,16,17] t4 b5
  have b6 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 2 t3 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,12,13,16] := remove (a 14) 2 [0,1,2,12,13,16] d14 b6
  have b7 : a 14 ≠ 16 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 16 t3 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,12,13] := remove (a 14) 16 [0,1,12,13,16] t6 b7
  have b8 : a 26 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 1 t3 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b8
  have b9 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 2 t3 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 3 t3 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 5 t3 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 9 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 9 t3 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 11 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 11 t3 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,6,7,8,10,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 15 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 15 t3 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,4,6,7,8,10,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 17 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 17 t3 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,18,19,20,21,22,23] := remove (a 26) 17 [0,4,6,7,8,10,12,13,14,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (t15))))

theorem chunk13 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,6,7,8])
    (d11 : a 11 ∈ [0,16])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20] ∧ a 15 ∈ [0,8] ∧ a 27 ∈ [0,1,9,11] := by
  have b0 : a 26 ≠ 18 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 18 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20,21,22,23] := remove (a 26) 18 [0,4,6,7,8,10,12,13,14,16,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 21 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 21 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20,22,23] := remove (a 26) 21 [0,4,6,7,8,10,12,13,14,16,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 22 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 22 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20,23] := remove (a 26) 22 [0,4,6,7,8,10,12,13,14,16,19,20,22,23] t1 b2
  have b3 : a 26 ≠ 23 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 23 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,4,6,7,8,10,12,13,14,16,19,20] := remove (a 26) 23 [0,4,6,7,8,10,12,13,14,16,19,20,23] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0,16] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,6,7,8] := remove (a 15) 1 [0,1,2,6,7,8] d15 b4
  have b5 : a 15 ≠ 2 := exclude [0,16] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,6,7,8] := remove (a 15) 2 [0,2,6,7,8] t4 b5
  have b6 : a 15 ≠ 6 := exclude [0,16] (fun u v => edge r38 v u) (a 15) (a 11) 6 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,7,8] := remove (a 15) 6 [0,6,7,8] t5 b6
  have b7 : a 15 ≠ 7 := exclude [0,16] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,8] := remove (a 15) 7 [0,7,8] t6 b7
  have b8 : a 27 ≠ 2 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b8
  have b9 : a 27 ≠ 3 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 5 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 6 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 7 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 10 := exclude [0,16] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,9,11] := remove (a 27) 10 [0,1,9,10,11] t14 b15
  exact And.intro t3 (And.intro t7 (t15))

theorem chunk14 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,8,15,17])
    (d13 : a 13 ∈ [0,4])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 12 ∈ [0,8] ∧ a 28 ∈ [0,4,10,11] ∧ a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 12 ≠ 15 := exclude [0,4] (edge r40) (a 12) (a 13) 15 d13 c40 (by decide +kernel)
  have t0 : a 12 ∈ [0,8,17] := remove (a 12) 15 [0,8,15,17] d12 b0
  have b1 : a 12 ≠ 17 := exclude [0,4] (edge r40) (a 12) (a 13) 17 d13 c40 (by decide +kernel)
  have t1 : a 12 ∈ [0,8] := remove (a 12) 17 [0,8,17] t0 b1
  have b2 : a 28 ≠ 1 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 1 t1 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b2
  have b3 : a 28 ≠ 2 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 2 t1 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 28 ≠ 3 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 3 t1 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 28 ≠ 5 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 5 t1 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,4,6,7,8,9,10,11] := remove (a 28) 5 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 28 ≠ 6 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 6 t1 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,4,7,8,9,10,11] := remove (a 28) 6 [0,4,6,7,8,9,10,11] t5 b6
  have b7 : a 28 ≠ 7 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 7 t1 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,4,8,9,10,11] := remove (a 28) 7 [0,4,7,8,9,10,11] t6 b7
  have b8 : a 28 ≠ 8 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 8 t1 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,4,9,10,11] := remove (a 28) 8 [0,4,8,9,10,11] t7 b8
  have b9 : a 28 ≠ 9 := exclude [0,8] (fun u v => edge r42 v u) (a 28) (a 12) 9 t1 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,4,10,11] := remove (a 28) 9 [0,4,9,10,11] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d29 b10
  have b11 : a 29 ≠ 3 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 29 ≠ 4 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 29 ≠ 6 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 29 ≠ 7 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t9 (t15))

theorem chunk15 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17])
    (d13 : a 13 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,1,12,13])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,1,8,9] ∧ a 30 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 10 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,8,9,11,12,13,14,15,16,17] := remove (a 29) 10 [0,1,8,9,10,11,12,13,14,15,16,17] d29 b0
  have b1 : a 29 ≠ 11 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,8,9,12,13,14,15,16,17] := remove (a 29) 11 [0,1,8,9,11,12,13,14,15,16,17] t0 b1
  have b2 : a 29 ≠ 12 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,8,9,13,14,15,16,17] := remove (a 29) 12 [0,1,8,9,12,13,14,15,16,17] t1 b2
  have b3 : a 29 ≠ 13 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,8,9,14,15,16,17] := remove (a 29) 13 [0,1,8,9,13,14,15,16,17] t2 b3
  have b4 : a 29 ≠ 14 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,8,9,15,16,17] := remove (a 29) 14 [0,1,8,9,14,15,16,17] t3 b4
  have b5 : a 29 ≠ 15 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,8,9,16,17] := remove (a 29) 15 [0,1,8,9,15,16,17] t4 b5
  have b6 : a 29 ≠ 16 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,8,9,17] := remove (a 29) 16 [0,1,8,9,16,17] t5 b6
  have b7 : a 29 ≠ 17 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,8,9] := remove (a 29) 17 [0,1,8,9,17] t6 b7
  have b8 : a 30 ≠ 1 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b8
  have b9 : a 30 ≠ 3 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 4 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 5 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 30 ≠ 6 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 30 ≠ 7 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 30 ≠ 8 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 9 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (t15)

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_201
