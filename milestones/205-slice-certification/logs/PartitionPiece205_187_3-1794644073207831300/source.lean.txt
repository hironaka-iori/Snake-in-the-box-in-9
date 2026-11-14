import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d9 : a 9 ∈ [0,2])
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 25 ∈ [0,10,18,19,20,21,22,23] := by
  have b0 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b0
  have b1 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,10,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 11 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 25 ≠ 12 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,10,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 12 [0,10,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 25 ≠ 13 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,10,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 13 [0,10,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 25 ≠ 14 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,10,15,16,17,18,19,20,21,22,23] := remove (a 25) 14 [0,10,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 25 ≠ 15 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,10,16,17,18,19,20,21,22,23] := remove (a 25) 15 [0,10,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 25 ≠ 16 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,10,17,18,19,20,21,22,23] := remove (a 25) 16 [0,10,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 25 ≠ 17 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,10,18,19,20,21,22,23] := remove (a 25) 17 [0,10,17,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk13 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,10,18,19,20,21,22,23])
    (d9 : a 9 ∈ [0,2])
    (d11 : a 11 ∈ [0,5,6,9])
    (d10 : a 10 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,7,8])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 25 ∈ [0,10,18,22] ∧ a 11 ∈ [0,6] ∧ a 26 ∈ [0,2,3,5] ∧ a 15 ∈ [0,1,2,7] := by
  have b0 : a 25 ≠ 19 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 19 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,10,18,20,21,22,23] := remove (a 25) 19 [0,10,18,19,20,21,22,23] d25 b0
  have b1 : a 25 ≠ 20 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 20 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,10,18,21,22,23] := remove (a 25) 20 [0,10,18,20,21,22,23] t0 b1
  have b2 : a 25 ≠ 21 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 21 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,10,18,22,23] := remove (a 25) 21 [0,10,18,21,22,23] t1 b2
  have b3 : a 25 ≠ 23 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 23 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,10,18,22] := remove (a 25) 23 [0,10,18,22,23] t2 b3
  have b4 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 5 d10 c35 (by decide +kernel)
  have t4 : a 11 ∈ [0,6,9] := remove (a 11) 5 [0,5,6,9] d11 b4
  have b5 : a 11 ≠ 9 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 9 d10 c35 (by decide +kernel)
  have t5 : a 11 ∈ [0,6] := remove (a 11) 9 [0,6,9] t4 b5
  have b6 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b6
  have b7 : a 26 ≠ 4 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 26) 6 [0,2,3,5,6,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3,5,8,9,10,11] := remove (a 26) 7 [0,2,3,5,7,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,2,3,5,9,10,11] := remove (a 26) 8 [0,2,3,5,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 9 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,3,5,10,11] := remove (a 26) 9 [0,2,3,5,9,10,11] t10 b11
  have b12 : a 26 ≠ 10 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,5,11] := remove (a 26) 10 [0,2,3,5,10,11] t11 b12
  have b13 : a 26 ≠ 11 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,5] := remove (a 26) 11 [0,2,3,5,11] t12 b13
  have b14 : a 15 ≠ 3 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 3 t5 c38 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,2,7,8] := remove (a 15) 3 [0,1,2,3,7,8] d15 b14
  have b15 : a 15 ≠ 8 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 8 t5 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,2,7] := remove (a 15) 8 [0,1,2,7,8] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t13 (t15)))

theorem chunk14 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6])
    (d12 : a 12 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,7])
    (d13 : a 13 ∈ [0,4])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,3,7,8] ∧ a 28 ∈ [0,1,4] ∧ a 15 ∈ [0,1] ∧ a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b0
  have b1 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 27) 4 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,3,6,7,8,9,10,11] := remove (a 27) 5 [0,3,5,6,7,8,9,10,11] t2 b3
  have b4 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,3,7,8,9,10,11] := remove (a 27) 6 [0,3,6,7,8,9,10,11] t3 b4
  have b5 : a 27 ≠ 9 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,3,7,8,10,11] := remove (a 27) 9 [0,3,7,8,9,10,11] t4 b5
  have b6 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,3,7,8,11] := remove (a 27) 10 [0,3,7,8,10,11] t5 b6
  have b7 : a 27 ≠ 11 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,3,7,8] := remove (a 27) 11 [0,3,7,8,11] t6 b7
  have b8 : a 28 ≠ 2 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,3,4,5,6] := remove (a 28) 2 [0,1,2,3,4,5,6] d28 b8
  have b9 : a 28 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,4,5,6] := remove (a 28) 3 [0,1,3,4,5,6] t8 b9
  have b10 : a 28 ≠ 5 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,4,6] := remove (a 28) 5 [0,1,4,5,6] t9 b10
  have b11 : a 28 ≠ 6 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,4] := remove (a 28) 6 [0,1,4,6] t10 b11
  have b12 : a 15 ≠ 2 := exclude [0,4] (fun u v => edge r43 v u) (a 15) (a 13) 2 d13 c43 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,7] := remove (a 15) 2 [0,1,2,7] d15 b12
  have b13 : a 15 ≠ 7 := exclude [0,4] (fun u v => edge r43 v u) (a 15) (a 13) 7 d13 c43 (by decide +kernel)
  have t13 : a 15 ∈ [0,1] := remove (a 15) 7 [0,1,7] t12 b13
  have b14 : a 29 ≠ 2 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b14
  have b15 : a 29 ≠ 3 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t7 (And.intro t11 (And.intro t13 (t15)))

theorem chunk15 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,4])
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 29 ∈ [0,1,10,11,22,23] := by
  have b0 : a 29 ≠ 4 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 6 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 7 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 8 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 9 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 12 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 13 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,1,10,11,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 14 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,10,11,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,1,10,11,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 15 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,10,11,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,1,10,11,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 16 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,10,11,17,18,19,20,21,22,23] := remove (a 29) 16 [0,1,10,11,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 17 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,10,11,18,19,20,21,22,23] := remove (a 29) 17 [0,1,10,11,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 18 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,10,11,19,20,21,22,23] := remove (a 29) 18 [0,1,10,11,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 19 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,10,11,20,21,22,23] := remove (a 29) 19 [0,1,10,11,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 20 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,10,11,21,22,23] := remove (a 29) 20 [0,1,10,11,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 21 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,10,11,22,23] := remove (a 29) 21 [0,1,10,11,21,22,23] t14 b15
  exact t15

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_187
