import PartitionData205_188
namespace PartitionCover205_188
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,5])
    (d9 : a 9 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d10 : a 10 ∈ [0,1,2,4,6,7,8,10])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,4,5,6,7,10,11])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 13 ∈ [0,1] ∧ a 25 ∈ [0,1,2,3] ∧ a 10 ∈ [0,6] ∧ a 14 ∈ [0,4,5,6,7,10,11] := by
  have b0 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] d13 b0
  have b1 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 25) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b1
  have b2 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 25) 5 [0,1,2,3,5,6,7,8,9,10,11] t1 b2
  have b3 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 25) 6 [0,1,2,3,6,7,8,9,10,11] t2 b3
  have b4 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,2,3,8,9,10,11] := remove (a 25) 7 [0,1,2,3,7,8,9,10,11] t3 b4
  have b5 : a 25 ≠ 8 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,9,10,11] := remove (a 25) 8 [0,1,2,3,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,10,11] := remove (a 25) 9 [0,1,2,3,9,10,11] t5 b6
  have b7 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3,11] := remove (a 25) 10 [0,1,2,3,10,11] t6 b7
  have b8 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,2,3] := remove (a 25) 11 [0,1,2,3,11] t7 b8
  have b9 : a 10 ≠ 1 := exclude [0,6] (edge r35) (a 10) (a 11) 1 d11 c35 (by decide +kernel)
  have t9 : a 10 ∈ [0,2,4,6,7,8,10] := remove (a 10) 1 [0,1,2,4,6,7,8,10] d10 b9
  have b10 : a 10 ≠ 4 := exclude [0,6] (edge r35) (a 10) (a 11) 4 d11 c35 (by decide +kernel)
  have t10 : a 10 ∈ [0,2,6,7,8,10] := remove (a 10) 4 [0,2,4,6,7,8,10] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,6] (edge r35) (a 10) (a 11) 7 d11 c35 (by decide +kernel)
  have t11 : a 10 ∈ [0,2,6,8,10] := remove (a 10) 7 [0,2,6,7,8,10] t10 b11
  have b12 : a 10 ≠ 10 := exclude [0,6] (edge r35) (a 10) (a 11) 10 d11 c35 (by decide +kernel)
  have t12 : a 10 ∈ [0,2,6,8] := remove (a 10) 10 [0,2,6,8,10] t11 b12
  have b13 : a 10 ≠ 2 := exclude [0,1,4,5,6,7,10,11] (edge r36) (a 10) (a 14) 2 d14 c36 (by decide +kernel)
  have t13 : a 10 ∈ [0,6,8] := remove (a 10) 2 [0,2,6,8] t12 b13
  have b14 : a 10 ≠ 8 := exclude [0,1,4,5,6,7,10,11] (edge r36) (a 10) (a 14) 8 d14 c36 (by decide +kernel)
  have t14 : a 10 ∈ [0,6] := remove (a 10) 8 [0,6,8] t13 b14
  have b15 : a 14 ≠ 1 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 1 t14 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,5,6,7,10,11] := remove (a 14) 1 [0,1,4,5,6,7,10,11] d14 b15
  exact And.intro t0 (And.intro t8 (And.intro t14 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,5,6,7,10,11])
    (d10 : a 10 ∈ [0,6])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 14 ∈ [0,6] ∧ a 26 ∈ [0,2,9,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 4 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,5,6,7,10,11] := remove (a 14) 4 [0,4,5,6,7,10,11] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,6,7,10,11] := remove (a 14) 5 [0,5,6,7,10,11] t0 b1
  have b2 : a 14 ≠ 7 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,6,10,11] := remove (a 14) 7 [0,6,7,10,11] t1 b2
  have b3 : a 14 ≠ 10 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,6,11] := remove (a 14) 10 [0,6,10,11] t2 b3
  have b4 : a 14 ≠ 11 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,6] := remove (a 14) 11 [0,6,11] t3 b4
  have b5 : a 26 ≠ 1 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b5
  have b6 : a 26 ≠ 3 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 4 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 5 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 6 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 7 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 8 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 10 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,9,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 10 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 11 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,9,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,2,9,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 12 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 12 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,2,9,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 12 [0,2,9,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 13 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 13 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,9,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 13 [0,2,9,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t4 (t15)

theorem chunk10 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,9,14,15,16,17,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,6])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,2,9,21] ∧ a 15 ∈ [0,1,3,4] ∧ a 27 ∈ [0,2,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 26 ≠ 14 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 14 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,9,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,2,9,14,15,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 15 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 15 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,2,9,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,2,9,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 16 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 16 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,2,9,17,18,19,20,21,22,23] := remove (a 26) 16 [0,2,9,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 17 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 17 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,2,9,18,19,20,21,22,23] := remove (a 26) 17 [0,2,9,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 18 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 18 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,2,9,19,20,21,22,23] := remove (a 26) 18 [0,2,9,18,19,20,21,22,23] t3 b4
  have b5 : a 26 ≠ 19 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 19 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,2,9,20,21,22,23] := remove (a 26) 19 [0,2,9,19,20,21,22,23] t4 b5
  have b6 : a 26 ≠ 20 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 20 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,9,21,22,23] := remove (a 26) 20 [0,2,9,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 22 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 22 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,9,21,23] := remove (a 26) 22 [0,2,9,21,22,23] t6 b7
  have b8 : a 26 ≠ 23 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 23 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,9,21] := remove (a 26) 23 [0,2,9,21,23] t7 b8
  have b9 : a 15 ≠ 2 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b9
  have b10 : a 15 ≠ 5 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,3,4] := remove (a 15) 5 [0,1,3,4,5] t9 b10
  have b11 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d27 b11
  have b12 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,2,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 6 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 27 ≠ 7 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,2,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 7 [0,2,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 8 [0,2,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (And.intro t10 (t15))

theorem chunk11 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d11 : a 11 ∈ [0,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,4])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,2,4,5] ∧ a 28 ∈ [0,2,3,4,5,6,7,8] := by
  have b0 : a 27 ≠ 9 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 9 [0,2,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d27 b0
  have b1 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 10 [0,2,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 27 ≠ 11 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,2,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 11 [0,2,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 27 ≠ 12 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,2,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 12 [0,2,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 27 ≠ 13 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,2,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 13 [0,2,4,5,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 27 ≠ 14 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,2,4,5,15,16,17,18,19,20,21,22,23] := remove (a 27) 14 [0,2,4,5,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 27 ≠ 15 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,2,4,5,16,17,18,19,20,21,22,23] := remove (a 27) 15 [0,2,4,5,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 27 ≠ 16 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,2,4,5,17,18,19,20,21,22,23] := remove (a 27) 16 [0,2,4,5,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 27 ≠ 17 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,2,4,5,18,19,20,21,22,23] := remove (a 27) 17 [0,2,4,5,17,18,19,20,21,22,23] t7 b8
  have b9 : a 27 ≠ 18 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 18 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,2,4,5,19,20,21,22,23] := remove (a 27) 18 [0,2,4,5,18,19,20,21,22,23] t8 b9
  have b10 : a 27 ≠ 19 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 19 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,2,4,5,20,21,22,23] := remove (a 27) 19 [0,2,4,5,19,20,21,22,23] t9 b10
  have b11 : a 27 ≠ 20 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 20 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,2,4,5,21,22,23] := remove (a 27) 20 [0,2,4,5,20,21,22,23] t10 b11
  have b12 : a 27 ≠ 21 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 21 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,2,4,5,22,23] := remove (a 27) 21 [0,2,4,5,21,22,23] t11 b12
  have b13 : a 27 ≠ 22 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 22 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,2,4,5,23] := remove (a 27) 22 [0,2,4,5,22,23] t12 b13
  have b14 : a 27 ≠ 23 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 23 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,2,4,5] := remove (a 27) 23 [0,2,4,5,23] t13 b14
  have b15 : a 28 ≠ 1 := exclude [0,4] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,3,4,5,6,7,8] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8] d28 b15
  exact And.intro t14 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_188
