import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,10,11,12,13,14,15,16,17,20,21,22,23])
    (d9 : a 9 ∈ [0,4])
    (d25 : a 25 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,2,7,9,10,11,18,20])
    (d10 : a 10 ∈ [0,23])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    : a 13 ∈ [0,1,2,23] ∧ a 25 ∈ [0,2] ∧ a 11 ∈ [0,2,11,18,20] := by
  have b0 : a 13 ≠ 10 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 10 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,2,11,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 10 [0,1,2,10,11,12,13,14,15,16,17,20,21,22,23] d13 b0
  have b1 : a 13 ≠ 11 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 11 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,2,12,13,14,15,16,17,20,21,22,23] := remove (a 13) 11 [0,1,2,11,12,13,14,15,16,17,20,21,22,23] t0 b1
  have b2 : a 13 ≠ 12 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 12 d9 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,2,13,14,15,16,17,20,21,22,23] := remove (a 13) 12 [0,1,2,12,13,14,15,16,17,20,21,22,23] t1 b2
  have b3 : a 13 ≠ 13 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 13 d9 c33 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,2,14,15,16,17,20,21,22,23] := remove (a 13) 13 [0,1,2,13,14,15,16,17,20,21,22,23] t2 b3
  have b4 : a 13 ≠ 14 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 14 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,2,15,16,17,20,21,22,23] := remove (a 13) 14 [0,1,2,14,15,16,17,20,21,22,23] t3 b4
  have b5 : a 13 ≠ 15 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 15 d9 c33 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,2,16,17,20,21,22,23] := remove (a 13) 15 [0,1,2,15,16,17,20,21,22,23] t4 b5
  have b6 : a 13 ≠ 16 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 16 d9 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,2,17,20,21,22,23] := remove (a 13) 16 [0,1,2,16,17,20,21,22,23] t5 b6
  have b7 : a 13 ≠ 17 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 17 d9 c33 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,2,20,21,22,23] := remove (a 13) 17 [0,1,2,17,20,21,22,23] t6 b7
  have b8 : a 13 ≠ 20 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 20 d9 c33 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,2,21,22,23] := remove (a 13) 20 [0,1,2,20,21,22,23] t7 b8
  have b9 : a 13 ≠ 21 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 21 d9 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,22,23] := remove (a 13) 21 [0,1,2,21,22,23] t8 b9
  have b10 : a 13 ≠ 22 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 22 d9 c33 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,23] := remove (a 13) 22 [0,1,2,22,23] t9 b10
  have b11 : a 25 ≠ 1 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b11
  have b12 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t11 b12
  have b13 : a 11 ≠ 7 := exclude [0,23] (fun u v => edge r35 v u) (a 11) (a 10) 7 d10 c35 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,9,10,11,18,20] := remove (a 11) 7 [0,2,7,9,10,11,18,20] d11 b13
  have b14 : a 11 ≠ 9 := exclude [0,23] (fun u v => edge r35 v u) (a 11) (a 10) 9 d10 c35 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,10,11,18,20] := remove (a 11) 9 [0,2,9,10,11,18,20] t13 b14
  have b15 : a 11 ≠ 10 := exclude [0,23] (fun u v => edge r35 v u) (a 11) (a 10) 10 d10 c35 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,11,18,20] := remove (a 11) 10 [0,2,10,11,18,20] t14 b15
  exact And.intro t10 (And.intro t12 (t15))

theorem chunk9 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,11,18,20])
    (d10 : a 10 ∈ [0,23])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 11 ∈ [0,2,18,20] ∧ a 14 ∈ [0,4] ∧ a 26 ∈ [0,4,7,8,9,10,11] := by
  have b0 : a 11 ≠ 11 := exclude [0,23] (fun u v => edge r35 v u) (a 11) (a 10) 11 d10 c35 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,18,20] := remove (a 11) 11 [0,2,11,18,20] d11 b0
  have b1 : a 14 ≠ 1 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b1
  have b2 : a 14 ≠ 2 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 2 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 3 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 5 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,4,6,7,8,9,10,11] := remove (a 14) 5 [0,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 6 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,7,8,9,10,11] := remove (a 14) 6 [0,4,6,7,8,9,10,11] t4 b5
  have b6 : a 14 ≠ 7 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,4,8,9,10,11] := remove (a 14) 7 [0,4,7,8,9,10,11] t5 b6
  have b7 : a 14 ≠ 8 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,4,9,10,11] := remove (a 14) 8 [0,4,8,9,10,11] t6 b7
  have b8 : a 14 ≠ 9 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 9 d10 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,4,10,11] := remove (a 14) 9 [0,4,9,10,11] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,4,11] := remove (a 14) 10 [0,4,10,11] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0,23] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,4] := remove (a 14) 11 [0,4,11] t9 b10
  have b11 : a 26 ≠ 1 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b11
  have b12 : a 26 ≠ 2 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 26 ≠ 3 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 26 ≠ 5 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,6,7,8,9,10,11] := remove (a 26) 5 [0,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 26 ≠ 6 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,7,8,9,10,11] := remove (a 26) 6 [0,4,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t10 (t15))

theorem chunk10 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,7,8,9,10,11])
    (d10 : a 10 ∈ [0,23])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,2,18,20])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,4,9,10] ∧ a 15 ∈ [0,2,5,6,9,10] ∧ a 27 ∈ [0,1,9,10,11] := by
  have b0 : a 26 ≠ 7 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,4,8,9,10,11] := remove (a 26) 7 [0,4,7,8,9,10,11] d26 b0
  have b1 : a 26 ≠ 8 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,4,9,10,11] := remove (a 26) 8 [0,4,8,9,10,11] t0 b1
  have b2 : a 26 ≠ 11 := exclude [0,23] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,4,9,10] := remove (a 26) 11 [0,4,9,10,11] t1 b2
  have b3 : a 15 ≠ 1 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b3
  have b4 : a 15 ≠ 3 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 15) 3 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 15 ≠ 4 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 15) 4 [0,2,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 15 ≠ 7 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,5,6,8,9,10,11] := remove (a 15) 7 [0,2,5,6,7,8,9,10,11] t5 b6
  have b7 : a 15 ≠ 8 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 8 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,2,5,6,9,10,11] := remove (a 15) 8 [0,2,5,6,8,9,10,11] t6 b7
  have b8 : a 15 ≠ 11 := exclude [0,2,18,20] (fun u v => edge r38 v u) (a 15) (a 11) 11 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,2,5,6,9,10] := remove (a 15) 11 [0,2,5,6,9,10,11] t7 b8
  have b9 : a 27 ≠ 2 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b9
  have b10 : a 27 ≠ 3 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 4 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 5 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 6 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 7 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 8 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t8 (t15))

theorem chunk11 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,9,10,11])
    (d11 : a 11 ∈ [0,2,18,20])
    (d12 : a 12 ∈ [0,2,3,9])
    (d13 : a 13 ∈ [0,1,2,23])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (d15 : a 15 ∈ [0,2,5,6,9,10])
    (d14 : a 14 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 27 ∈ [0,1,9,10] ∧ a 12 ∈ [0,9] ∧ a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,14,15,16,18,19] ∧ a 29 ∈ [0,1,4,5] ∧ a 15 ∈ [0,2] ∧ a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 27 ≠ 11 := exclude [0,2,18,20] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,9,10] := remove (a 27) 11 [0,1,9,10,11] d27 b0
  have b1 : a 12 ≠ 2 := exclude [0,1,2,23] (edge r40) (a 12) (a 13) 2 d13 c40 (by decide +kernel)
  have t1 : a 12 ∈ [0,3,9] := remove (a 12) 2 [0,2,3,9] d12 b1
  have b2 : a 12 ≠ 3 := exclude [0,1,2,23] (edge r40) (a 12) (a 13) 3 d13 c40 (by decide +kernel)
  have t2 : a 12 ∈ [0,9] := remove (a 12) 3 [0,3,9] t1 b2
  have b3 : a 28 ≠ 3 := exclude [0,9] (fun u v => edge r42 v u) (a 28) (a 12) 3 t2 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 28) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d28 b3
  have b4 : a 28 ≠ 12 := exclude [0,9] (fun u v => edge r42 v u) (a 28) (a 12) 12 t2 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19] := remove (a 28) 12 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 28 ≠ 13 := exclude [0,9] (fun u v => edge r42 v u) (a 28) (a 12) 13 t2 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,14,15,16,17,18,19] := remove (a 28) 13 [0,1,2,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19] t4 b5
  have b6 : a 28 ≠ 17 := exclude [0,9] (fun u v => edge r42 v u) (a 28) (a 12) 17 t2 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,2,4,5,6,7,8,9,10,11,14,15,16,18,19] := remove (a 28) 17 [0,1,2,4,5,6,7,8,9,10,11,14,15,16,17,18,19] t5 b6
  have b7 : a 29 ≠ 2 := exclude [0,1,2,23] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,3,4,5,6,7] := remove (a 29) 2 [0,1,2,3,4,5,6,7] d29 b7
  have b8 : a 29 ≠ 3 := exclude [0,1,2,23] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,4,5,6,7] := remove (a 29) 3 [0,1,3,4,5,6,7] t7 b8
  have b9 : a 29 ≠ 6 := exclude [0,1,2,23] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,4,5,7] := remove (a 29) 6 [0,1,4,5,6,7] t8 b9
  have b10 : a 29 ≠ 7 := exclude [0,1,2,23] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,4,5] := remove (a 29) 7 [0,1,4,5,7] t9 b10
  have b11 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r45 v u) (a 15) (a 14) 5 d14 c45 (by decide +kernel)
  have t11 : a 15 ∈ [0,2,6,9,10] := remove (a 15) 5 [0,2,5,6,9,10] d15 b11
  have b12 : a 15 ≠ 6 := exclude [0,4] (fun u v => edge r45 v u) (a 15) (a 14) 6 d14 c45 (by decide +kernel)
  have t12 : a 15 ∈ [0,2,9,10] := remove (a 15) 6 [0,2,6,9,10] t11 b12
  have b13 : a 15 ≠ 9 := exclude [0,4] (fun u v => edge r45 v u) (a 15) (a 14) 9 d14 c45 (by decide +kernel)
  have t13 : a 15 ∈ [0,2,10] := remove (a 15) 9 [0,2,9,10] t12 b13
  have b14 : a 15 ≠ 10 := exclude [0,4] (fun u v => edge r45 v u) (a 15) (a 14) 10 d14 c45 (by decide +kernel)
  have t14 : a 15 ∈ [0,2] := remove (a 15) 10 [0,2,10] t13 b14
  have b15 : a 30 ≠ 1 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b15
  exact And.intro t0 (And.intro t2 (And.intro t6 (And.intro t10 (And.intro t14 (t15)))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_185
