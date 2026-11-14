import PartitionData205_183
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6])
    (d13 : a 13 ∈ [0,1,2,3,12,13,14,15])
    (d9 : a 9 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (c28 : edge r28 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 23)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    : a 8 ∈ [0,1] ∧ a 23 ∈ [0,1,2] ∧ a 13 ∈ [0,1,3,12,13,15] ∧ a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] ∧ a 25 ∈ [0,1,2,3,4,5,8] := by
  have b0 : a 8 ≠ 2 := exclude [0,1] (edge r28) (a 8) (a 10) 2 d10 c28 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b0
  have b1 : a 8 ≠ 3 := exclude [0,1] (edge r28) (a 8) (a 10) 3 d10 c28 (by decide +kernel)
  have t1 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t0 b1
  have b2 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r30 v u) (a 23) (a 8) 3 t1 c30 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,2,4,5,6] := remove (a 23) 3 [0,1,2,3,4,5,6] d23 b2
  have b3 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r30 v u) (a 23) (a 8) 4 t1 c30 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,5,6] := remove (a 23) 4 [0,1,2,4,5,6] t2 b3
  have b4 : a 23 ≠ 5 := exclude [0,1] (fun u v => edge r30 v u) (a 23) (a 8) 5 t1 c30 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,6] := remove (a 23) 5 [0,1,2,5,6] t3 b4
  have b5 : a 23 ≠ 6 := exclude [0,1] (fun u v => edge r30 v u) (a 23) (a 8) 6 t1 c30 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2] := remove (a 23) 6 [0,1,2,6] t4 b5
  have b6 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r32 v u) (a 13) (a 9) 2 d9 c32 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,3,12,13,14,15] := remove (a 13) 2 [0,1,2,3,12,13,14,15] d13 b6
  have b7 : a 13 ≠ 14 := exclude [0,1] (fun u v => edge r32 v u) (a 13) (a 9) 14 d9 c32 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,3,12,13,15] := remove (a 13) 14 [0,1,3,12,13,14,15] t6 b7
  have b8 : a 24 ≠ 12 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 12 d9 c33 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] := remove (a 24) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b8
  have b9 : a 24 ≠ 13 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 13 d9 c33 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] := remove (a 24) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 14 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 14 d9 c33 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] := remove (a 24) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 15 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 15 d9 c33 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := remove (a 24) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] t10 b11
  have b12 : a 24 ≠ 16 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 16 d9 c33 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17] := remove (a 24) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17] t11 b12
  have b13 : a 24 ≠ 17 := exclude [0,1] (fun u v => edge r33 v u) (a 24) (a 9) 17 d9 c33 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17] t12 b13
  have b14 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r36 v u) (a 25) (a 10) 6 d10 c36 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,4,5,7,8] := remove (a 25) 6 [0,1,2,3,4,5,6,7,8] d25 b14
  have b15 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r36 v u) (a 25) (a 10) 7 d10 c36 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,2,3,4,5,8] := remove (a 25) 7 [0,1,2,3,4,5,7,8] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t7 (And.intro t13 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,5,8])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,3,4,6,9])
    (d13 : a 13 ∈ [0,1,3,12,13,15])
    (d14 : a 14 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c38 : edge r38 (a 12) (a 13)=true)
    (c39 : edge r39 (a 12) (a 14)=true)
    (c40 : edge r40 (a 12) (a 27)=true)
    : a 25 ∈ [0,1,2,3,4,5] ∧ a 26 ∈ [0,1,2,3] ∧ a 12 ∈ [0,1] ∧ a 27 ∈ [0,2,5,6,7,8,9,10,11] := by
  have b0 : a 25 ≠ 8 := exclude [0,1] (fun u v => edge r36 v u) (a 25) (a 10) 8 d10 c36 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,4,5] := remove (a 25) 8 [0,1,2,3,4,5,8] d25 b0
  have b1 : a 26 ≠ 4 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 4 d11 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b1
  have b2 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 5 d11 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 26) 5 [0,1,2,3,5,6,7,8,9,10,11] t1 b2
  have b3 : a 26 ≠ 6 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 6 d11 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 26) 6 [0,1,2,3,6,7,8,9,10,11] t2 b3
  have b4 : a 26 ≠ 7 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 7 d11 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,2,3,8,9,10,11] := remove (a 26) 7 [0,1,2,3,7,8,9,10,11] t3 b4
  have b5 : a 26 ≠ 8 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 8 d11 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,2,3,9,10,11] := remove (a 26) 8 [0,1,2,3,8,9,10,11] t4 b5
  have b6 : a 26 ≠ 9 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 9 d11 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,2,3,10,11] := remove (a 26) 9 [0,1,2,3,9,10,11] t5 b6
  have b7 : a 26 ≠ 10 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 10 d11 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,2,3,11] := remove (a 26) 10 [0,1,2,3,10,11] t6 b7
  have b8 : a 26 ≠ 11 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 11) 11 d11 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,3] := remove (a 26) 11 [0,1,2,3,11] t7 b8
  have b9 : a 12 ≠ 6 := exclude [0,1,3,12,13,15] (edge r38) (a 12) (a 13) 6 d13 c38 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,3,4,9] := remove (a 12) 6 [0,1,3,4,6,9] d12 b9
  have b10 : a 12 ≠ 9 := exclude [0,1,3,12,13,15] (edge r38) (a 12) (a 13) 9 d13 c38 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,3,4] := remove (a 12) 9 [0,1,3,4,9] t9 b10
  have b11 : a 12 ≠ 3 := exclude [0,2] (edge r39) (a 12) (a 14) 3 d14 c39 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,4] := remove (a 12) 3 [0,1,3,4] t10 b11
  have b12 : a 12 ≠ 4 := exclude [0,2] (edge r39) (a 12) (a 14) 4 d14 c39 (by decide +kernel)
  have t12 : a 12 ∈ [0,1] := remove (a 12) 4 [0,1,4] t11 b12
  have b13 : a 27 ≠ 1 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 1 t12 c40 (by decide +kernel)
  have t13 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b13
  have b14 : a 27 ≠ 3 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 3 t12 c40 (by decide +kernel)
  have t14 : a 27 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 4 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 4 t12 c40 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 27) 4 [0,2,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t8 (And.intro t12 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0,2])
    (d16 : a 16 ∈ [0,2,6,8,12,14])
    (d15 : a 15 ∈ [0,3])
    (c40 : edge r40 (a 12) (a 27)=true)
    (c42 : edge r42 (a 14) (a 29)=true)
    (c43 : edge r43 (a 15) (a 16)=true)
    : a 27 ∈ [0,2,6,8,10,11] ∧ a 29 ∈ [0,1,6,7,12,13] ∧ a 16 ∈ [0,6,8,12,14] := by
  have b0 : a 27 ≠ 5 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 5 d12 c40 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,6,7,8,9,10,11] := remove (a 27) 5 [0,2,5,6,7,8,9,10,11] d27 b0
  have b1 : a 27 ≠ 7 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 7 d12 c40 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,6,8,9,10,11] := remove (a 27) 7 [0,2,6,7,8,9,10,11] t0 b1
  have b2 : a 27 ≠ 9 := exclude [0,1] (fun u v => edge r40 v u) (a 27) (a 12) 9 d12 c40 (by decide +kernel)
  have t2 : a 27 ∈ [0,2,6,8,10,11] := remove (a 27) 9 [0,2,6,8,9,10,11] t1 b2
  have b3 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 2 d14 c42 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d29 b3
  have b4 : a 29 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 3 d14 c42 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 29 ≠ 4 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 4 d14 c42 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 29 ≠ 5 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 5 d14 c42 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 29 ≠ 8 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 8 d14 c42 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 29) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 29 ≠ 9 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 9 d14 c42 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 29) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 29 ≠ 10 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 10 d14 c42 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 29) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 29 ≠ 11 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 11 d14 c42 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 29) 11 [0,1,6,7,11,12,13,14,15,16,17] t9 b10
  have b11 : a 29 ≠ 14 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 14 d14 c42 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,6,7,12,13,15,16,17] := remove (a 29) 14 [0,1,6,7,12,13,14,15,16,17] t10 b11
  have b12 : a 29 ≠ 15 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 15 d14 c42 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,6,7,12,13,16,17] := remove (a 29) 15 [0,1,6,7,12,13,15,16,17] t11 b12
  have b13 : a 29 ≠ 16 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 16 d14 c42 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,6,7,12,13,17] := remove (a 29) 16 [0,1,6,7,12,13,16,17] t12 b13
  have b14 : a 29 ≠ 17 := exclude [0,2] (fun u v => edge r42 v u) (a 29) (a 14) 17 d14 c42 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,6,7,12,13] := remove (a 29) 17 [0,1,6,7,12,13,17] t13 b14
  have b15 : a 16 ≠ 2 := exclude [0,3] (fun u v => edge r43 v u) (a 16) (a 15) 2 d15 c43 (by decide +kernel)
  have t15 : a 16 ∈ [0,6,8,12,14] := remove (a 16) 2 [0,2,6,8,12,14] d16 b15
  exact And.intro t2 (And.intro t14 (t15))

theorem chunk11 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,6,8,12,14])
    (d15 : a 15 ∈ [0,3])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d23 : a 23 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c43 : edge r43 (a 15) (a 16)=true)
    (c45 : edge r45 (a 15) (a 19)=true)
    (c46 : edge r46 (a 15) (a 23)=true)
    (c48 : edge r48 (a 16) (a 20)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    : a 16 ∈ [0,6] ∧ a 19 ∈ [0,1,6,7] ∧ a 23 ∈ [0] ∧ a 20 ∈ [0] ∧ a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 16 ≠ 8 := exclude [0,3] (fun u v => edge r43 v u) (a 16) (a 15) 8 d15 c43 (by decide +kernel)
  have t0 : a 16 ∈ [0,6,12,14] := remove (a 16) 8 [0,6,8,12,14] d16 b0
  have b1 : a 16 ≠ 12 := exclude [0,3] (fun u v => edge r43 v u) (a 16) (a 15) 12 d15 c43 (by decide +kernel)
  have t1 : a 16 ∈ [0,6,14] := remove (a 16) 12 [0,6,12,14] t0 b1
  have b2 : a 16 ≠ 14 := exclude [0,3] (fun u v => edge r43 v u) (a 16) (a 15) 14 d15 c43 (by decide +kernel)
  have t2 : a 16 ∈ [0,6] := remove (a 16) 14 [0,6,14] t1 b2
  have b3 : a 19 ≠ 2 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 2 d15 c45 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b3
  have b4 : a 19 ≠ 3 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 3 d15 c45 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 19 ≠ 4 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 4 d15 c45 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 19) 4 [0,1,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 19 ≠ 5 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 5 d15 c45 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,6,7,8,9,10,11] := remove (a 19) 5 [0,1,5,6,7,8,9,10,11] t5 b6
  have b7 : a 19 ≠ 8 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 8 d15 c45 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,6,7,9,10,11] := remove (a 19) 8 [0,1,6,7,8,9,10,11] t6 b7
  have b8 : a 19 ≠ 9 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 9 d15 c45 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,6,7,10,11] := remove (a 19) 9 [0,1,6,7,9,10,11] t7 b8
  have b9 : a 19 ≠ 10 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 10 d15 c45 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,6,7,11] := remove (a 19) 10 [0,1,6,7,10,11] t8 b9
  have b10 : a 19 ≠ 11 := exclude [0,3] (fun u v => edge r45 v u) (a 19) (a 15) 11 d15 c45 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,6,7] := remove (a 19) 11 [0,1,6,7,11] t9 b10
  have b11 : a 23 ≠ 1 := exclude [0,3] (fun u v => edge r46 v u) (a 23) (a 15) 1 d15 c46 (by decide +kernel)
  have t11 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] d23 b11
  have b12 : a 23 ≠ 2 := exclude [0,3] (fun u v => edge r46 v u) (a 23) (a 15) 2 d15 c46 (by decide +kernel)
  have t12 : a 23 ∈ [0] := remove (a 23) 2 [0,2] t11 b12
  have b13 : a 20 ≠ 1 := exclude [0,6] (fun u v => edge r48 v u) (a 20) (a 16) 1 t2 c48 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b13
  have b14 : a 24 ≠ 1 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 1 t2 c49 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b14
  have b15 : a 24 ≠ 2 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 2 t2 c49 (by decide +kernel)
  have t15 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_183
