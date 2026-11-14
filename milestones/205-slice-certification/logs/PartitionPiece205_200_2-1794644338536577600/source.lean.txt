import PartitionData205_200
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,4])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,1,2,3,4])
    (d11 : a 11 ∈ [0,12])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 13 ∈ [0,1] ∧ a 25 ∈ [0,1] ∧ a 10 ∈ [0,1,2] ∧ a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 13 ≠ 12 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 12 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,13,14,15,16,17] := remove (a 13) 12 [0,1,12,13,14,15,16,17] d13 b0
  have b1 : a 13 ≠ 13 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 13 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,14,15,16,17] := remove (a 13) 13 [0,1,13,14,15,16,17] t0 b1
  have b2 : a 13 ≠ 14 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 14 d9 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,15,16,17] := remove (a 13) 14 [0,1,14,15,16,17] t1 b2
  have b3 : a 13 ≠ 15 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 15 d9 c33 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,16,17] := remove (a 13) 15 [0,1,15,16,17] t2 b3
  have b4 : a 13 ≠ 16 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 16 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,17] := remove (a 13) 16 [0,1,16,17] t3 b4
  have b5 : a 13 ≠ 17 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 17 d9 c33 (by decide +kernel)
  have t5 : a 13 ∈ [0,1] := remove (a 13) 17 [0,1,17] t4 b5
  have b6 : a 25 ≠ 2 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,3,4,5,6,7,8] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8] d25 b6
  have b7 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,4,5,6,7,8] := remove (a 25) 3 [0,1,3,4,5,6,7,8] t6 b7
  have b8 : a 25 ≠ 4 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,5,6,7,8] := remove (a 25) 4 [0,1,4,5,6,7,8] t7 b8
  have b9 : a 25 ≠ 5 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,6,7,8] := remove (a 25) 5 [0,1,5,6,7,8] t8 b9
  have b10 : a 25 ≠ 6 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,7,8] := remove (a 25) 6 [0,1,6,7,8] t9 b10
  have b11 : a 25 ≠ 7 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,8] := remove (a 25) 7 [0,1,7,8] t10 b11
  have b12 : a 25 ≠ 8 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1] := remove (a 25) 8 [0,1,8] t11 b12
  have b13 : a 10 ≠ 3 := exclude [0,12] (edge r35) (a 10) (a 11) 3 d11 c35 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,2,4] := remove (a 10) 3 [0,1,2,3,4] d10 b13
  have b14 : a 10 ≠ 4 := exclude [0,12] (edge r35) (a 10) (a 11) 4 d11 c35 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,2] := remove (a 10) 4 [0,1,2,4] t13 b14
  have b15 : a 26 ≠ 1 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 1 t14 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b15
  exact And.intro t5 (And.intro t12 (And.intro t14 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,1,2,6,7,8])
    (d11 : a 11 ∈ [0,12])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] ∧ a 15 ∈ [0,6] ∧ a 27 ∈ [0,1,9,10,11] := by
  have b0 : a 26 ≠ 3 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 5 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 7 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 18 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 18 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23] := remove (a 26) 18 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 22 := exclude [0,1,2] (fun u v => edge r37 v u) (a 26) (a 10) 22 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,23] := remove (a 26) 22 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23] t3 b4
  have b5 : a 15 ≠ 1 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,2,6,7,8] := remove (a 15) 1 [0,1,2,6,7,8] d15 b5
  have b6 : a 15 ≠ 2 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,6,7,8] := remove (a 15) 2 [0,2,6,7,8] t5 b6
  have b7 : a 15 ≠ 7 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,6,8] := remove (a 15) 7 [0,6,7,8] t6 b7
  have b8 : a 15 ≠ 8 := exclude [0,12] (fun u v => edge r38 v u) (a 15) (a 11) 8 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,6] := remove (a 15) 8 [0,6,8] t7 b8
  have b9 : a 27 ≠ 2 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b9
  have b10 : a 27 ≠ 3 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 4 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 5 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 6 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 7 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 8 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t14 b15
  exact And.intro t4 (And.intro t8 (t15))

theorem chunk10 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,9,10,11])
    (d11 : a 11 ∈ [0,12])
    (d12 : a 12 ∈ [0,1,4,19])
    (d13 : a 13 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,12,13,14])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,1,9,11] ∧ a 12 ∈ [0,1] ∧ a 14 ∈ [0,1,12,13] ∧ a 28 ∈ [0,2,3,5] ∧ a 29 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 27 ≠ 10 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,9,11] := remove (a 27) 10 [0,1,9,10,11] d27 b0
  have b1 : a 12 ≠ 4 := exclude [0,1] (edge r40) (a 12) (a 13) 4 d13 c40 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,19] := remove (a 12) 4 [0,1,4,19] d12 b1
  have b2 : a 12 ≠ 19 := exclude [0,1] (edge r40) (a 12) (a 13) 19 d13 c40 (by decide +kernel)
  have t2 : a 12 ∈ [0,1] := remove (a 12) 19 [0,1,19] t1 b2
  have b3 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r41 v u) (a 14) (a 12) 2 t2 c41 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,12,13,14] := remove (a 14) 2 [0,1,2,12,13,14] d14 b3
  have b4 : a 14 ≠ 14 := exclude [0,1] (fun u v => edge r41 v u) (a 14) (a 12) 14 t2 c41 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,12,13] := remove (a 14) 14 [0,1,12,13,14] t3 b4
  have b5 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 1 t2 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b5
  have b6 : a 28 ≠ 4 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 4 t2 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 28) 4 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 28 ≠ 6 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 6 t2 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 28) 6 [0,2,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 28 ≠ 7 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 7 t2 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,3,5,8,9,10,11] := remove (a 28) 7 [0,2,3,5,7,8,9,10,11] t7 b8
  have b9 : a 28 ≠ 8 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 8 t2 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,3,5,9,10,11] := remove (a 28) 8 [0,2,3,5,8,9,10,11] t8 b9
  have b10 : a 28 ≠ 9 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 9 t2 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,3,5,10,11] := remove (a 28) 9 [0,2,3,5,9,10,11] t9 b10
  have b11 : a 28 ≠ 10 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 10 t2 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,3,5,11] := remove (a 28) 10 [0,2,3,5,10,11] t10 b11
  have b12 : a 28 ≠ 11 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 11 t2 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,3,5] := remove (a 28) 11 [0,2,3,5,11] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t12 (t15))))

theorem chunk11 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,1,12,13])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,2] ∧ a 30 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] d29 b0
  have b1 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,2,8,9,10,11,12,13,14,15,16,17] := remove (a 29) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 29 ≠ 8 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,2,9,10,11,12,13,14,15,16,17] := remove (a 29) 8 [0,2,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,10,11,12,13,14,15,16,17] := remove (a 29) 9 [0,2,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,11,12,13,14,15,16,17] := remove (a 29) 10 [0,2,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,12,13,14,15,16,17] := remove (a 29) 11 [0,2,11,12,13,14,15,16,17] t5 b6
  have b7 : a 29 ≠ 12 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,2,13,14,15,16,17] := remove (a 29) 12 [0,2,12,13,14,15,16,17] t6 b7
  have b8 : a 29 ≠ 13 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,2,14,15,16,17] := remove (a 29) 13 [0,2,13,14,15,16,17] t7 b8
  have b9 : a 29 ≠ 14 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,2,15,16,17] := remove (a 29) 14 [0,2,14,15,16,17] t8 b9
  have b10 : a 29 ≠ 15 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,2,16,17] := remove (a 29) 15 [0,2,15,16,17] t9 b10
  have b11 : a 29 ≠ 16 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,2,17] := remove (a 29) 16 [0,2,16,17] t10 b11
  have b12 : a 29 ≠ 17 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,2] := remove (a 29) 17 [0,2,17] t11 b12
  have b13 : a 30 ≠ 1 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b13
  have b14 : a 30 ≠ 3 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 4 := exclude [0,1,12,13] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_200
